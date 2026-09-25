"""The JSON API (app/API.md, DESIGN.md §16.3) without HTTP: `handle(method,
path, query, body)` returns (status, response dict). server.py is the only
caller besides the tests.

Untrusted. Every verdict string is kernel.report's; everything else here
is rendering. No ProofState, Handle or Term leaves this module: responses
are built from str, int, bool, None, lists and dicts only.
"""

import glob
import json
import os
import secrets

import session as S
from session import K, KERNEL, Refusal, loader
from terms import Refused, parse_goal, parse_term, show

PROBLEMS = os.path.join(KERNEL, "problems")


class ApiError(Exception):
    def __init__(self, status, code, message):
        super().__init__(f"{code}: {message}")
        self.status, self.code, self.message = status, code, message


def _bad(message):
    return ApiError(400, "bad-request", message)


def _text(x):
    """show(x), never raising: a number too long for str() is named."""
    try:
        return show(x)
    except ValueError:
        return f"(a {type(x).__name__} too large to print)"


# ---------------------------------------------------------------- rendering

def _obligation(ob, before):
    method, cites = ob.tag
    return {"key": _text(ob.key), "sources": sorted(ob.sources),
            "status": ob.status, "method": method, "cites": list(cites),
            "reason": ob.reason, "new": ob.key not in before}


def _summary(n):
    a = n.args
    main = {"rewrite": a.get("entry"), "fact": a.get("entry"),
            "ftc": a.get("F") and f"F := {a['F']}",
            "close": a.get("value") and f"?A := {a['value']}",
            "int_subst": a.get("sub") and
            f"{a.get('var', '')} := {a['sub']}".strip()}.get(n.move)
    return f"{n.move} {main}" if main else n.move


def render(sess, n):
    st = n.state
    before = (set() if n.parent is None else
              {ob.key for ob in sess.nodes[n.parent].state.obligations()})
    return {"session": sess.id, "node": n.id, "parent": n.parent,
            "move": n.move, "report": K.report(st),
            "goal": None if st.goal is None else _text(st.goal),
            "theorem": None if st.theorem is None else _text(st.theorem),
            "obligations": [_obligation(ob, before)
                            for ob in st.obligations()],
            "occurrences": st.last.occurrences,
            "handles": sorted(n.handles), "retracted": n.retracted}


def refusal(r):
    return {"refusal": {"code": r.code, "message": r.message,
                        "residual": None if r.residual is None
                        else _text(r.residual)}}


# ---------------------------------------------------------------- state

SESSIONS = {}


def _problem_files():
    """id -> (Problem, title, statement) for every file loader.load
    accepts. The reference proof stays in the Problem, never sent (PF1)."""
    out = {}
    for path in sorted(glob.glob(os.path.join(PROBLEMS, "*", "*.json"))):
        try:
            p = loader.load(path)
        except ValueError:
            continue
        with open(path, encoding="utf-8") as f:
            raw = json.load(f)
        out[p.id] = (p, raw["title"], raw["statement"])
    return out


def _field(body, name, kind, optional=False):
    if name not in body:
        if optional:
            return None
        raise _bad(f"missing field {name!r}")
    v = body[name]
    if not isinstance(v, kind) or isinstance(v, bool) and kind is not bool:
        raise _bad(f"{name!r} must be a {kind.__name__}")
    return v


def _sig(body):
    fns = _field(body, "functions", dict, optional=True) or {}
    if not all(isinstance(k, str) and type(v) is int and v > 0
               for k, v in fns.items()):
        raise _bad("functions maps names to positive arities")
    return fns


def _session(args):
    sid = _field(args, "session", str)
    if sid not in SESSIONS:
        raise ApiError(400, "unknown-session", f"no session {sid!r}")
    return SESSIONS[sid]


def _node(sess, args):
    nid = _field(args, "node", str)
    if nid not in sess.nodes:
        raise ApiError(400, "unknown-node", f"no node {nid!r}")
    return sess.nodes[nid]


# ---------------------------------------------------------------- routes

def problems(_):
    return {"problems": [{"id": p.id, "title": title, "statement": st}
                         for p, title, st in _problem_files().values()]}


def new_session(body):
    if "problem" in body:
        pid = _field(body, "problem", str)
        files = _problem_files()
        if pid not in files:
            raise ApiError(400, "unknown-problem", f"no problem {pid!r}")
        p = files[pid][0]
        goal, sig = p.goal_text, p.sig
    else:
        goal, sig, pid = _field(body, "goal", str), _sig(body), None
    sid = secrets.token_hex(8)
    sess = S.Session(sid, goal, sig, pid)
    SESSIONS[sid] = sess
    return render(sess, sess.root())


def step(body):
    sess = _session(body)
    at = _node(sess, body)
    move = _field(body, "move", str)
    args = _field(body, "args", dict)
    return render(sess, sess.step(at.id, move, args))


def retract(body):
    sess = _session(body)
    return render(sess, sess.retract(_node(sess, body).id))


def node(query):
    sess = _session(query)
    return render(sess, _node(sess, query))


def tree(query):
    sess = _session(query)
    return {"session": sess.id, "problem": sess.problem_id,
            "nodes": [{"node": n.id, "parent": n.parent, "move": n.move,
                       "report": K.report(n.state),
                       "retracted": n.retracted, "summary": _summary(n)}
                      for n in sess.nodes.values()]}


def parse(body):
    text, sig = _field(body, "text", str), _sig(body)
    try:
        t = parse_goal(text, sig) if "==" in text else parse_term(text, sig)
    except Refused as r:
        raise Refusal.of(r) from None
    return {"term": _text(t), "katex": None}


def not_built(query):
    _node(_session(query), query)
    raise Refusal("not-built", "the assistance layer is not built yet")


ROUTES = {("GET", "/problems"): problems,
          ("POST", "/session"): new_session,
          ("POST", "/step"): step,
          ("POST", "/retract"): retract,
          ("GET", "/node"): node,
          ("GET", "/tree"): tree,
          ("POST", "/parse"): parse,
          ("GET", "/hint"): not_built,
          ("GET", "/palette"): not_built}


def handle(method, path, args):
    """Dispatch one request. `args` is the JSON body for POST, the query
    (str -> str) for GET. Returns (status, dict)."""
    route = ROUTES.get((method, path))
    if route is None:
        return 404, {"error": {"code": "unknown-route",
                               "message": f"no route {method} {path}"}}
    if not isinstance(args, dict):
        return 400, {"error": {"code": "bad-request",
                               "message": "the body is a JSON object"}}
    try:
        return 200, route(args)
    except Refusal as r:
        return 200, refusal(r)
    except ApiError as e:
        return e.status, {"error": {"code": e.code, "message": e.message}}
    except Exception as e:  # a kernel bug (E21), or ours: never a verdict
        return 500, {"error": {"code": "kernel-error",
                               "message": f"{type(e).__name__}: {e}"}}
