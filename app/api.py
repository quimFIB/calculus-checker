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

import script
import session as S
import tex
import work
from assist import palette as PL
from assist import probe, progress, recognizer, stuck
from session import K, KERNEL, Refusal, loader
from terms import Integral, Refused, parse_goal, parse_term, show, trees

PROBLEMS = os.path.join(KERNEL, "problems")
WORK_DIR = None  # PERSIST.md: server.py sets it; None saves nothing
OWNER = {}  # PERSIST.md: key -> the id of the one session that may save it


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
            f"{a.get('var', '')} := {a['sub']}".strip(),
            "int_parts": a.get("u") and f"u := {a['u']}, v := {a.get('v')}",
            "int_improper": a.get("F") and f"F := {a['F']}"}.get(n.move)
    return f"{n.move} {main}" if main else n.move


def _tex(x):
    """tex.tex(x), or None: drawing never fails a response (UI.md §1)."""
    if x is None:
        return None
    try:
        return tex.tex(x)
    except Exception:
        return None


def _assist(fn, *args):
    """An assistance call that must not fail the response: None instead."""
    try:
        return fn(*args)
    except Exception:
        return None


def _steps_to(sess, n):
    k = 0
    while n.parent is not None:
        n, k = sess.nodes[n.parent], k + 1
    return k


def render(sess, n):
    st = n.state
    parent = None if n.parent is None else sess.nodes[n.parent].state
    before = (set() if parent is None else
              {ob.key for ob in parent.obligations()})
    obs = [_obligation(ob, before) for ob in st.obligations()]
    return {"session": sess.id, "node": n.id, "parent": n.parent,
            "move": n.move, "report": K.report(st),
            "goal": None if st.goal is None else _text(st.goal),
            "theorem": None if st.theorem is None else _text(st.theorem),
            "goal_tex": _tex(st.goal), "theorem_tex": _tex(st.theorem),
            "admissions": sum(ob.status == K.ADMITTED
                              for ob in st.obligations()),
            "steps": _steps_to(sess, n),
            "progress": None if parent is None else _assist(
                progress.signal, parent.goal, st.goal),
            "probe": None if parent is None or st.goal is None
            or parent.goal is None else _assist(
                probe.compare, parent.goal, st.goal),
            "obligations": obs,
            "stuck": None if parent is None else _assist(
                stuck.admitted, obs),
            "occurrences": st.last.occurrences,
            "handles": sorted(n.handles), "retracted": n.retracted}


def refusal(r):
    return {"refusal": {"code": r.code, "message": r.message,
                        "residual": None if r.residual is None
                        else _text(r.residual),
                        "stuck": getattr(r, "stuck", None)}}


# ---------------------------------------------------------------- stuck

def _trial(sess, at, sentences):
    """Whether the kernel accepts `sentences` in order from node `at`.
    Nothing is recorded: kernel states are values, and no node is added."""
    state, handles = at.state, dict(at.handles)
    for text in sentences:
        move, args = script.parse(text)
        r = K.step(state, move, loader.step_args(args, handles, sess.sig))
        if isinstance(r, K.Refusal):
            return False
        if move == "fact":
            handles[args["bind"]] = r.last.handle
        state = r
    return True


def _stepped(sess, at, move, args):
    """sess.step, with a refusal's STUCK.md explanation attached."""
    try:
        return sess.step(at.id, move, args)
    except Refusal as r:
        _explain(r, sess, at, move, args)
        raise


def _explain(r, sess, at, move, args):
    r.stuck = _assist(lambda: stuck.explain(
        r.code, r.message, r.residual, at.state.goal, move, args,
        sig=sess.sig, handles=at.handles,
        trial=lambda ss: _trial(sess, at, ss), show_move=script.show))


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


def _goal_of(body):
    """(goal, sig, problem id) for a /session body: a problem's from its
    own file, else the body's goal and functions."""
    if "problem" in body:
        pid = _field(body, "problem", str)
        files = _problem_files()
        if pid not in files:
            raise ApiError(400, "unknown-problem", f"no problem {pid!r}")
        p = files[pid][0]
        return p.goal_text, p.sig, pid
    return _field(body, "goal", str), _sig(body), None


def new_session(body):
    goal, sig, pid = _goal_of(body)
    resume = _field(body, "resume", bool, optional=True) or False
    k = work.key(pid, goal, sig)
    sid = secrets.token_hex(8)
    resumed, old, unreadable = None, None, False
    if WORK_DIR:
        try:
            old = work.read(WORK_DIR, k)
        except work.BadDocument as e:
            _aside(k, "bad", move=True)
            resumed = {"error": str(e)}
        except OSError as e:
            resumed = {"error": f"{type(e).__name__}: {e}"}
            unreadable = True
    if resume and old is not None:
        sess, resumed = work.replay(old, sid, goal, sig, pid)
    else:
        sess = S.Session(sid, goal, sig, pid)
        if old is not None:  # Start fresh: keep the old file, and its rung
            _aside(k, "prev")
            sess.max_rung = max(0, old.get("max_rung", 0))
        if not resume:
            resumed = None
    if unreadable:  # never save over a file that could not be read
        sess.key, SESSIONS[sess.id], OWNER[k] = k, sess, None
        sess.saved = {"error": resumed["error"]}
    else:
        _own(sess, k)
    return dict(render(sess, sess.root()), resumed=resumed, problem=pid,
                key=k)


def _own(sess, k):
    """Register the session, make it the key's one writer (PERSIST.md,
    ownership), and save at once, so a fresh start sticks."""
    sess.key = k
    SESSIONS[sess.id] = sess
    OWNER[k] = sess.id
    _save(sess)


def _aside(k, suffix, move=False):
    """PERSIST.md: keep the file about to be replaced (or unreadable)."""
    if not WORK_DIR:
        return
    try:
        if work.set_aside(WORK_DIR, k, suffix) and move:
            os.unlink(work.path_of(WORK_DIR, k))
    except OSError:
        pass


def _save(sess):
    """Write the session's work file. Never fails the request: the outcome
    is kept for /tree's `saved`."""
    if not WORK_DIR:
        return False
    if OWNER.get(sess.key) != sess.id:
        if OWNER.get(sess.key) is not None:
            sess.saved = {"error": "superseded: this goal was opened "
                                   "again, and the newer one is saved"}
        return False
    try:
        f = work.write(WORK_DIR, sess.key, work.document(sess))
        sess.saved = {"file": f, "at": work.document(sess)["saved"]}
        return True
    except (OSError, TypeError, ValueError) as e:
        sess.saved = {"error": f"{type(e).__name__}: {e}"}
        return False


def save_script(body):
    """PERSIST.md: the page's script and checked path, then a save."""
    sess = _session(body)
    text = _field(body, "script", str)
    path = _field(body, "path", list)
    if not path or path[0] != "n0" or not all(
            isinstance(p, str) and p in sess.nodes for p in path):
        raise _bad("path is a list of this session's node ids from n0")
    sess.script, sess.path = text, list(path)
    return {"saved": _save(sess)}


def export(query):
    return work.document(_session(query))


def import_(body):
    doc = _field(body, "document", dict)
    try:
        work.check(doc)
    except work.BadDocument as e:
        raise ApiError(400, "bad-document", str(e)) from None
    pid = doc.get("problem")
    if pid is not None:
        files = _problem_files()
        if pid not in files:
            raise ApiError(400, "bad-document", f"no problem {pid!r}")
        p = files[pid][0]
        goal, sig = p.goal_text, p.sig
    else:
        fns = doc.get("functions", {})
        if not all(isinstance(k, str) and type(v) is int and v > 0
                   for k, v in fns.items()):
            raise ApiError(400, "bad-document",
                           "functions maps names to positive arities")
        goal, sig = doc["goal"], fns
    sess, resumed = work.replay(doc, secrets.token_hex(8), goal, sig, pid)
    k = work.key(pid, goal, sig)
    _aside(k, "prev")
    _own(sess, k)
    return dict(render(sess, sess.root()), resumed=resumed, problem=pid,
                key=k)


def step(body):
    sess = _session(body)
    at = _node(sess, body)
    move = _field(body, "move", str)
    args = _field(body, "args", dict)
    n = _stepped(sess, at, move, args)
    _save(sess)
    return render(sess, n)


def tactic(body):
    """SCRIPT.md: one sentence, parsed to (move, args) and fed as /step."""
    sess = _session(body)
    at = _node(sess, body)
    try:
        move, args = script.parse(_field(body, "text", str))
    except script.TacticError as e:
        r = Refusal("bad-tactic", str(e))
        _explain(r, sess, at, None, None)
        raise r from None
    n = _stepped(sess, at, move, args)
    _save(sess)
    return render(sess, n)


def retract(body):
    sess = _session(body)
    n = sess.retract(_node(sess, body).id)
    _save(sess)
    return render(sess, n)


def node(query):
    sess = _session(query)
    return render(sess, _node(sess, query))


def tree(query):
    sess = _session(query)
    return {"session": sess.id, "problem": sess.problem_id,
            "max_rung": getattr(sess, "max_rung", 0),
            "saved": getattr(sess, "saved", None),
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
    return {"term": _text(t), "katex": _tex(t)}


# PAGE.md: the optional arguments the kernel's _check_args accepts
_OPTIONAL = {"rewrite": ("occurrence",), "int_flip": ("occurrence",),
             "ftc": ("occurrence",), "int_parts": ("occurrence",),
             "int_improper": ("occurrence",),
             "int_subst": ("mode", "occurrence", "f")}


def moves(_):
    """Every kernel move in MOVES order, with its arguments typed as the
    loader reads them (PAGE.md), so the page builds its form from this."""
    def arg(name, optional):
        return {"name": name, "type": loader.ARG_TYPES[name].__name__,
                "term": name in loader.TERM_ARGS, "optional": optional}
    return {"moves": [
        {"name": m, "args": [arg(a, False) for a in K._ARGS[m]]
         + [arg(a, True) for a in _OPTIONAL.get(m, ())]}
        for m in K.MOVES]}


def hint(query):
    """RECOGNIZER.md, the ladder: rung 1, 2 or 3 of the first row that
    matches the first Int in the node's goal (pre-order)."""
    sess = _session(query)
    n = _node(sess, query)
    rung = _field(query, "rung", str)
    if rung == "4":
        raise Refusal("not-built", "rung 4 would make the move; it is not "
                      "built")
    if rung not in ("1", "2", "3"):
        raise _bad(f"rung is 1, 2, 3 or 4, not {rung!r}")
    sess.max_rung = max(getattr(sess, "max_rung", 0), int(rung))
    _save(sess)
    goal = n.state.goal
    ints = [] if goal is None else [t for t in trees(goal)
                                    if isinstance(t, Integral)]
    if not ints:
        raise Refusal("no-integral", "the goal holds no integral")
    i = ints[0]
    step = recognizer.ladder(i.body, i.var)
    if step is None:
        raise Refusal("no-row", f"no row of the table matches "
                      f"{_text(i.body)} in {i.var}")
    return {"rung": int(rung), "integral": _text(i), "row": step["row"],
            "text": step[int(rung)], "cost": step["cost"]}


def palette(query):
    """UI.md §2: the moves that fit, the rewrites that match, the card."""
    sess = _session(query)
    return PL.palette(_node(sess, query).state.goal)


ROUTES = {("GET", "/problems"): problems,
          ("POST", "/session"): new_session,
          ("POST", "/step"): step,
          ("POST", "/tactic"): tactic,
          ("POST", "/retract"): retract,
          ("GET", "/node"): node,
          ("GET", "/tree"): tree,
          ("POST", "/parse"): parse,
          ("GET", "/moves"): moves,
          ("GET", "/hint"): hint,
          ("GET", "/palette"): palette,
          ("POST", "/script"): save_script,
          ("GET", "/export"): export,
          ("POST", "/import"): import_}


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
