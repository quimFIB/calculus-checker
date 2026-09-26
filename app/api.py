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
import re
import secrets

import dx
import pretty2d
import script
import session as S
import tex
import untex
import work
from assist import palette as PL
from assist import classify as CL
from assist import factor as FA
from assist import integrate, probe, progress, recognizer, stuck
from session import K, KERNEL, Refusal, loader
from entries import STATEMENTS as ENTRY_TEXT
from terms import (Integral, MVar, Neg, Num, NegInf, PosInf, Refused, Rel, Var,
                   parse_goal, parse_judgement, parse_term, show, trees)

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
    return {"key": _text(ob.key), "key_tex": _tex(ob.key),
            "sources": sorted(ob.sources),
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
            "int_improper": a.get("F") and f"F := {a['F']}",
            "taylor_lagrange": a.get("f") and
            f"{a.get('bind')} := {a.get('side')} of {a['f']} at {a.get('at')}",
            "bound": a.get("facts") and ", ".join(
                f[1] for f in a["facts"]),
            "verify": a.get("check") and f"by {a['check']}"}.get(n.move)
    return f"{n.move} {main}" if main else n.move


def _tex(x):
    """tex.tex(x), or None: drawing never fails a response (UI.md §1)."""
    if x is None:
        return None
    try:
        return tex.tex(x)
    except Exception:
        return None


def _2d(x):
    """pretty2d.pretty(x), or None, as _tex (GOALS2D.md)."""
    if x is None:
        return None
    try:
        return pretty2d.pretty(x)
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
            "goal_2d": _2d(st.goal), "theorem_2d": _2d(st.theorem),
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
                        "residual_tex": _tex(r.residual),
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
        if move in ("fact", "taylor_lagrange"):  # both bind a handle
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
    own file, else the body's goal and functions. A .dx header (DX.md) is
    read into one of those first."""
    if "header" in body:
        try:
            h = dx.header(_field(body, "header", str))
        except dx.HeaderError as e:
            raise Refusal("bad-header", str(e)) from None
        body = {k: v for k, v in body.items() if k != "header"}
        body.update(h)
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
                key=k, functions=sig)


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


def restore(docs, owner=None, saved=None):
    """TIMEOUT.md: rebuild sessions from their work documents under their
    own ids after a worker restart. Path, script, max rung and save state
    come back exactly, and every node keeps its id or the session fails;
    OWNER is set from `owner`, as it was; nothing is written. Returns
    (restored ids, {id: why} for the ones that failed)."""
    if owner is not None:
        OWNER.clear()
        OWNER.update(owner)
    done, failed = [], {}
    for sid, doc in docs.items():
        try:
            work.check(doc)
            pid = doc.get("problem")
            if pid is not None:
                p = _problem_files()[pid][0]
                goal, sig = p.goal_text, p.sig
            else:
                goal, sig = doc["goal"], doc.get("functions", {})
            sess, got = work.replay(doc, sid, goal, sig, pid)
            if got["dropped"] or any(k != v for k, v in got["ids"].items()):
                raise ValueError(f"{len(got['dropped'])} node(s) did not "
                                 "replay under their own ids")
            sess.path = [got["ids"][p] for p in doc.get("path", ["n0"])]
            sess.script = doc.get("script", "")
            sess.max_rung = doc.get("max_rung", 0)
            sess.key = work.key(pid, goal, sig)
            sess.saved = (saved or {}).get(sid)
            SESSIONS[sid] = sess
            done.append(sid)
        except Exception as e:
            failed[sid] = f"{type(e).__name__}: {e}"
    return done, failed


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
                key=k, functions=sig)


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
            "evaluations": list(getattr(sess, "evaluations", [])),
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


def _term_tex(text, sig):
    """PRETTY.md: a term segment's TeX: "" for the palette's hole `_`,
    None when the term does not parse (the page keeps it as text)."""
    if text.strip() == "_":
        return ""
    try:
        return _tex(parse_term(text, sig))
    except Refused:
        return None


def layout(body):
    """PRETTY.md: the script cut into sentence, gap and open pieces that
    cover it exactly; a sentence's term segments carry their TeX."""
    text, sig = _field(body, "text", str), _sig(body)
    pieces, at = [], 0

    def plain(kind, a, b):
        if a < b:
            pieces.append({"kind": kind, "start": a, "end": b,
                           "segments": [{"text": text[a:b]}]})
    for a, b in script.spans(text):
        plain("gap", at, a)
        segs = script.layout(text[a:b])
        for seg in segs:
            if "term" in seg:
                seg["tex"] = _term_tex(seg["term"], sig)
        pieces.append({"kind": "sentence", "start": a, "end": b,
                       "segments": segs})
        at = b
    # after the last sentence: comments and space are a gap; anything
    # else (an unfinished sentence, an unclosed comment) is the open piece
    rest = re.sub(r"\(\*.*?\*\)", "", text[at:], flags=re.S)
    if rest.strip():
        lead = len(text[at:]) - len(text[at:].lstrip(script.SPACE))
        plain("gap", at, at + lead)
        plain("open", at + lead, len(text))
    else:
        plain("gap", at, len(text))
    return {"pieces": pieces}


def drop(body):
    """LSP.md review 3: forget a session (its nodes and states). App-side
    only; the work file, if any, is untouched."""
    sid = _field(body, "session", str)
    sess = SESSIONS.pop(sid, None)
    if sess is not None and OWNER.get(getattr(sess, "key", None)) == sid:
        OWNER[sess.key] = None
    return {"dropped": sess is not None}


# ---------------------------------------------------------------- evaluate

def _eval_target(body):
    """EVAL.md: (start state, handles, sig, goal, session or None) for
    {session, node} or {term, functions?}. A term gets an unregistered
    session: never _own or _save, so it takes no work file (review 4)."""
    if "term" in body:
        term, sig = _field(body, "term", str), _sig(body)
        try:
            t = parse_term(term, sig)
        except Refused as r:
            raise Refusal.of(r) from None
        if not isinstance(t, Integral):
            raise Refusal("not-an-integral", "evaluate takes a definite "
                          "integral, Int[x = a .. b] f")
        try:
            sess = S.Session("scratch", show(t) + " == ?A", sig)
        except Refusal as r:
            raise Refusal("refused-goal", f"{r.code}: {r.message}") from None
        n = sess.root()
        return n.state, dict(n.handles), sig, n.state.goal, None, n
    sess = _session(body)
    n = _node(sess, body)
    return n.state, dict(n.handles), sess.sig, n.state.goal, sess, n


def _integral_of(goal):
    """The goal's integral and the parameters its domain says are > 0, or
    a not-an-integral-goal refusal naming the shape wanted."""
    ok = (goal is not None and len(goal) == 1 and isinstance(goal[0], Rel)
          and goal[0].op == "==" and isinstance(goal[0].lhs, Integral)
          and isinstance(goal[0].rhs, MVar))
    if not ok:
        raise Refusal("not-an-integral-goal", "evaluate wants a goal of the "
                      "shape Int[x = a .. b] f == ?A")
    positive = [d.lhs.name for d in goal[0].dom
                if isinstance(d, Rel) and d.op == ">" and
                isinstance(d.lhs, Var) and d.rhs == Num(0)]
    t = goal[0].lhs
    improper = any(isinstance(e, (PosInf, NegInf)) for e in (t.lo, t.hi))
    return t, positive, improper


def evaluate_goal(body):
    """EVAL.md, review 5: what the proposer needs, read without it."""
    _, _, sig, goal, _, n = _eval_target(body)
    t, positive, improper = _integral_of(goal)
    return {"integral": show(t), "functions": sig, "positive": positive,
            "improper": improper, "node": n.id}


def _eval_step(sig):
    def step(st, text):
        state, handles = st
        try:
            move, args = script.parse(text)
        except script.TacticError as e:
            return None, {"code": "bad-tactic", "message": str(e),
                          "residual": None}
        try:
            r = K.step(state, move, loader.step_args(args, handles, sig))
        except Refused as e:
            r = e
        if isinstance(r, (K.Refusal, Refused)):
            res = getattr(r, "residual", None)
            out = {"code": r.code, "message": r.message,
                   "residual": None if res is None else _text(res)}
            out["stuck"] = _assist(lambda: stuck.explain(
                r.code, r.message, res, state.goal, move, args, sig=sig,
                handles=handles, trial=lambda ss: _trial_at(
                    state, handles, sig, ss), show_move=script.show))
            return None, out
        handles = dict(handles)
        if move in ("fact", "taylor_lagrange"):
            handles[args["bind"]] = r.last.handle
        return (r, handles), None
    return step


def _match(pat, t, schema, inst):
    """Structural match of an entry's side against a term: schema
    variables bind (consistently), everything else must be equal."""
    if isinstance(pat, Var) and pat.name in schema:
        if pat.name in inst:
            return inst[pat.name] == t
        inst[pat.name] = t
        return True
    if isinstance(pat, Neg) and isinstance(pat.a, Var) and \
            pat.a.name in schema and not isinstance(t, Neg):
        # -u against an argument that is negative only up to arithmetic
        # (atan((2*0 - 1)/sqrt 3)): u := -(t); the kernel checks -u = t
        return _match(pat.a, Neg(t), schema, inst)
    if type(pat) is not type(t):
        return False
    if not hasattr(pat, "__dataclass_fields__"):
        return pat == t
    for f in pat.__dataclass_fields__:
        a, b = getattr(pat, f), getattr(t, f)
        if hasattr(a, "__dataclass_fields__"):
            if not _match(a, b, schema, inst):
                return False
        elif isinstance(a, tuple):
            if len(a) != len(b) or not all(
                    _match(x, y, schema, inst) for x, y in zip(a, b)):
                return False
        elif a != b:
            return False
    return True


def _rewrite_of(sig):
    """EVAL.md's planner: `rewrite ENTRY [with u := T] at R.` for the
    entry E27 named and the subterm it left, or None."""
    def rw(entry, residual):
        if entry not in ENTRY_TEXT:
            return None
        text, schema = ENTRY_TEXT[entry]
        try:
            lhs = parse_judgement(text).lhs
            r = parse_term(residual, sig)
        except (Refused, AttributeError):
            return None
        inst = {}
        if not _match(lhs, r, set(schema), inst):
            return None
        with_ = "; ".join(f"{v} := {show(inst[v])}" for v in schema)
        return (f"rewrite {entry}" + (f" with {with_}" if with_ else "") +
                f" at {residual}.")
    return rw


def _trial_at(state, handles, sig, sentences):
    handles = dict(handles)
    for text in sentences:
        move, args = script.parse(text)
        r = K.step(state, move, loader.step_args(args, handles, sig))
        if isinstance(r, K.Refusal):
            return False
        if move in ("fact", "taylor_lagrange"):
            handles[args["bind"]] = r.last.handle
        state = r
    return True


def _numeric(goal):
    try:
        v = probe.value(goal)
    except probe.Skip as e:
        return {"skipped": str(e)}
    except Exception as e:  # never fail the response
        return {"skipped": f"{type(e).__name__}"}
    old = probe.TOL
    try:
        probe.TOL = old / 2
        w = probe.value(goal)
    except Exception:
        w = v
    finally:
        probe.TOL = old
    return {"value": v, "digits": probe.digits(v, w)}


def evaluate_check(body):
    """EVAL.md: the kernel's half. `proposal` is sympy_propose.py's answer
    (untrusted); nothing is recorded in the tree."""
    state, handles, sig, goal, sess, n = _eval_target(body)
    t, _, improper = _integral_of(goal)
    prop = body.get("proposal")
    if not isinstance(prop, dict):
        raise ApiError(400, "bad-request", "proposal is an object")

    def normal(text):
        try:
            return show(parse_term(text, sig))
        except (Refused, TypeError, ValueError):
            return None

    out = {"status": prop.get("status") or "error", "term": show(t),
           "value": None, "antiderivative": None, "sentences": [],
           "antiderivative_checked": False, "refusal": None,
           "message": prop.get("message") or "", "node": n.id}
    if out["status"] == "ok":
        built = integrate.build(
            (state, handles), _eval_step(sig), prop, improper,
            side_of=lambda st: show(st[0].goal[0].lhs),
            report_of=lambda st: K.report(st[0]), normal=normal,
            rewrite_of=_rewrite_of(sig))
        if built is None:
            out.update(status="outside-grammar",
                       message="SymPy's answer did not parse as a term")
        else:
            out.update(built)
            if built["status"] == "proved":
                out["message"] = "Proved by the kernel."
            else:
                r = built["refusal"] or {}
                if r.get("code") == "admissions":
                    out["message"] = ("SymPy's answer, not verified: the "
                                      "kernel's proof reads "
                                      f"\"{r.get('message')}\"")
                else:
                    out["message"] = ("SymPy's answer, not verified: the "
                                      f"kernel said {r.get('code')}: "
                                      f"{r.get('message')}")
    if out["status"] != "proved" and out["value"] is None and \
            prop.get("value"):
        out["value"] = normal(prop["value"])
    if prop.get("value_note"):
        out["message"] = (out["message"] + " " + prop["value_note"]).strip()
    out["value_tex"] = _term_tex(out["value"], sig) if out["value"] else None
    out["antiderivative_tex"] = _term_tex(out["antiderivative"], sig) \
        if out["antiderivative"] else None
    out["numeric"] = _numeric(goal)
    if sess is not None:
        sess.evaluations = getattr(sess, "evaluations", []) + [{
            "node": n.id, "status": out["status"], "value": out["value"],
            "sentences": out["sentences"]}]
        _save(sess)
    return out


def templates(_):
    """PRETTY.md, autocomplete: each move's template and its usage line."""
    return {"templates": [{"move": m, "template": t, "usage": script.USAGE[m]}
                          for m, t in script.TEMPLATES.items()]}


def untex_(body):
    """PRETTY.md: the term a MathLive field holds, as canonical text."""
    latex, sig = _field(body, "latex", str), _sig(body)
    try:
        t = untex.read(latex, sig)
    except untex.TexError as e:
        raise Refusal("bad-tex", str(e)) from None
    except Refused as r:
        raise Refusal.of(r) from None
    return {"term": _text(t), "tex": _tex(t)}


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


def _factor_args(body):
    """FACTOR.md: the term, its variable and the field of a /factor or
    /apart body."""
    fld = _field(body, "field", str)
    if fld not in ("Q", "R"):
        raise _bad("field is Q or R")
    var = _field(body, "var", str)
    try:
        t = parse_term(_field(body, "term", str), _sig(body))
    except Refused as r:
        raise Refusal.of(r) from None
    return t, var, fld


def _factor_call(fn, *args):
    try:
        return fn(*args)
    except FA.Refusal as r:
        raise Refusal(r.code, r.message) from None


def _with_tex(out, *keys):
    """The answer's terms as TeX too (UI.md §1), for the page."""
    for k in keys:
        if out.get(k) is not None:
            out[k + "_tex"] = _tex(parse_term(out[k], {}))
    return out


def factor(body):
    """FACTOR.md: a polynomial, or a rational function's denominator,
    factored over Q or R, checked by the kernel."""
    return _with_tex(_factor_call(FA.factor, *_factor_args(body)),
                     "product")


def classify(body):
    """CLASSIFY.md: F(t), F(v), F(x) or none, from the force's free
    variables (§12.1); a report, not a judgement."""
    force = _field(body, "force", str)
    names = {k: _field(body, k, str, optional=True) or k
             for k in ("t", "v", "x")}
    try:
        return CL.classify(force, sig=_sig(body), **names)
    except CL.Refusal as e:
        raise Refusal(e.code, e.message) from None


def apart(body):
    """FACTOR.md: partial fractions over Q or R, checked by the kernel."""
    t, var, fld = _factor_args(body)
    ansatz = _field(body, "ansatz", list, optional=True)
    if ansatz is not None and not all(
            isinstance(a, dict) and isinstance(a.get("den"), str)
            and a.get("numerator") in ("constant", "linear") for a in ansatz):
        raise _bad("ansatz is a list of {den: term, numerator: "
                   "constant|linear}")
    return _with_tex(_factor_call(FA.apart, t, var, fld, ansatz), "sum")


ROUTES = {("GET", "/problems"): problems,
          ("POST", "/session"): new_session,
          ("POST", "/step"): step,
          ("POST", "/tactic"): tactic,
          ("POST", "/retract"): retract,
          ("GET", "/node"): node,
          ("GET", "/tree"): tree,
          ("POST", "/parse"): parse,
          ("POST", "/layout"): layout,
          ("POST", "/untex"): untex_,
          ("GET", "/templates"): templates,
          ("POST", "/drop"): drop,
          ("POST", "/evaluate/goal"): evaluate_goal,
          ("POST", "/evaluate/check"): evaluate_check,
          ("GET", "/moves"): moves,
          ("GET", "/hint"): hint,
          ("GET", "/palette"): palette,
          ("POST", "/script"): save_script,
          ("GET", "/export"): export,
          ("POST", "/import"): import_,
          ("POST", "/factor"): factor,
          ("POST", "/apart"): apart,
          ("POST", "/classify"): classify}


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
