"""The work file (app/PERSIST.md): an attempt tree saved as moves, and
replayed through the kernel on load.

Untrusted. A work file holds what the page already sends: a goal, moves
and their arguments, the script text. It never holds a proof state, a
report, a theorem, an obligation or a handle, and nothing here reads one
from it: loading is `Session.step` from n0, so a stale or hand-edited file
can fail to replay but cannot produce a verdict (DESIGN.md §15.3).
"""

import hashlib
import json
import os
import re
import shutil
import tempfile
import time

import script
import session as S

FORMAT, VERSION = "calc-work", 1
_KEY = re.compile(r"[A-Za-z0-9._-]+\Z")


class BadDocument(ValueError):
    """Not a calc-work version 1 document."""


def key(problem, goal, functions):
    """The file key: the problem id when it is a safe name, else goal- and
    12 hex digits of SHA-256 over the goal and its sorted functions."""
    if (problem is not None and _KEY.match(problem)
            and problem not in (".", "..")
            and not problem.endswith((".prev", ".bad"))):
        return problem
    h = hashlib.sha256(json.dumps([goal, sorted(functions.items())])
                       .encode("utf-8")).hexdigest()
    return "goal-" + h[:12]


# ---------------------------------------------------------------- writing

def document(sess):
    """The work file for a session, as it would be saved now."""
    return {"format": FORMAT, "version": VERSION,
            "problem": sess.problem_id, "goal": sess.goal_text,
            "functions": dict(sess.sig),
            "script": getattr(sess, "script", ""),
            "path": list(getattr(sess, "path", ["n0"])),
            "max_rung": getattr(sess, "max_rung", 0),
            "nodes": [{"node": n.id, "parent": n.parent, "move": n.move,
                       "args": n.args, "retracted": n.retracted}
                      for n in sess.nodes.values() if n.parent is not None],
            "saved": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}


def path_of(directory, k):
    return os.path.join(directory, k + ".json")


def write(directory, k, doc):
    """Write doc to DIR/k.json atomically: a temporary file in DIR, then
    os.replace. Returns the path. Raises OSError."""
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix="." + k + ".", suffix=".tmp",
                               dir=directory)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=1, ensure_ascii=False)
            f.write("\n")
        dest = path_of(directory, k)
        os.replace(tmp, dest)
        return dest
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def set_aside(directory, k, suffix):
    """Copy DIR/k.json to DIR/k.<suffix>.json, if it exists."""
    src = path_of(directory, k)
    if os.path.exists(src):
        shutil.copyfile(src, os.path.join(directory, f"{k}.{suffix}.json"))
        return True
    return False


# ---------------------------------------------------------------- reading

def read(directory, k):
    """The document at DIR/k.json, or None when there is none. Raises
    BadDocument for a file that is not one, and OSError when it cannot be
    read at all (the file is then left alone)."""
    p = path_of(directory, k)
    if not os.path.exists(p):
        return None
    with open(p, "rb") as f:
        data = f.read()
    try:
        doc = json.loads(data.decode("utf-8"))
    except (ValueError, UnicodeDecodeError) as e:
        raise BadDocument(f"{os.path.basename(p)}: {e}") from None
    check(doc)
    return doc


def _is(v, kind):
    return isinstance(v, kind) and not (isinstance(v, bool) and kind is int)


def check(doc):
    """Raise BadDocument unless doc has the calc-work version 1 shape.
    Fields beyond the format's are ignored, never read."""
    if not isinstance(doc, dict):
        raise BadDocument("a work file is a JSON object")
    if doc.get("format") != FORMAT or doc.get("version") != VERSION:
        raise BadDocument(f"not a {FORMAT} version {VERSION} document")
    ok = (_is(doc.get("goal"), str)
          and (doc.get("problem") is None or _is(doc.get("problem"), str))
          and _is(doc.get("functions", {}), dict)
          and _is(doc.get("script", ""), str)
          and _is(doc.get("path", ["n0"]), list)
          and all(_is(p, str) for p in doc.get("path", []))
          and _is(doc.get("max_rung", 0), int)
          and _is(doc.get("nodes", []), list)
          and all(_is(n, dict) for n in doc.get("nodes", [])))
    if not ok:
        raise BadDocument("a field of the work file has the wrong type")


def replay(doc, sid, goal, sig, problem):
    """A Session rebuilt from doc's nodes by Session.step (PERSIST.md,
    Replay). `goal`, `sig` and `problem` are the caller's: for a problem,
    its own file's, never the document's copy. Returns (session, resumed)
    where resumed is PERSIST.md's object. Raises session.Refusal when the
    goal itself does not install."""
    sess = S.Session(sid, goal, sig, problem)
    ids, dropped = {"n0": "n0"}, []
    retracted = []
    for n in doc.get("nodes", []):
        old, parent = n.get("node"), n.get("parent")
        move, args = n.get("move"), n.get("args")
        if not (_is(old, str) and _is(parent, str) and _is(move, str)
                and _is(args, dict)) or old in ids:
            dropped.append({"node": old if _is(old, str) else None,
                            "move": move if _is(move, str) else None,
                            "code": "bad-node",
                            "message": "a malformed or repeated node"})
            continue
        if parent not in ids:
            dropped.append({"node": old, "move": move, "code": "dropped",
                            "message": f"its parent {parent} did not replay"})
            continue
        try:
            new = sess.step(ids[parent], move, args)
        except S.Refusal as r:
            dropped.append({"node": old, "move": move, "code": r.code,
                            "message": r.message})
            continue
        except Exception as e:  # a kernel bug on odd input: drop, go on
            dropped.append({"node": old, "move": move, "code": "kernel-error",
                            "message": f"{type(e).__name__}: {e}"})
            continue
        ids[old] = new.id
        if n.get("retracted") is True:
            retracted.append(new.id)
    for nid in retracted:
        sess.nodes[nid].retracted = True
    text = doc.get("script", "")
    path = []
    for p in doc.get("path", ["n0"]) or ["n0"]:
        if p not in ids or (path and sess.nodes[ids[p]].parent != path[-1]):
            break
        path.append(ids[p])
    if not path or path[0] != "n0":
        path = ["n0"]
    checked = checked_prefix(sess, text, path)
    path = path[:checked + 1]
    sess.script, sess.path = text, path
    sess.max_rung = max(0, doc.get("max_rung", 0))
    return sess, {"script": text, "path": path, "checked": checked,
                  "spans": [list(s) for s in script.spans(text)[:checked]],
                  "dropped": dropped, "ids": ids,
                  "max_rung": sess.max_rung}


def checked_prefix(sess, text, path):
    """The longest k such that sentence i of the script parses to node
    path[i+1]'s move and args, for every i < k, and none of those nodes is
    retracted."""
    k = 0
    for sentence, nid in zip(script.sentences(text), path[1:]):
        n = sess.nodes[nid]
        try:
            same = script.parse(sentence) == (n.move, n.args)
        except script.TacticError:
            same = False
        if not same or n.retracted:
            break
        k += 1
    return k
