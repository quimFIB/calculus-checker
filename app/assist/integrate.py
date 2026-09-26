"""The integral evaluator's two halves (app/EVAL.md), both untrusted.

`Proposer` runs sympy_propose.py in a Python that has SymPy, outside the
worker, killed at its time limit or on cancel (review 5).

`build` turns a proposal into a script with the kernel steering (review
1-3): ftc (adopting the kernel-checked STUCK.md suggestion for facts), then
a rewrite planner driven by E27's own close-not-evaluated, then close.
Every sentence goes through `step`, which the API supplies: it runs the
kernel from a state and records nothing. So a value is reported proved
only when the kernel's last report is exactly `Proved.`.
"""

import json
import os
import re
import shutil
import signal
import subprocess
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
PROPOSER = os.path.join(HERE, "sympy_propose.py")
MAX_REWRITES = 12
_ENTRY = re.compile(r"\(([A-Za-z_][A-Za-z0-9_]*)\)\s*$")
_FACT = re.compile(r"^fact\s+([A-Za-z_][A-Za-z0-9_']*)\s*:=")


# ---------------------------------------------------------------- proposer

_HAS = {}


def has_sympy(python):
    if python not in _HAS:
        try:
            r = subprocess.run([python, "-c", "import sympy"],
                               capture_output=True, timeout=30)
            _HAS[python] = r.returncode == 0
        except (OSError, subprocess.SubprocessError):
            _HAS[python] = False
    return _HAS[python]


def find_python(explicit=None):
    """--sympy, else $CALC_SYMPY, else python3 if it has SymPy; or None."""
    for c in (explicit, os.environ.get("CALC_SYMPY"),
              shutil.which("python3")):
        if c and has_sympy(c):
            return c
    return None


class Proposer:
    """One proposal at a time (review 5); cancel() kills the running one."""

    def __init__(self, python, timeout=5.0):
        self.python, self.timeout = python, timeout
        self.lock = threading.Lock()
        self.proc = None
        self.cancelled = False

    def propose(self, integral, functions=None, positive=()):
        if not self.python:
            return {"status": "no-proposer",
                    "message": "SymPy is not installed: start ./calc with "
                               "--sympy PYTHON, a Python that has it"}
        req = json.dumps({"integral": integral, "functions": functions or {},
                          "positive": list(positive)})
        with self.lock:
            self.cancelled = False
            try:
                self.proc = subprocess.Popen(
                    [self.python, PROPOSER], stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    text=True, start_new_session=True)
                out, _ = self.proc.communicate(req, timeout=self.timeout)
            except subprocess.TimeoutExpired:
                _kill(self.proc)
                self.proc.communicate()
                return {"status": "not-found", "message":
                        f"not found within {self.timeout:g} s; one may "
                        "well exist"}
            finally:
                proc, self.proc = self.proc, None
            if self.cancelled:
                return {"status": "cancelled", "message": "cancelled"}
            try:
                return json.loads(out)
            except ValueError:
                return {"status": "error", "message":
                        f"the proposer stopped ({proc.returncode})"}

    def cancel(self):
        p = self.proc
        if p is None:
            return False
        self.cancelled = True
        _kill(p)
        return True


def _kill(p):
    """The proposer and anything it started: its own process group."""
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except OSError:
        try:
            p.kill()
        except OSError:
            pass


# ---------------------------------------------------------------- builder

class Run:
    """A script being built: `step(text)` either advances or returns the
    refusal (a dict: code, message, residual, stuck)."""

    def __init__(self, start, step):
        self.start, self._step = start, step
        self.state, self.lines, self.facts = start, [], []

    def fork(self):
        r = Run(self.start, self._step)
        r.state, r.lines, r.facts = self.state, list(self.lines), \
            list(self.facts)
        return r

    def step(self, text):
        new, refusal = self._step(self.state, text)
        if refusal is not None:
            return refusal
        self.state = new
        self.lines.append(text)
        m = _FACT.match(text)
        if m:
            self.facts.append(m.group(1))
        return None

    def steps(self, texts):
        """All or nothing: the first refusal, else None."""
        trial = self.fork()
        for t in texts:
            r = trial.step(t)
            if r is not None:
                return r
        self.state, self.lines, self.facts = trial.state, trial.lines, \
            trial.facts
        return None

    def using(self):
        return f" using {', '.join(self.facts)}" if self.facts else ""


def _antiderivative(run, move, F):
    """ftc (or int_improper) with F: by ring, by field, then the STUCK.md
    suggestion (a fact and the move with it), which the kernel checked."""
    last = None
    for by in ("ring", "field"):
        r = run.step(f"{move} {F} by {by}.")
        if r is None:
            return None
        last = r
    sug = (last.get("stuck") or {}).get("suggest")
    if sug and run.steps(sug) is None:
        return None
    return last


def _close(run, values, side_of, report_of, rewrite_of):
    """Close with a value, rewriting what E27 says can still be
    evaluated."""
    last = None
    for _ in range(MAX_REWRITES + 1):
        for V in values:
            for by in ("ring", "field"):
                r = run.step(f"close {V} by {by}{run.using()}.")
                if r is None:
                    return None
                last = r
        side = side_of(run.state)
        r = run.step(f"close {side} by field{run.using()}.")
        if r is None:
            return None
        last = r
        if r.get("code") != "close-not-evaluated":
            return last
        m = _ENTRY.search(r.get("message") or "")
        if not m or not r.get("residual"):
            return last
        text = rewrite_of(m.group(1), r["residual"]) or \
            f"rewrite {m.group(1)} at {r['residual']}."
        rw = run.step(text)
        if rw is not None:
            sug = (rw.get("stuck") or {}).get("suggest")
            if not sug or run.steps(sug) is not None:
                return rw
    return last


def build(start, step, proposal, improper, side_of, report_of, normal,
          rewrite_of=lambda entry, residual: None):
    """The best script for `proposal` from state `start`.

    step(state, text) -> (state, None) | (None, refusal dict)
    side_of(state) -> the goal's value side as text
    report_of(state) -> kernel.report
    normal(text) -> the kernel's printing of a term, or None if it does
    not parse (a malformed proposal is refused at parse, not trusted).
    rewrite_of(entry, residual) -> the rewrite sentence, its `with`
    clause filled by matching the entry, or None."""
    move = "int_improper" if improper else "ftc"
    values = [normal(v) for v in [proposal.get("value")] +
              list(proposal.get("values") or []) if v]
    values = [v for i, v in enumerate(values) if v and v not in values[:i]]
    V = values[0] if values else None
    best = None  # (sentences, refusal) of the furthest attempt
    for raw in proposal.get("shapes") or []:
        F = normal(raw)
        if F is None:
            continue
        run = Run(start, step)
        r = _antiderivative(run, move, F)
        if r is not None:
            if best is None:
                best = (F, [], r, False)
            continue
        r = _close(run, values, side_of, report_of, rewrite_of)
        if r is None:
            if report_of(run.state) == "Proved.":
                return {"status": "proved", "antiderivative": F,
                        "value": _closed_value(run.lines[-1]),
                        "sentences": run.lines, "refusal": None,
                        "antiderivative_checked": True}
            r = {"code": "admissions", "message": report_of(run.state),
                 "residual": None}
        if best is None or not best[3]:
            best = (F, run.lines, r, True)
    if best is None:
        return None
    F, lines, r, checked = best
    return {"status": "unverified", "antiderivative": F, "value": V,
            "sentences": lines, "refusal": r,
            "antiderivative_checked": checked}


def _closed_value(close_line):
    """V from `close V [by ...] [using ...].`."""
    body = close_line[len("close "):].rstrip(".")
    return re.split(r"\s+(?:by|using)\s+", body)[0]


# ---------------------------------------------------------------- the route

def evaluate(handle, proposer, body):
    """POST /evaluate (EVAL.md, review 5): read the goal through the
    worker, propose outside it, check through it. `handle` is the
    backend's (method, path, args) -> (status, body)."""
    target = {k: body[k] for k in ("session", "node", "term", "functions")
              if k in body}
    status, goal = handle("POST", "/evaluate/goal", target)
    if status == 200 and "refusal" in goal:
        r = goal["refusal"]
        return 200, {"status": r["code"], "refusal": r,
                     "message": r["message"]}
    if status != 200 or "integral" not in goal:
        return status, goal
    prop = proposer.propose(goal["integral"], goal["functions"],
                            goal["positive"])
    return handle("POST", "/evaluate/check", dict(target, proposal=prop))
