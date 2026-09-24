"""The proof-of-life's done script, and the kernel's regression suite.

    python3 kernel/proof_of_life.py                 run every Done-when check
    python3 kernel/proof_of_life.py --plant NAME    one planted bug (a child)
    python3 kernel/proof_of_life.py --mutate NAME   one definedness mutation (a child)
    python3 kernel/proof_of_life.py --control       the same child, unpatched
    python3 kernel/proof_of_life.py --backstop NAME one closing check_goal, reached through a seam (a child)
    python3 kernel/proof_of_life.py --isolate NAME  one E26 (b) seam weakened alone (a child)

It asserts every item of WHAT.md's "Done when" against p1_expected.py, which
was written before the kernel and is never changed to fit it. The header
prints the protection in force, handles for facts and the sentinel for
proof states, with the reason the sentinel is enough for states. It was written
from kernel/ARCHITECTURE.md, the skeletons' signatures and p1_expected.py
alone, not from the kernel's code, so it tests the contract rather than
mirroring the implementation.

  1  proves P1.1, its fallback, P1.2 and P1.2-alt: every step accepted, each
     goal_after as a tree, the theorem, N and the verdict string;
  2  every step's obligation list (key, sources, status, tag, reason, new),
     deriv's trace and output, the final tracker, and no admission tagged
     none; also MATCH_ACCEPTS, DEFINEDNESS_CASES (E26: installation's and
     the close's lists, the final tracker, the report exactly), OCCURRENCE_CASE
     and the pinned entries, and
     the suite's own cases for what P1's data masks: field's divisors in
     atom arguments, ftc's charge of F's formers, emission placement, and
     TAG_RULES read both ways;
  3  each PLANTED_BUGS mutation, and each DEFINEDNESS_MUTATIONS one,
     patched into a child process through the seams of ARCHITECTURE.md §7,
     is caught at every `caught_by` location, with N as the data gives it;
  4  each WRONG_ANSWERS move is refused, its residual equal to the expected
     one under `compare` and not zero; deriv's trace on W1, and on the
     divisor-owing rules P1 never reaches;
  5  each BAD_MOVES refusal code, the suite's own bad moves for the codes and
     rule clauses no p1_expected case reaches, a check that every
     REFUSAL_CODES code (p1_expected's "unreachable in P1" notes excuse
     none), every kernel-local code and every GRAMMAR.md §1 code is
     asserted somewhere,
     the closing check_goal of rewrite and ftc reached through a seam
     (BACKSTOPS, each in a child process), install's hypothesis gate and
     E7's own Int-or-D check each weakened alone (ISOLATED_SEAMS, likewise),
     each FORGERIES case by its
     accept rule, and the review's trust cases:
     hand-built trees, vars() writes, a report that fails closed, a
     read-only cite library and deriv rule table;
  6  the echo of each goal, ROUND_TRIP, the S-expression trees, PRINT_EXACT
     and the parse refusals.

It also runs the unit tests (test_field.py, test_grammar.py) in a child
process, as one check of its own beside items 1-6: field's planted bugs
neg_power_wrong_divisor and reduce_drops_q pass items 1-6 and are caught
there only, so this one command is the whole regression suite.

It does not stop at the first failure. Each check prints PASS or FAIL with
its details, the summary counts them per item, the verdict of each proof is
printed last, and the exit status is 1 if anything failed. Standard library
only: it must run with nothing installed.
"""

import contextlib
import copy
import dataclasses
import inspect
import io
import json
import math
import os
import pickle
import re
import subprocess
import sys
import traceback
import types
from collections import Counter

import p1_expected as X
import terms as T

# The kernel is imported apart from the parser, so that item 6's parser
# checks still run, and every other check reports why it could not, when the
# kernel does not import.
try:
    import deriv as DV
    import entries as EN
    import field as FD
    import kernel as K
    import tagger as TG
    KERNEL_ERROR = None
except Exception as e:  # noqa: BLE001 -- reported, never swallowed
    DV = EN = FD = K = TG = None
    KERNEL_ERROR = "".join(traceback.format_exception_only(type(e), e)).strip()

SIG = X.SIG
ITEMS = {
    1: "proves P1.1 == 2 and P1.2 in both forms",
    2: "obligation lists, domains and tags",
    3: "fails on the planted bugs",
    4: "rejects wrong answers, asserting the residual",
    5: "refuses bad moves and forgeries",
    6: "round-trips the parser, echoes each goal",
}
UNIT, UNIT_TEXT = "unit", "unit tests: test_field.py, test_grammar.py"  # beside 1-6
MAX_SHOWN = 12  # detail lines printed under one failed check


# ---------------------------------------------------------------- data to calls
#
# ARCHITECTURE.md §4's mapping. Every term string goes through parse_term
# with SIG, every goal through parse_goal, and every expected obligation
# through parse_judgement(judgement_string(prop, dom)), so the comparisons
# below are between trees, never strings.

def term(s):
    return T.parse_term(s, SIG)


def goal(s):
    return T.parse_goal(s, SIG)


def key(prop, dom):
    """The obligation key an expected (prop, dom) names (E8)."""
    return T.parse_judgement(X.judgement_string(prop, dom), SIG)


def tag_of(ob):
    return (ob.tag[0], tuple(ob.tag[1]))


def fact_object(ref, handles, forged):
    if ref == "FORGED":
        return forged
    kind, s = ref
    if kind == "handle":
        return handles[s]
    if kind == "raw":
        return T.parse_judgement(s, SIG)
    raise ValueError(f"unknown fact reference {ref!r}")


def build_args(args, handles, forged=None):
    """A p1_expected args dict as step() takes it."""
    out = {}
    for k, v in args.items():
        if k in ("at", "F", "value"):
            out[k] = term(v)
        elif k == "inst":
            out[k] = {var: term(s) for var, s in v.items()}
        elif k == "facts":
            out[k] = [fact_object(f, handles, forged) for f in v]
        else:  # entry, bind, check, occurrence
            out[k] = v
    return out


def show(x):
    return "None" if x is None else T.show(x)


def describe(r):
    if isinstance(r, K.Refusal):
        return f"refused {r.code}: {r.message}"
    if isinstance(r, K.ProofState):
        return "a new state"
    return repr(r)


def fmt(where, detail):
    parts = [" @ ".join(w) if isinstance(w, tuple) else str(w) for w in where]
    return f"{' / '.join(parts)}: {detail}"


def tuplify(x):
    """JSON gives lists; caught_by is written with tuples."""
    return tuple(map(tuplify, x)) if isinstance(x, (list, tuple)) else x


class Mismatch(Exception):
    """The suite's own failure, one that stops a run: a refused step, say.
    `where` has one of PLANTED_BUGS' caught_by shapes, or one like them."""

    def __init__(self, item, where, detail):
        super().__init__(fmt(where, detail))
        self.item, self.where, self.detail = item, where, detail


def install(g, where):
    st = K.install(goal(g))
    if not isinstance(st, K.ProofState):
        raise Mismatch(1, where + ("refused",), describe(st))
    return st


def take(state, move, args, handles, where):
    """step(), with a refusal raised as Mismatch. A fact step binds its
    handle under args["bind"]."""
    r = K.step(state, move, build_args(args, handles))
    if not isinstance(r, K.ProofState):
        raise Mismatch(1, where + ("refused",), describe(r))
    if move == "fact":
        handles[args["bind"]] = r.last.handle
    return r


def replay(proof, through):
    """The state after step `through` of PROOFS[proof], and the handles bound
    on the way. Each call is a fresh install, so a fresh lineage."""
    p = X.PROOFS[proof]
    st, handles = install(p["goal"], (proof, "goal")), {}
    for s in p["steps"]:
        st = take(st, s["move"], s["args"], handles, (proof, s["id"]))
        if s["id"] == through:
            return st, handles
    raise ValueError(f"{proof} has no step {through!r}")


def keys_of(state):
    return frozenset(o.key for o in state.obligations())


# ---------------------------------------------------------------- comparisons

def compare_emitted(miss, proof, sid, expected, emitted, prev_keys):
    """One step's `last.emitted` against its expected list, as a set of keys
    (KEYING). `new` is computed here from the previous state's tracker, never
    taken from the kernel. The locations are PLANTED_BUGS' caught_by shapes:
    (proof, step, prop, dom) for an absent key, (proof, step, prop, what)
    for a key present with a wrong field."""
    got = {}
    for ob in emitted:
        if ob.key in got:
            miss(2, (proof, sid, "duplicate", T.show(ob.key)),
                 "listed twice in one step's emissions")
        got[ob.key] = ob
    want = set()
    for prop, dom, sources, status, tag, new in expected:
        k = key(prop, dom)
        want.add(k)
        ob = got.get(k)
        if ob is None:
            miss(2, (proof, sid, prop, dom), "not emitted")
            continue
        if frozenset(ob.sources) != frozenset(sources):
            miss(2, (proof, sid, prop, "sources"),
                 f"{sorted(ob.sources)}, expected {sorted(sources)}")
        if ob.status != status:
            miss(2, (proof, sid, prop, "status"),
                 f"{ob.status}, expected {status}")
        if tag_of(ob) != tag:
            miss(2, (proof, sid, prop, "tag"), f"{tag_of(ob)}, expected {tag}")
        reason = X.ADMISSION_REASON if status == X.ADMITTED else None
        if ob.status == status and ob.reason != reason:
            miss(2, (proof, sid, prop, "reason"),
                 f"{ob.reason!r}, expected {reason!r}")
        if (k not in prev_keys) != new:
            miss(2, (proof, sid, prop, "new"),
                 f"new is {k not in prev_keys}, expected {new}")
    for k, ob in got.items():
        if k not in want:
            miss(2, (proof, sid, "extra", T.show(k)),
                 f"{ob.status} {tag_of(ob)} from {sorted(ob.sources)}")


def tracker_problems(obs, expected, sources=None):
    """obligations() against a FINAL_TRACKER-shaped list of (prop, dom,
    status, tag). Returns (location suffix, detail) pairs. An absent key's
    suffix is ((prop, dom),), which is caught_by's FINAL_TRACKER shape.
    `sources`, when given, maps each key to the union of its expected
    sources over the steps (E8: add merges sources)."""
    out, got, want = [], {}, set()
    for ob in obs:
        if ob.key in got:
            out.append((("duplicate", T.show(ob.key)), "listed twice"))
        got[ob.key] = ob
    for prop, dom, status, tag in expected:
        k = key(prop, dom)
        want.add(k)
        ob = got.get(k)
        if ob is None:
            out.append((((prop, dom),), "absent"))
            continue
        if ob.status != status:
            out.append((((prop, dom), "status"), f"{ob.status}, expected {status}"))
        if tag_of(ob) != tag:
            out.append((((prop, dom), "tag"), f"{tag_of(ob)}, expected {tag}"))
        reason = X.ADMISSION_REASON if status == X.ADMITTED else None
        if ob.reason != reason:
            out.append((((prop, dom), "reason"), f"{ob.reason!r}"))
        if sources is not None and frozenset(ob.sources) != frozenset(sources[k]):
            out.append((((prop, dom), "sources"),
                        f"{sorted(ob.sources)}, expected {sorted(sources[k])}"))
    for k, ob in got.items():
        if k not in want:
            out.append((("extra", T.show(k)), f"{ob.status} {tag_of(ob)}"))
    return out


def expected_sources(proof):
    out = {}
    for obs in X.EXPECTED_OBLIGATIONS[proof].values():
        for prop, dom, sources, *_ in obs:
            out.setdefault(key(prop, dom), set()).update(sources)
    return out


def multiset_text(c, show_one):
    return ", ".join(f"{show_one(x)}" + (f" x{n}" if n > 1 else "")
                     for x, n in c.items())


def deriv_problems(F, trace, output):
    """deriv's trace (a multiset of (rule, subterm), and what each firing
    emitted), its output as a tree, and its emissions, against DERIV."""
    d = DERIV_BY_F[F]
    out = []

    def pair(x):
        return f"{x[0]} {T.show(x[1])}"

    want = Counter((r, term(s)) for r, s, _ in d["trace"])
    got = Counter((e.rule, e.subterm) for e in trace)
    if got != want:
        out.append(("trace", f"missing [{multiset_text(want - got, pair)}]; "
                    f"extra [{multiset_text(got - want, pair)}]"))
    want_e = Counter((r, term(s), frozenset(T.parse_judgement(j, SIG) for j in em))
                     for r, s, em in d["trace"])
    got_e = Counter((e.rule, e.subterm, frozenset(e.emits)) for e in trace)
    if got == want and got_e != want_e:
        def trip(x):
            return f"{pair(x)} emits {{{', '.join(map(T.show, x[2]))}}}"
        out.append(("trace_emits", f"expected [{multiset_text(want_e - got_e, trip)}]; "
                    f"got [{multiset_text(got_e - want_e, trip)}]"))
    if output != term(d["output"]):
        out.append(("output", f"got {show(output)}"))
    union = {k for e in trace for k in e.emits}
    want_u = {T.parse_judgement(j, SIG) for j in d["emits"]}
    if union != want_u:
        out.append(("deriv_emits", f"got {sorted(map(T.show, union))}"))
    return out


DERIV_BY_F = {d["F"]: d for d in X.DERIV.values()}


# ---------------------------------------------------------------- one proof run

class Run:
    """What one run of a proof found. `found` holds (item, where, detail)."""

    def __init__(self, name):
        self.name, self.found, self.lines = name, [], []
        self.state = None  # the last state reached
        self.n = None  # N, once the proof has closed

    def miss(self, item, where, detail):
        self.found.append((item, where, detail))


def run_proof(name, strict=True, out=print):
    """Install PROOFS[name], echo it, run its steps, and compare everything
    with p1_expected. `strict` adds what holds only of an unmutated run: the
    echo checks and no admission tagged none (the tag data's own rule).
    A Mismatch stops the run and is recorded. Any other exception is a
    kernel crash and propagates."""
    run = Run(name)
    try:
        _run_proof(run, strict, out)
    except Mismatch as m:
        run.miss(m.item, m.where, m.detail)
    return run


def _run_proof(run, strict, out):
    name, p = run.name, X.PROOFS[run.name]
    exp = X.EXPECTED_OBLIGATIONS[name]
    installed = goal(p["goal"])
    st = install(p["goal"], (name, "goal"))
    run.state = st
    # Done-when 6: the echo is printed from the installed tree, before s1.
    echo = T.show_goal(st.goal)
    run.lines.append(echo)
    out(echo)
    if strict:
        if run.lines[0] != X.ECHO[name]:
            run.miss(6, (name, "echo"), f"{run.lines[0]!r}, expected {X.ECHO[name]!r}")
        if T.parse_goal(echo, SIG) != st.goal:
            run.miss(6, (name, "echo", "reparse"), "does not parse back to the tree")
    if st.goal != installed or st.original != installed:
        run.miss(1, (name, "goal", "installed"), f"got {show(st.goal)}")
    if st.last.move != "install":
        run.miss(1, (name, "goal", "move"), f"last.move is {st.last.move!r}")
    compare_emitted(run.miss, name, "goal", exp["goal"], st.last.emitted,
                    frozenset())
    seen = list(st.last.emitted)
    handles = {}
    for s in p["steps"]:
        prev = st
        st = take(prev, s["move"], s["args"], handles, (name, s["id"]))
        run.state = st
        _check_step(run, s, prev, st)
        compare_emitted(run.miss, name, s["id"], exp[s["id"]], st.last.emitted,
                        keys_of(prev))
        seen += st.last.emitted
    obs = st.obligations()
    for suffix, detail in tracker_problems(obs, X.FINAL_TRACKER[name],
                                           expected_sources(name)):
        run.miss(2, ("FINAL_TRACKER", name) + suffix, detail)
    if strict:  # WHAT.md: an admission tagged none fails the milestone
        nones = {T.show(o.key) for o in seen + list(obs)
                 if o.status == X.ADMITTED and o.tag[0] == "none"}
        for k in sorted(nones):
            run.miss(2, ("NONE_TAG", name, k), "admitted and tagged none")
    if st.goal is not None:
        raise Mismatch(1, (name, "closed"), f"goal still open: {show(st.goal)}")
    run.n = sum(o.status == X.ADMITTED for o in obs)
    if run.n != X.ADMISSIONS[name]:
        run.miss(1, ("N", name), f"{run.n} admissions, expected {X.ADMISSIONS[name]}")
    verdict = K.report(st)
    if verdict != X.VERDICTS[name]:
        run.miss(1, ("VERDICT", name), f"{verdict!r}, expected {X.VERDICTS[name]!r}")
    if st.theorem != goal(p["theorem"]):
        run.miss(1, ("THEOREM", name), f"got {show(st.theorem)}")
    if T.instantiate(installed, term(X.ANSWERS[name])) != goal(p["theorem"]):
        run.miss(1, ("ANSWER", name), "ANSWERS disagrees with the theorem")


def _check_step(run, s, prev, st):
    where, last = (run.name, s["id"]), st.last
    if last.move != s["move"]:
        run.miss(1, where + ("move",), f"last.move is {last.move!r}")
    if st.lineage != prev.lineage or st.original != prev.original:
        run.miss(1, where + ("lineage",), "a step changed the lineage or original")
    want = None if s["goal_after"] is None else goal(s["goal_after"])
    if st.goal != want:
        run.miss(1, where + ("goal_after",), f"got {show(st.goal)}")
    if "occurrences" in s and last.occurrences != s["occurrences"]:
        run.miss(1, where + ("occurrences",),
                 f"{last.occurrences}, expected {s['occurrences']}")
    if s["move"] == "fact":
        h = last.handle
        if type(h) is not K.Handle:
            run.miss(1, where + ("handle",), f"last.handle is {type(h).__name__}")
        elif st.conclusion(h) != T.parse_judgement(s["conclusion"], SIG):
            run.miss(1, where + ("conclusion",), f"got {show(st.conclusion(h))}")
    if s["move"] == "ftc":
        for what, detail in deriv_problems(s["args"]["F"], last.trace, last.output):
            run.miss(2, where + (what,), detail)


# ---------------------------------------------------------------- the checks

class Suite:
    def __init__(self):
        self.rows = []  # (item, label, problems)

    def check(self, item, label, fn, needs_kernel=True):
        """Run fn(), which returns a list of problems; empty is a pass."""
        if needs_kernel and K is None:
            problems = [f"not run: the kernel did not import ({KERNEL_ERROR})"]
        else:
            try:
                problems = list(fn())
            except Mismatch as m:
                problems = [str(m)]
            except Exception as e:  # noqa: BLE001 -- a crash is a failure
                problems = ["crash: " + crash_text(e)]
        self.record(item, label, problems)

    def record(self, item, label, problems):
        self.rows.append((item, label, problems))
        print(f"  {'PASS' if not problems else 'FAIL'}  [{item}] {label}")
        for p in problems[:MAX_SHOWN]:
            print(f"          {p}")
        if len(problems) > MAX_SHOWN:
            print(f"          ... and {len(problems) - MAX_SHOWN} more")

    def failed(self):
        return [r for r in self.rows if r[2]]


def crash_text(e):
    tb = traceback.extract_tb(e.__traceback__)
    at = f" (at {os.path.basename(tb[-1].filename)}:{tb[-1].lineno} in " \
         f"{tb[-1].name})" if tb else ""
    return f"{type(e).__name__}: {e}{at}"


def equal_by(method, a, b, facts=()):
    """(True, "") when `method` proves a == b modulo facts, which are (lhs,
    rhs) Term pairs. The divisors a comparison owes are not tracked (E14)."""
    try:
        if method == "ring":
            FD.ring(a, b)
        else:
            FD.field(a, b, facts)
        return True, ""
    except FD.NotEqual:
        return False, ""
    except T.Refused as r:
        return False, f" (refused {r.code})"


def fact_pairs(state, handles, names):
    """The equations of the named handles, read through the public
    conclusion(); the script never sees how the kernel stores them."""
    out = []
    for n in names:
        j = state.conclusion(handles[n])
        out.append((j.lhs, j.rhs))
    return out


def entries_problems():
    """§6.8's pinned statements, entries.py against NAMED_ENTRIES."""
    out = []
    want = set(X.NAMED_ENTRIES) | set(X.ADDED_ENTRIES)
    if set(EN.ENTRIES) != want:
        out.append(f"entries are {sorted(EN.ENTRIES)}, expected {sorted(want)}")
    for name, e in X.NAMED_ENTRIES.items():
        got = EN.ENTRIES.get(name)
        if got is None:
            continue
        if got.statement != T.parse_judgement(e["statement"], SIG):
            out.append(f"{name}: statement {show(got.statement)}")
        if tuple(got.schema) != tuple(e["schema"]):
            out.append(f"{name}: schema {got.schema}")
        for side in ("lhs", "rhs"):
            if side in e and getattr(got.statement, side) != term(e[side]):
                out.append(f"{name}: {side} {show(getattr(got.statement, side))}")
        if tuple(got.hyps) != tuple(T.parse_judgement(h, SIG) for h in e["hyps"]):
            out.append(f"{name}: hyps {[show(h) for h in got.hyps]}")
    return out


def match_problems(case):
    """A MATCH_ACCEPTS case: installed fresh, one accepted rewrite."""
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(case["goal"], (case["id"], "goal"))
    compare_emitted(miss, case["id"], "goal", case["goal_emits"], st.last.emitted,
                    frozenset())
    move, args = case["move"]
    st2 = take(st, move, args, {}, (case["id"], move))
    if st2.goal != goal(case["goal_after"]):
        out.append(f"goal_after: got {show(st2.goal)}")
    compare_emitted(miss, case["id"], move, case["emits"], st2.last.emitted,
                    keys_of(st))
    return out


def occurrence_problems(which):
    c = X.OCCURRENCE_CASE[which]
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(X.OCCURRENCE_CASE["goal"], ("OCCURRENCE_CASE", "goal"))
    move, args = c["move"]
    st2 = take(st, move, args, {}, ("OCCURRENCE_CASE", which))
    if st2.last.occurrences != c["occurrences"]:
        out.append(f"occurrences {st2.last.occurrences}, expected {c['occurrences']}")
    if st2.goal != goal(c["goal_after"]):
        out.append(f"goal_after: got {show(st2.goal)}")
    compare_emitted(miss, "OCCURRENCE_CASE", which, c["emits"], st2.last.emitted,
                    keys_of(st))
    return out


def definedness_problems(case):
    """A DEFINEDNESS_CASES case (E26): installed fresh and closed with its
    move. Installation's and the close's lists, the final tracker, the
    report exactly and the theorem. No no-none assertion: two of these
    admissions are false and tagged none on purpose, and tan_zero_true's
    true one is tagged none by TAG_RULES as stated."""
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(case["goal"], (case["id"], "goal"))
    compare_emitted(miss, case["id"], "goal", case["goal_emits"], st.last.emitted,
                    frozenset())
    move, args = case["move"]
    st2 = take(st, move, args, {}, (case["id"], move))
    compare_emitted(miss, case["id"], move, case["emits"], st2.last.emitted,
                    keys_of(st))
    out += [fmt((case["id"], "final") + sfx, d)
            for sfx, d in tracker_problems(st2.obligations(), case["final"])]
    if st2.goal is not None:
        out.append(f"the goal is still open: {show(st2.goal)}")
    if K.report(st2) != case["report"]:
        out.append(f"report {K.report(st2)!r}, expected {case['report']!r}")
    if st2.theorem != goal(case["theorem"]):
        out.append(f"theorem {show(st2.theorem)}, expected {case['theorem']}")
    return out


def numeric_problems(name):
    """A math-module check that the answer is the integral: NUMERIC against
    the theorem's right side evaluated, and against Simpson's rule on the
    goal's integral. It shares no code with the kernel."""
    base = "P1.1" if name.startswith("P1.1") else "P1.2"
    want = X.NUMERIC[base]
    out = []
    answer = value(goal(X.PROOFS[name]["theorem"])[0].rhs)
    if abs(answer - want) > 1e-12 * max(1.0, abs(want)):
        out.append(f"the answer is {answer!r}, NUMERIC says {want!r}")
    integral = value(goal(X.PROOFS[name]["goal"])[0].lhs)
    if abs(integral - want) > 1e-4:
        out.append(f"Simpson gives {integral!r}, NUMERIC says {want!r}")
    return out


MATH = {"sin": math.sin, "cos": math.cos, "tan": math.tan, "asin": math.asin,
        "acos": math.acos, "atan": math.atan, "exp": math.exp, "ln": math.log,
        "sqrt": math.sqrt, "abs": abs, "sinh": math.sinh, "cosh": math.cosh,
        "tanh": math.tanh, "asinh": math.asinh, "acosh": math.acosh,
        "atanh": math.atanh}


def value(t, env=None):
    env = env or {}
    if isinstance(t, T.Num):
        return float(t.n)
    if isinstance(t, T.Const):
        return {"pi": math.pi, "e_const": math.e}[t.name]
    if isinstance(t, T.Var):
        return env[t.name]
    if isinstance(t, T.Neg):
        return -value(t.a, env)
    if isinstance(t, (T.Add, T.Mul, T.Div)):
        a, b = value(t.a, env), value(t.b, env)
        return a + b if isinstance(t, T.Add) else a * b if isinstance(t, T.Mul) else a / b
    if isinstance(t, T.Pow):
        return value(t.base, env) ** t.n
    if isinstance(t, T.RPow):
        return value(t.base, env) ** value(t.exp, env)
    if isinstance(t, T.App):
        return MATH[t.fn](value(t.arg, env))
    if isinstance(t, T.Integral):
        return simpson(lambda v: value(t.body, {**env, t.var: v}),
                       value(t.lo, env), value(t.hi, env))
    raise TypeError(f"no value for {t!r}")


def simpson(f, a, b, n=20000):
    h = (b - a) / n
    odd = sum(f(a + (2 * i - 1) * h) for i in range(1, n // 2 + 1))
    even = sum(f(a + 2 * i * h) for i in range(1, n // 2))
    return (f(a) + f(b) + 4 * odd + 2 * even) * h / 3


def w1_deriv_problems():
    """DERIV["W1"]: its ftc is refused, so deriv is run directly, on P1.1's
    open interval."""
    d = X.DERIV["W1"]
    dom = T.parse_judgement("t > 0 @ (0, pi/2)", SIG).dom
    got = DV.deriv(term(d["F"]), d["var"], dom)
    return [fmt(("W1", what), detail)
            for what, detail in deriv_problems(d["F"], got.trace, got.output)]


def wrong_answer_problems(w):
    st, handles = replay(*w["state"])
    before, before_goal = st.obligations(), st.goal
    move, args = w["move"]
    r = K.step(st, move, build_args(args, handles))
    if isinstance(r, K.ProofState):
        return ["accepted: the wrong answer went through"]
    out = []
    if r.code != w["refusal"]:
        out.append(f"refused {r.code}: {r.message}")
    if st.obligations() != before or st.goal != before_goal:
        out.append("the refused step changed the state (E13)")
    if r.residual is None:
        return out + ["the refusal carries no residual"]
    method, names = w["compare"]
    facts = fact_pairs(st, handles, names)
    for field_ in ("residual", "residual_factored"):
        if field_ in w:
            ok, note = equal_by(method, r.residual, term(w[field_]), facts)
            if not ok:
                out.append(f"residual {show(r.residual)} is not {field_} "
                           f"{w[field_]} under {method}{note}")
    zero, note = equal_by(method, r.residual, T.Num(0), facts)
    if zero or note:
        out.append(f"residual {show(r.residual)} is zero under {method}{note}")
    return out


# Refusals that no p1_expected case reaches: REFUSAL_CODES' own, and the
# kernel-local codes of ARCHITECTURE.md §6. Also one case for each clause of
# a rule that no p1_expected case exercises: REWRITE_RULE step 3's same head
# (both p1_expected mismatch cases keep the head and vary the argument, and
# without it sqrt_sq rewrites sin(x^2) to x), and its non-application
# clause (sqrt_sq_val's (sqrt a)^2 is the only equation entry whose left
# side is not an App; up to ring it would take sqrt 3 * sqrt 3), the
# occurrence range both ways, ring taking no facts, fact's exact schema,
# E23's exclusions p1_expected pins only for Integral, install's
# one-judgement rule, install's charge of the goal's own hypotheses (E6, E26),
# and ftc's closing check_goal, the only guard against a variable free in F
# that the goal's rhs binds. rewrite's closing check_goal is a backstop no
# move reaches since E26 (b), so it is tested through a seam instead
# (BACKSTOPS rewrite_closing_check_goal), as is ftc's against an Int in F
# (BACKSTOPS ftc_closing_check_goal_Int_in_F). A code
# p1_expected marks "unreachable in P1" still gets a case here when a plain
# move reaches it (range-same-infinity). close's oo refusal is trusted and
# runs before E23's untrusted whitelist: it is what stops a lax schema from
# admitting an improper integral whose convergence nothing charges. They
# are the suite's own cases, not p1_expected data: each code and its
# meaning is REFUSAL_CODES', GRAMMAR.md's or ARCHITECTURE.md's, and the
# only thing chosen here is a move that reaches it.
SUITE_BAD_MOVES = [
    {"id": "literal_hyp_false", "goal": "sqrt((-1)^2) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "-1"},
                          "at": "sqrt((-1)^2)"}),
     "refusal": "obligation-refuted"},  # E7: -1 >= 0 is literal and false
    {"id": "rewrite_target_absent", "goal": "sqrt(x^2) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "y"},
                          "at": "sqrt(y^2)"}),
     "refusal": "rewrite-target-not-found"},
    {"id": "rewrite_head_mismatch", "goal": "sin(x^2) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "x"},
                          "at": "sin(x^2)"}),
     "refusal": "rewrite-lhs-mismatch"},  # REWRITE_RULE 3: the same head h
    {"id": "rewrite_nonapp_tree_match", "goal": "sqrt 3 * sqrt 3 == ?A", "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq_val", "inst": {"a": "3"},
                          "at": "sqrt 3 * sqrt 3"}),
     "refusal": "rewrite-lhs-mismatch"},  # REWRITE_RULE 3: a non-App L matches as trees, not up to ring
    {"id": "occurrence_out_of_range", "goal": X.OCCURRENCE_CASE["goal"], "setup": [],
     "move": ("rewrite", {**X.OCCURRENCE_CASE["one"]["move"][1], "occurrence": 2}),
     "refusal": "rewrite-target-not-found"},  # REWRITE_RULE: k past the last one
    {"id": "occurrence_negative", "goal": X.OCCURRENCE_CASE["goal"], "setup": [],
     "move": ("rewrite", {**X.OCCURRENCE_CASE["one"]["move"][1], "occurrence": -2}),
     "refusal": "rewrite-target-not-found"},  # 0-based, so k < 0 is out of range; -2, since found[-1:0] is empty anyway
    {"id": "ring_with_facts", "goal": "1 + 1 == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "sqrt_sq_val", "inst": {"a": "3"}, "bind": "h"}}],
     "move": ("close", {"value": "2", "check": "ring", "facts": [("handle", "h")]}),
     "refusal": "bad-args"},  # ARCHITECTURE.md §4: ring takes no facts
    {"id": "fact_inst_missing", "goal": "(sqrt 3)^2 == ?A", "setup": [],
     "move": ("fact", {"entry": "sqrt_sq_val", "inst": {}, "bind": "h"}),
     "refusal": "bad-args"},  # E10: exactly the schema's variables
    {"id": "fact_inst_extra", "goal": "(sqrt 3)^2 == ?A", "setup": [],
     "move": ("fact", {"entry": "sqrt_sq_val", "inst": {"a": "3", "b": "1"},
                       "bind": "h"}),
     "refusal": "bad-args"},
    {"id": "ftc_not_integral", "goal": "x == ?A", "setup": [],
     "move": ("ftc", {"F": "x", "check": "ring", "facts": []}),
     "refusal": "ftc-no-integral"},  # a crash (AttributeError) without it, E21
    {"id": "close_value_is_goal_lhs", "goal": "D[x] x^2 == ?A", "setup": [],
     "move": ("close", {"value": "D[x] x^2", "check": "ring", "facts": []}),
     "refusal": "close-schema-not-closed"},  # E23: D is off the whitelist
    {"id": "bad_move_name", "goal": "x == ?A", "setup": [],
     "move": ("simp", {}), "refusal": "bad-move"},
    {"id": "range_same_infinity", "goal": "Int[x = oo .. oo] 1 == ?A", "setup": [],
     "move": ("install", {}), "refusal": "range-same-infinity"},  # E4: empty range
    {"id": "range_same_neg_infinity", "goal": "Int[x = -oo .. -oo] 1 == ?A",
     "setup": [], "move": ("install", {}), "refusal": "range-same-infinity"},
    {"id": "goal_not_equation", "goal": "x > 0", "setup": [],
     "move": ("install", {}), "refusal": "goal-shape"},
    {"id": "goal_two_judgements", "goal": "1 + 1 == ?A /\\ 0 == 1", "setup": [],
     "move": ("install", {}), "refusal": "goal-shape"},  # moves act on goal[0] only; a 2nd judgement would enter the theorem unproved
    {"id": "close_value_mentions_oo", "goal": "Int[x=0..1] x == ?A", "setup": [],
     "move": ("close", {"value": "Int[t=0..oo] exp(-t)", "check": "ring", "facts": []}),
     "refusal": "bad-args"},  # ARCHITECTURE.md §4: refused before E23's untrusted whitelist
    # rewrite_inst_shadows carries an Int into the goal through an inst
    # value, which only rewrite's closing check_goal used to refuse
    # (shadowing). Since E26 (b) it lies in L's argument, which step 3's
    # ring_nf refuses first, so the case pins that earlier refusal, and the
    # closing check is reached through a seam (BACKSTOPS). ftc's closing
    # check_goal is live: ftc_F_binder_free_in_rhs reaches it through a
    # variable free in F that the goal's rhs binds. An Int inside F is
    # refused earlier, by deriv (E12's d_const guard when x-free), which
    # ftc_F_holds_Int_binder pins. check_goal's own guards are still asserted
    # directly (DIRECT_REFUSALS).
    {"id": "rewrite_inst_shadows", "goal": "Int[t = 0 .. 1] atan(-y) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "atan_odd",
                          "inst": {"u": "y + ((Int[t = 0 .. 1] t) - (Int[t = 0 .. 1] t))"},
                          "at": "atan(-y)"}),
     "refusal": "Int-or-D-not-normalisable"},  # REWRITE_RULE step 3, E26 (b)
    {"id": "ftc_F_binder_free_in_rhs",
     "goal": "Int[x = 0 .. 1] 2*x == (Int[y = 0 .. 1] y) - (Int[y = 0 .. 1] y) + 1",
     "setup": [],
     "move": ("ftc", {"F": "x^2 + y - y", "check": "ring", "facts": []}),
     "refusal": "D11-bound-and-free"},  # ftc's closing check_goal: y is free in F(b) - F(a) and bound in the rhs
    {"id": "ftc_F_holds_Int_binder", "goal": "Int[x = 0 .. 1] 2*x == y - y + 1",
     "setup": [],
     "move": ("ftc", {"F": "x^2 + (Int[y = 0 .. 1] y) - (Int[y = 0 .. 1] y)",
                      "check": "ring", "facts": []}),
     "refusal": "Int-or-D-not-normalisable"},  # E12's d_const guard, E26 (b)
    # The goal's own hypotheses (E6, E26): each is charged at the hypotheses
    # before it, and one holding an Int or D node presupposes that value
    # exists. Each of these closed as a plain 'Proved.' (or ftc's Regs were
    # admitted carrying the Int) before install charged the domain.
    {"id": "goal_hyp_former_refuted", "goal": "1 == ?A @ ln(-1) > 0", "setup": [],
     "move": ("install", {}), "refusal": "obligation-refuted"},  # E26 (a): ln(-1) owes -1 > 0, false (E7)
    {"id": "goal_hyp_holds_Int", "goal": "1 == ?A @ (Int[t = 0 .. oo] 1) > 0",
     "setup": [], "move": ("install", {}),
     "refusal": "Int-or-D-not-normalisable"},  # E26 (b): a divergent Int as a hypothesis
    {"id": "goal_hyp_holds_D", "goal": "x == ?A @ D[x] abs x > 0", "setup": [],
     "move": ("install", {}), "refusal": "Int-or-D-not-normalisable"},  # E26 (b)
    {"id": "goal_hyp_holds_Int_before_ftc",
     "goal": "Int[x = 0 .. 1] 1 == ?A @ (Int[t = 0 .. oo] 1) > 0", "setup": [],
     "move": ("install", {}),
     "refusal": "Int-or-D-not-normalisable"},  # E26 (b): ftc's Regs would carry it, admitted
    # E7's domain half with nothing in front of it: ln x (or 1/x) owes its
    # former over [(Int[t = 0 .. 1] 1), oo). Its proposition holds no Int,
    # the range's infinite end means no orientation is owed (E4), and no goal
    # hypothesis carries the Int, so install's hypothesis gate never sees it.
    # A norm_num that checks only the proposition installs both, admitting
    # the former over a range whose end presupposes an Int exists.
    {"id": "norm_num_refuses_Int_in_range_domain",
     "goal": "Int[x = (Int[t = 0 .. 1] 1) .. oo] ln x == ?A", "setup": [],
     "move": ("install", {}), "refusal": "Int-or-D-not-normalisable"},  # E7, E26 (b)
    {"id": "norm_num_refuses_Int_in_range_domain_div",
     "goal": "Int[x = (Int[t = 0 .. 1] 1) .. oo] 1/x == ?A", "setup": [],
     "move": ("install", {}), "refusal": "Int-or-D-not-normalisable"},  # E7, E26 (b)
    # A fact's inst values enter the proof when the fact is used (E10, E6,
    # E26 (a)): the step that uses it charges their formers at its own
    # domain. Each of these closed as 'Proved.', or with the fact_hyp
    # admission 2 + 0*ln(-1) >= 0 tagged linear, while only the goal, R,
    # F and close's value were charged: ring cancels the undefined part, so
    # the fact still matches the goal's atom.
    {"id": "fact_inst_ln_refuted_at_close", "goal": "atan(-3) == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "atan_odd", "inst": {"u": "3 + 0*ln(-1)"}, "bind": "h"}}],
     "move": ("close", {"value": "-atan(3)", "check": "field", "facts": [("handle", "h")]}),
     "refusal": "obligation-refuted"},  # ln(-1) owes -1 > 0, false (E7)
    {"id": "fact_inst_ln_refuted_with_hyp", "goal": "(sqrt 2)^2 == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "sqrt_sq_val", "inst": {"a": "2 + 0*ln(-1)"}, "bind": "h"}}],
     "move": ("close", {"value": "2", "check": "field", "facts": [("handle", "h")]}),
     "refusal": "obligation-refuted"},  # not the admission 2 + 0*ln(-1) >= 0 alone
    {"id": "fact_inst_sqrt_refuted_at_close", "goal": "sqrt 4 == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "sqrt_sq", "inst": {"u": "2 + 0*sqrt(-1)"}, "bind": "h"}}],
     "move": ("close", {"value": "2", "check": "field", "facts": [("handle", "h")]}),
     "refusal": "obligation-refuted"},  # sqrt(-1) owes -1 >= 0, false (E7)
    {"id": "fact_inst_ln_refuted_at_ftc", "goal": "Int[x=1..4] 1/(2*sqrt x) == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "sqrt_sq_val", "inst": {"a": "x + 0*ln(-1)"}, "bind": "h"}}],
     "move": ("ftc", {"F": "sqrt x", "check": "field", "facts": [("handle", "h")]}),
     "refusal": "obligation-refuted"},  # ftc's check charges it too, on (1, 4)
    # REWRITE_RULE step 9 (b) read with step 10's charges, as (a) is: H is
    # empty, but R's sqrt t (ln t) owes t >= 0 (t > 0) on the closed
    # [1, x] through the x-dependent range below D[x]. The proposition does
    # not mention x, so (a) passes; (b) must refuse. Accepted while (b) ran
    # only on a non-empty H.
    {"id": "rewrite_under_D_through_Int_R_former",
     "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "t + (sqrt t - sqrt t)"},
                          "at": "atan(-t)"}),
     "refusal": "rewrite-under-D-needs-open-domain"},
    {"id": "rewrite_under_D_through_Int_R_former_ln",
     "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "t + (ln t - ln t)"},
                          "at": "atan(-t)"}),
     "refusal": "rewrite-under-D-needs-open-domain"},
    {"id": "close_without_mvar", "goal": "x == x", "setup": [],
     "move": ("close", {"value": "x", "check": "ring", "facts": []}),
     "refusal": "close-no-mvar"},
    {"id": "field_fact_not_equation", "goal": "pi == ?A",
     "setup": [{"id": "h", "move": "fact",
                "args": {"entry": "pi_pos", "inst": {}, "bind": "h"}}],
     "move": ("close", {"value": "pi", "check": "field", "facts": [("handle", "h")]}),
     "refusal": "field-fact-shape"},  # ARCHITECTURE.md §6: pi > 0 is no a^k == r
]

# ARCHITECTURE.md §6's kernel-local codes, each of which some case must name
# (SUITE_BAD_MOVES, or DIRECT_CODES' check for the two no move data reaches).
KERNEL_LOCAL_CODES = ("state-not-minted", "proof-finished", "bad-move", "bad-args",
                      "goal-shape", "ftc-no-integral", "close-no-mvar",
                      "field-fact-shape")
DIRECT_CODES = ("state-not-minted", "proof-finished")  # unminted_finished_problems


# GRAMMAR.md §1's table: every parse code, each of which some case must name.
GRAMMAR_CODES = (
    "D1-decimal", "implicit-mul", "non-ascii", "D2-deferred", "D3-bare-e",
    "reserved-hint", "D4-not-a-name", "D5-undeclared", "D5-arity",
    "D5-uncalled", "D5-sig-collision", "D5-sig-arity0",
    "D6-ambiguous-app-power", "D6-neg-operand", "D6-app-as-base",
    "D7-int-in-arith", "D8-pow-chain", "D8-neg-exponent", "bound-in-endpoint",
    "shadowing", "D11-bound-and-free", "D13-unnamed-interval", "oo-misplaced",
    "chained-cmp", "hash-nonzero", "mvar-misplaced", "syntax")


def refusal_coverage_problems():
    """Each case asserts its own code, so a code that no case names is a
    refusal path nothing exercises. p1_expected's "unreachable in P1" notes
    are true of P1's proofs, not of the kernel: every REFUSAL_CODES code
    needs a case too, from DIRECT_REFUSALS when no move reaches it."""
    named = {c["refusal"] for c in X.BAD_MOVES + X.WRONG_ANSWERS + SUITE_BAD_MOVES}
    named |= {a.split(":", 1)[1] for f in X.FORGERIES for a in f["accept"]
              if a.startswith("refusal:")}
    named |= set(DIRECT_CODES) | {"syntax"}  # HOSTILE_TREES
    named |= {c for _, _, c in DIRECT_REFUSALS}
    named |= {r[-1] for r in X.PARSE_REFUSALS + X.PARSE_REFUSALS_JUDGEMENT}
    named |= {r[-1] for rows in SUITE_PARSE_REFUSALS.values() for r in rows}
    return [f"{c}: no case asserts it" for c in X.REFUSAL_CODES
            if c not in named] + [
        f"{c} (kernel-local): no case asserts it" for c in KERNEL_LOCAL_CODES
        if c not in named] + [
        f"{c} (GRAMMAR.md §1): no case asserts it" for c in GRAMMAR_CODES
        if c not in named]


def unminted_finished_problems():
    """DIRECT_CODES: a state the kernel did not make, and a step on a closed
    proof, refused without raising (ARCHITECTURE.md §4's first two checks)."""
    out = []
    r = K.step(object(), "close", {"value": T.Num(2), "check": "ring", "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "state-not-minted"):
        out.append(f"a bare object as the state: {describe(r)}")
    st = K.step(install("1 + 1 == ?A", ("finished", "goal")), "close",
                {"value": T.Num(2), "check": "ring", "facts": []})
    r = K.step(st, "close", {"value": T.Num(2), "check": "ring", "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "proof-finished"):
        out.append(f"a step after close: {describe(r)}")
    return out


def bad_move_problems(b):
    move, args = b["move"]
    if move == "install":
        try:
            g = goal(b["goal"])
        except T.ParseError as e:  # parse_goal is part of installing
            return [] if e.code == b["refusal"] else [f"parse refused {e.code}"]
        r = K.install(g)
        if isinstance(r, K.ProofState):
            return ["installed"]
        return [] if r.code == b["refusal"] else [f"refused {r.code}: {r.message}"]
    out = []
    if "state" in b:
        st, handles = replay(*b["state"])
        if st.original != goal(b["goal"]):
            out.append("the state's original goal is not the entry's goal")
    else:
        st, handles = install(b["goal"], (b["id"], "goal")), {}
        for s in b["setup"]:
            st = take(st, s["move"], s["args"], handles, (b["id"], s["id"]))
    before, before_goal = st.obligations(), st.goal
    r = K.step(st, move, build_args(args, handles))
    if isinstance(r, K.ProofState):
        return out + ["accepted"]
    if r.code != b["refusal"]:
        out.append(f"refused {r.code}: {r.message}")
    if st.obligations() != before or st.goal != before_goal:
        out.append("the refused step changed the state (E13)")
    return out


# ---------------------------------------------------------------- forgeries
#
# E21. A fact-slot case passes at FORGERY_STATE with FORGERY_MOVE, only by
# raising while the forged object is built (where 'accept' lists
# raise_at_forge) or by step() returning the case's refusal. An exception
# out of step() is a crash. After every case the slot's tracker must still
# be TRACKER_AT_FORGERY_STATE, and the genuine h_sqrt3 must still close it.

class Slot:
    def __init__(self):
        self.state, self.handles = replay(*X.FORGERY_STATE)
        self.h = self.handles["h_sqrt3"]
        self.w4 = term(next(w["residual"] for w in X.WRONG_ANSWERS
                            if w["id"] == "W4"))

    def attempt(self, obj, state=None):
        """Pass obj at the slot: (outcome, what step returned)."""
        move, args = X.FORGERY_MOVE
        try:
            r = K.step(state or self.state, move, build_args(args, self.handles, obj))
        except Exception as e:  # noqa: BLE001 -- E21: a crash, not a refusal
            return "raised", crash_text(e)
        if isinstance(r, K.ProofState):
            return "accepted", r
        if (r.code == "close-check-failed" and r.residual is not None
                and equal_by("field", r.residual, self.w4)[0]):
            return "ignored", r
        return "refusal:" + r.code, r

    def post(self):
        out = [fmt(("TRACKER_AT_FORGERY_STATE",) + sfx, d) for sfx, d in
               tracker_problems(self.state.obligations(), X.TRACKER_AT_FORGERY_STATE)]
        outcome, r = self.attempt(self.h)
        if outcome != "accepted":
            out.append(f"the genuine h_sqrt3 no longer closes the slot: {outcome}")
        elif K.report(r) != X.VERDICTS["P1.2-alt"]:
            out.append(f"after the genuine close the report is {K.report(r)!r}")
        return out


def at_slot(slot, label, build, state=None):
    try:
        obj = build()
    except Exception as e:  # noqa: BLE001 -- building the forgery raised
        return label, "raise_at_forge", crash_text(e)
    outcome, r = slot.attempt(obj, state)
    return label, outcome, r if isinstance(r, str) else describe(r)


def forge_construct(slot, case):
    h, concl = slot.h, T.parse_judgement("(sqrt 3)^2 == 3", SIG)
    builds = [("Handle(id, lineage) built directly", lambda: K.Handle(h.id, h.lineage)),
              ("the Judgement (sqrt 3)^2 == 3 itself", lambda: concl)]
    minted = getattr(K, "_Minted", None)  # the kernel's private record
    if minted is not None:
        builds.append(("the private _Minted record",
                       lambda: minted(h, h.lineage, concl, "sqrt_sq_val")))
    return [at_slot(slot, label, b) for label, b in builds], slot.post()


def forge_object_new(slot, case):
    h = slot.h

    def build():
        obj = object.__new__(type(h))
        names = ([f.name for f in dataclasses.fields(h)] if dataclasses.is_dataclass(h)
                 else list(vars(h)))
        for n in names:
            object.__setattr__(obj, n, getattr(h, n))
        return obj
    return [at_slot(slot, "object.__new__ with h_sqrt3's fields", build)], slot.post()


def forge_copy(slot, case):
    return [at_slot(slot, "copy.copy(h_sqrt3)", lambda: copy.copy(slot.h)),
            at_slot(slot, "copy.deepcopy(h_sqrt3)", lambda: copy.deepcopy(slot.h))], \
        slot.post()


def forge_pickle(slot, case):
    return [at_slot(slot, "pickle round trip of h_sqrt3",
                    lambda: pickle.loads(pickle.dumps(slot.h)))], slot.post()


def forge_fabricated_id(slot, case):
    post = []
    st2 = K.step(slot.state, "fact", build_args(
        {"entry": "sqrt_sq_val", "inst": {"a": "3"}, "bind": "h_victim"}, {}))
    if not isinstance(st2, K.ProofState):
        return [("(a) fact sqrt_sq_val 3", "refused", describe(st2))], slot.post()
    post += [fmt(("after fact h_victim",) + sfx, d) for sfx, d in
             tracker_problems(st2.obligations(), X.TRACKER_AT_FORGERY_STATE)]
    victim = st2.last.handle
    new_id = victim.id + 1

    def alter():
        try:
            victim.id = new_id
        except Exception:  # noqa: BLE001 -- frozen: go round it, as the case says
            object.__setattr__(victim, "id", new_id)
        return victim
    attempts = [at_slot(slot, "(a) h_victim with its id changed to id + 1", alter, st2),
                at_slot(slot, "(b) that id as a bare int", lambda: new_id, st2),
                at_slot(slot, "(c) h_sqrt3.id as a bare int", lambda: slot.h.id)]
    return attempts, post + slot.post()


def forge_foreign(slot, case):
    _, other = replay("P1.2", "s1")

    def relabel():  # E17: the lineage compared is the kernel's record, not the handle's field
        h = other["h_sqrt3"]  # the second run's handle, so slot.h is untouched
        object.__setattr__(h, "lineage", slot.state.lineage)
        return h
    # The plain attempt first: the second one alters the same object.
    return [at_slot(slot, "h_sqrt3 minted in a second P1.2 run", lambda: other["h_sqrt3"]),
            at_slot(slot, "that handle with its lineage field set to the slot's",
                    relabel)], slot.post()


def tracker_write(st):
    """Public API only: delete t >= 0 @ [0, pi/2] from what obligations()
    returns, and mark 0 <= pi/2 discharged, by attribute and then through
    vars(), which looks like a copy but is the record's own dict when it has
    one. Returns what raised."""
    raised = []
    obs = st.obligations()
    try:
        del obs[next(i for i, o in enumerate(obs) if o.key == key("t >= 0", "[0, pi/2]"))]
    except Exception as e:  # noqa: BLE001
        raised.append(("delete", crash_text(e)))
    target = next(o for o in obs if o.key == key("0 <= pi/2", "true"))
    try:
        target.status = X.DISCHARGED
    except Exception as e:  # noqa: BLE001
        raised.append(("mark discharged", crash_text(e)))
    try:
        vars(target)["status"] = X.DISCHARGED
    except Exception as e:  # noqa: BLE001
        raised.append(("mark discharged through vars()", crash_text(e)))
    return raised


def p1_1_post(st):
    out = [fmt(("FINAL_TRACKER", "P1.1") + sfx, d) for sfx, d in
           tracker_problems(st.obligations(), X.FINAL_TRACKER["P1.1"])]
    if K.report(st) != X.VERDICTS["P1.1"]:
        out.append(f"the report is {K.report(st)!r}")
    return out


def forge_tracker_write(case):
    st = replay(*case["state"])[0]
    raised = tracker_write(st)
    outcome = "raise_at_mutation" if raised else "no_effect"
    detail = "; ".join(f"{op} raised {e}" for op, e in raised) or "both completed"
    return [("delete an admission and mark one discharged", outcome, detail)], p1_1_post(st)


def report_attempt(label, build, reports):
    try:
        obj = build()
    except Exception as e:  # noqa: BLE001
        return label, "raise_at_forge", crash_text(e)
    try:
        text = K.report(obj)
    except (TypeError, ValueError) as e:
        return label, "raise_at_call", crash_text(e)
    except Exception as e:  # noqa: BLE001 -- not a clean refusal to print
        return label, "crash", crash_text(e)
    reports.append(text)
    return label, "returned", repr(text)


def forge_print_proved(case):
    st = replay(*case["state"])[0]
    reports, attempts, captured = [], [], io.StringIO()
    with contextlib.redirect_stdout(captured):
        # (a) a report or state object built from outside, handed to report
        for label, build in (
                ("(a) ProofState(...) without the kernel's token",
                 lambda: K.ProofState(object(), None, st.original, st.lineage,
                                      None, st.last, st.theorem)),
                ("(a) object.__new__(ProofState)", lambda: object.__new__(K.ProofState)),
                ("(a) the string 'Proved.'", lambda: "Proved."),
                ("(a) VERDICT with n = 0", lambda: K.VERDICT.format(n=0))):
            attempts.append(report_attempt(label, build, reports))
        # (b) a caller-supplied count or status
        params = list(inspect.signature(K.report).parameters)
        if len(params) == 1:
            attempts.append(("(b) report's parameters", "no_such_parameter", str(params)))
        for extra in ((0,), ("Proved.",)):
            try:
                text = K.report(st, *extra)
            except (TypeError, ValueError) as e:
                attempts.append((f"(b) report(st, {extra[0]!r})", "raise_at_call",
                                 crash_text(e)))
            else:
                reports.append(text)
                attempts.append((f"(b) report(st, {extra[0]!r})", "returned", repr(text)))
        # (c) the report again, after the direct_tracker_write attempt. The
        # kernel declining the forged change is recorded as 'refused'.
        tracker_write(st)
        text = K.report(st)
        reports.append(text)
        attempts.append(("(c) report after a tracker write",
                         "refused" if text == X.VERDICTS["P1.1"] else "returned",
                         repr(text)))
        # (d) a script-side tactic's result object claiming the goal closed
        fake = types.SimpleNamespace(goal=None, theorem=st.theorem, closed=True,
                                     verdict="Proved.", obligations=lambda: ())
        attempts.append(report_attempt("(d) report of a tactic's result object",
                                       lambda: fake, reports))
        try:
            r = K.step(fake, "close", build_args(
                {"value": "2", "check": "ring", "facts": []}, {}))
        except Exception as e:  # noqa: BLE001 -- E21: a crash
            attempts.append(("(d) step on the tactic's object", "crash", crash_text(e)))
        else:
            attempts.append(("(d) step on the tactic's object",
                             "refused" if isinstance(r, K.Refusal) else "accepted",
                             describe(r)))
        reports.append(K.report(st))
    post = [f"a report is {t!r}, not {X.VERDICTS['P1.1']!r}" for t in reports
            if t != X.VERDICTS["P1.1"]]
    post += [f"a report contains 'Proved.': {t!r}" for t in reports
             if "Proved." in str(t)]
    post += [f"{f.__name__}(state) contains 'Proved.'" for f in (str, repr)
             if "Proved." in f(st)]
    if "Proved." in captured.getvalue():
        post.append("'Proved.' was printed")
    return attempts, post + p1_1_post(st)


def public_names():
    names = list(getattr(K, "__all__", None) or
                 [n for n in dir(K) if not n.startswith("_")])
    return names, [n for n in dir(K.ProofState) if not n.startswith("_")]


def forge_json(slot, case):
    st = slot.state
    names, state_names = public_names()
    try:
        json.dumps(st)
        dump_raises = False
    except TypeError:
        dump_raises = True
    for n in names:  # the kernel's own serialiser, if it documents one
        if re.search(r"dump|serial|json|save|export|pickle", n, re.I):
            try:
                getattr(K, n)(st)
                dump_raises = False
            except TypeError:
                pass
    loaders = []
    callables = [(n, getattr(K, n)) for n in names] + \
        [("ProofState." + n, getattr(K.ProofState, n)) for n in state_names] + \
        [("state." + n, getattr(st, n)) for n in state_names]
    for n, fn in callables:
        if not callable(fn):
            continue
        for arg in ("{}", b"{}", {}):
            try:
                got = fn(arg)
            except Exception:  # noqa: BLE001 -- not a loader for this input
                continue
            if isinstance(got, K.ProofState):
                loaders.append(n)
    if dump_raises:
        outcome = "dump_raises"
    elif not loaders:
        outcome = "no_loader"
    else:  # the kernel documents no loader, so there is nothing to load with
        outcome = "loader:" + ",".join(sorted(set(loaders)))
    detail = f"json.dumps {'raised' if dump_raises else 'worked'}; loaders " \
             f"{sorted(set(loaders)) or 'none'} among {len(callables)} public names"
    post = [fmt(("TRACKER_AT_FORGERY_STATE",) + sfx, d) for sfx, d in
            tracker_problems(st.obligations(), X.TRACKER_AT_FORGERY_STATE)]
    return [("serialise the state and load it back", outcome, detail)], post


FORGERY_CODE = {  # E21: the cases are code, listed by name
    "construct_theorem_directly": forge_construct,
    "object_new_theorem": forge_object_new,
    "copy_handle": forge_copy,
    "pickle_roundtrip_handle": forge_pickle,
    "fabricated_handle_id": forge_fabricated_id,
    "foreign_state_handle": forge_foreign,
    "json_roundtrip_state": forge_json,
    "direct_tracker_write": forge_tracker_write,
    "print_proved_with_admissions": forge_print_proved,
}
AT_P1_1 = ("direct_tracker_write", "print_proved_with_admissions")


def forgery_problems(case):
    code = FORGERY_CODE.get(case["id"])
    if code is None:
        return ["the script has no code for this case"]
    attempts, post = code(case) if case["id"] in AT_P1_1 else code(Slot(), case)
    out = [f"{label}: {outcome} ({detail}), accepted outcomes {case['accept']}"
           for label, outcome, detail in attempts if outcome not in case["accept"]]
    return out + post


# ---------------------------------------------------------------- planted bugs
#
# ARCHITECTURE.md §7. The trusted code has no bug switch. Each bug is patched
# in through its seam, in a child process that runs nothing else, so the
# patch lives and dies with it. The parent never imports unittest.mock.

def reemitted_key():
    """tracker_drops_reemitted's key, read from its one caught_by entry: the
    prop named there, looked up in that proof's step list for its domain. It
    must match exactly one expected obligation there, re-emitted (new False),
    and the step before must have minted it (new True), or the mutation
    would not be the one the data describes."""
    (proof, sid, prop, flag), = X.PLANTED_BUGS["tracker_drops_reemitted"][
        "caught_by"]
    steps = X.EXPECTED_OBLIGATIONS[proof]
    hits = [ob for ob in steps[sid] if ob[0] == prop]
    assert flag == "new" and len(hits) == 1 and hits[0][5] is False, hits
    k = key(prop, hits[0][1])
    ids = list(steps)
    before = steps[ids[ids.index(sid) - 1]]
    assert [ob[5] for ob in before if key(ob[0], ob[1]) == k] == [True], before
    return k


def seam_patch(name, mock):
    """The child's patch for one PLANTED_BUGS key. Each seam is asserted to
    exist first: patch.dict would add a missing key without complaint.
    deriv.APP_RULES is read-only, so its whole mapping is swapped."""
    if name == "d_ln_emits_nothing":
        assert "ln" in DV.APP_RULES, "seam deriv.APP_RULES['ln'] is missing"
        orig = DV.APP_RULES["ln"]
        return mock.patch.object(DV, "APP_RULES", types.MappingProxyType(
            {**DV.APP_RULES, "ln": lambda u, du: (orig(u, du)[0], ())}))
    if name == "ftc_derivative_premise_on_closed":
        assert callable(getattr(K, "derivative_domain", None)), \
            "seam kernel.derivative_domain is missing"
        return mock.patch.object(K, "derivative_domain", lambda iv: iv)
    if name in ("tracker_drops_one", "tracker_drops_reemitted"):
        assert callable(getattr(getattr(K, "_Tracker", None), "add", None)), \
            "seam kernel._Tracker.add is missing"
        orig = K._Tracker.add
        if name == "tracker_drops_one":
            drop = {key(p, d) for p, d in X.PLANTED_BUGS[name]["drop_keys"]}
            first_only = False
        else:  # the key its catch names, dropped the first time only
            drop, first_only = {reemitted_key()}, True
        dropped = []

        def add(self, emission):
            if emission.key in drop and not (first_only and dropped):
                dropped.append(emission.key)
                return None
            return orig(self, emission)
        return mock.patch.object(K._Tracker, "add", add)
    if name == "pi_pos_not_in_constraint_set":
        assert "pi" in TG.SIGN_FACTS, "seam tagger.SIGN_FACTS['pi'] is missing"
        return mock.patch.dict(TG.SIGN_FACTS, clear=True)
    raise KeyError(f"no seam for planted bug {name!r}")


# The case tables a definedness mutation's caught_by can name, as
# ("BAD_MOVES", id) and the like: that case fails, by a refusal that no
# longer happens or by a list, tracker or report that differs.
CASE_TABLES = (("BAD_MOVES", "bad_move_problems"),
               ("DEFINEDNESS_CASES", "definedness_problems"),
               ("MATCH_ACCEPTS", "match_problems"))


def case_failures():
    """[table, id] for every case of CASE_TABLES that fails. A Mismatch (a
    refused setup step, say) is a failure of that case; anything else is a
    crash and propagates."""
    out = []
    for table, fn in CASE_TABLES:
        for c in getattr(X, table):
            try:
                problems = globals()[fn](c)
            except Mismatch as m:
                problems = [str(m)]
            if problems:
                out.append([table, c["id"]])
    return out


def child(name, kind="plant"):
    """Run every proof in PROOFS under one planted bug (kind "plant"), one
    definedness mutation (kind "mutate") or nothing (name None, the
    control), print one JSON object and exit 0. The mutation and control
    runs also run CASE_TABLES' cases. Any exception that is not a Mismatch
    exits 2."""
    if K is None:
        print(KERNEL_ERROR, file=sys.stderr)
        return 2
    try:
        if name is None:
            ctx = contextlib.nullcontext()
        else:
            from unittest import mock
            ctx = (seam_patch if kind == "plant" else mutation_patch)(name, mock)
        found, admissions, final = [], {}, {}
        with ctx:
            for p in X.PROOFS:
                run = run_proof(p, strict=False, out=lambda line: None)
                found += [where for _, where, _ in run.found]
                admissions[p] = run.n
                final[p] = None if run.n is None else [
                    [T.show(o.key), o.status, o.tag[0], list(o.tag[1])]
                    for o in run.state.obligations()]
            if kind != "plant":
                found += case_failures()
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions, "final": final}))
    return 0


def spawn(*flags):
    proc = subprocess.run([sys.executable, os.path.abspath(__file__), *flags],
                          capture_output=True, text=True, timeout=1800)
    if proc.returncode != 0:
        tail = (proc.stderr.strip().splitlines() or ["(no stderr)"])[-3:]
        return None, [f"child exited {proc.returncode}: " + " | ".join(tail)]
    data = json.loads(proc.stdout.strip().splitlines()[-1])
    if "mismatches" in data:  # a backstop child reports one result instead
        data["mismatches"] = {tuplify(m) for m in data["mismatches"]}
    return data, []


def final_rows(data, proof):
    rows = data["final"].get(proof) or []
    return {r[0]: (r[1], (r[2], tuple(r[3]))) for r in rows}


def planted_problems(name, bug):
    data, out = spawn("--plant", name)
    if data is None:
        return out
    found = data["mismatches"]
    out += [f"not caught at {c}" for c in map(tuplify, bug["caught_by"])
            if c not in found]
    if data["admissions"] != bug["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {bug['admissions']}")
    for proof, js in bug.get("missing", {}).items():
        rows = final_rows(data, proof)
        out += [f"{proof}: {j} is still in the final tracker" for j in js
                if T.show(T.parse_judgement(j, SIG)) in rows]
    for proof, pairs in bug.get("missing_from_final_tracker", {}).items():
        rows = final_rows(data, proof)
        out += [f"{proof}: {p} @ {d} is still in the final tracker" for p, d in pairs
                if T.show(key(p, d)) in rows]
    for proof, retags in bug.get("retagged", {}).items():
        rows = final_rows(data, proof)
        for p, d, tag in retags:
            got = rows.get(T.show(key(p, d)))
            if got is None or got[1] != tag:
                out.append(f"{proof}: {p} @ {d} is {got}, expected tag {tag}")
    if bug.get("step_lists_changed") is False:
        out += [f"a step list changed: {m}" for m in found if m[0] in X.PROOFS]
    for proof in bug.get("affects", ()):
        if not any(proof in m[:2] for m in found):
            out.append(f"{proof} is listed as affected and shows no mismatch")
    return out


def control_problems():
    """The child harness, unpatched, finds nothing, in the proofs or in the
    cases a definedness mutation can name: so what a planted or mutated run
    catches comes from its patch, not from the child."""
    data, out = spawn("--control")
    if data is None:
        return out
    out += [f"unpatched child found {m}" for m in sorted(data["mismatches"], key=str)]
    if data["admissions"] != X.ADMISSIONS:
        out.append(f"unpatched admissions {data['admissions']}")
    return out


def clean_after_problems():
    """The unmutated suite, run again in this process after the planted runs:
    nothing leaked, and unittest.mock was never imported here."""
    out = []
    for p in X.PROOFS:
        run = run_proof(p, out=lambda line: None)
        out += [f"{p}: {fmt(w, d)}" for _, w, d in run.found]
        if run.n != X.ADMISSIONS[p]:
            out.append(f"{p}: N = {run.n}")
    if "unittest.mock" in sys.modules:
        out.append("unittest.mock is imported in the unmutated process")
    return out


# ---------------------------------------------------------------- backstops
#
# A closing check_goal along a path that an earlier refusal stops first
# since E26 (b) (all of rewrite's; for ftc, an Int in F) is still the only
# guard left there if the earlier refusal ever weakens, and a bad move cannot tell
# whether it is there. Each case weakens that earlier refusal through its
# seam (ARCHITECTURE.md §7), in a child process as PLANTED_BUGS are, replays
# a SUITE_BAD_MOVES move, and asserts the closing check then refuses it.
# Deleting the check makes the case fail: the move is accepted, building a
# goal whose binder is also free (rewrite's inst Int shadowing the Int
# around the target; ftc's F bringing an Int whose binder the rhs has free).
BACKSTOPS = {
    "rewrite_closing_check_goal": {
        "case": "rewrite_inst_shadows", "seam": "field.ring_equal",  # REWRITE_RULE step 3, made lax
        "refusal": "shadowing"},
    "ftc_closing_check_goal_Int_in_F": {
        "case": "ftc_F_holds_Int_binder", "seam": "deriv.const_guard",  # E12's guard, off
        "refusal": "D11-bound-and-free"},
}


def backstop_patch(name, mock):
    """The child's patch for one BACKSTOPS case. The seam is asserted to
    exist first."""
    seam = BACKSTOPS[name]["seam"]
    if seam == "field.ring_equal":
        assert callable(getattr(FD, "ring_equal", None)), "seam field.ring_equal is missing"
        return mock.patch.object(FD, "ring_equal", lambda a, b: True)
    if seam == "deriv.const_guard":
        assert callable(getattr(DV, "const_guard", None)), "seam deriv.const_guard is missing"
        return mock.patch.object(DV, "const_guard", lambda t: None)
    raise KeyError(f"no seam for backstop {name!r}")


def backstop_child(name):
    """Replay one BACKSTOPS case's move under its patch and print
    {"result": the refusal code, or "accepted"}. A crash exits 2."""
    if K is None:
        print(KERNEL_ERROR, file=sys.stderr)
        return 2
    try:
        from unittest import mock
        b = {c["id"]: c for c in SUITE_BAD_MOVES}[BACKSTOPS[name]["case"]]
        move, args = b["move"]
        with backstop_patch(name, mock):
            st = install(b["goal"], (name, "goal"))
            r = K.step(st, move, build_args(args, {}))
        result = "accepted" if isinstance(r, K.ProofState) else r.code
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"result": result}))
    return 0


def backstop_problems(name, case):
    data, out = spawn("--backstop", name)
    if data is None:
        return out
    if data["result"] != case["refusal"]:
        out.append(f"{data['result']}, expected {case['refusal']}")
    return out


# ---------------------------------------------------------------- isolated seams
#
# E26 (b) is checked in two places that raise the same code: install's gate
# on the goal's hypotheses (field.hypothesis_tree) and E7's check of every
# obligation (field.norm_num_tree, proposition and domain). DEFINEDNESS_
# MUTATIONS' three norm_num names weaken both, so what catches them could
# be either. Each case here weakens one seam alone, in a child process, and
# replays suite and data bad moves: the move its seam is the only guard for
# must go through ("accepted"), and a move the other check still stops must
# keep its refusal. Deleting either check, or merging it into the other,
# fails one of them.
ISOLATED_SEAMS = {
    "norm_num_ignores_domain_only": {
        "seam": "field.norm_num_tree", "results": {
            "norm_num_refuses_Int_in_range_domain": "accepted",
            "norm_num_refuses_Int_in_range_domain_div": "accepted",
            "norm_num_refuses_Int_in_domain": "Int-or-D-not-normalisable",  # the gate
            "goal_hyp_holds_Int": "Int-or-D-not-normalisable"}},
    "install_admits_hypothesis_trees": {
        "seam": "field.hypothesis_tree", "results": {
            "goal_hyp_holds_Int": "accepted",
            "goal_hyp_holds_D": "accepted",
            "norm_num_refuses_Int_in_domain": "Int-or-D-not-normalisable",  # E7's domain check
            "norm_num_refuses_D_in_domain": "Int-or-D-not-normalisable",
            "norm_num_refuses_Int_in_range_domain": "Int-or-D-not-normalisable"}},
}


def isolated_patch(name, mock):
    """The child's patch for one ISOLATED_SEAMS case. The seam is asserted
    to exist first."""
    seam = ISOLATED_SEAMS[name]["seam"]
    if seam == "field.norm_num_tree":
        assert callable(getattr(FD, "norm_num_tree", None)), "seam field.norm_num_tree is missing"
        orig = FD.norm_num_tree
        return mock.patch.object(FD, "norm_num_tree", lambda node, in_domain: (
            None if in_domain else orig(node, in_domain)))
    if seam == "field.hypothesis_tree":
        assert callable(getattr(FD, "hypothesis_tree", None)), \
            "seam field.hypothesis_tree is missing"
        return mock.patch.object(FD, "hypothesis_tree", lambda node: None)
    raise KeyError(f"no seam for isolated case {name!r}")


def move_result(b):
    """A bad move's outcome: its refusal code, or "accepted"."""
    move, args = b["move"]
    if move == "install":
        r = K.install(goal(b["goal"]))
    else:
        st, handles = install(b["goal"], (b["id"], "goal")), {}
        for s in b["setup"]:
            st = take(st, s["move"], s["args"], handles, (b["id"], s["id"]))
        r = K.step(st, move, build_args(args, handles))
    return "accepted" if isinstance(r, K.ProofState) else r.code


def isolated_child(name):
    """Replay one ISOLATED_SEAMS case's moves under its patch and print
    {"results": {case id: outcome}}. A crash exits 2."""
    if K is None:
        print(KERNEL_ERROR, file=sys.stderr)
        return 2
    try:
        from unittest import mock
        cases = {c["id"]: c for c in [*SUITE_BAD_MOVES, *X.BAD_MOVES]}
        with isolated_patch(name, mock):
            results = {i: move_result(cases[i]) for i in ISOLATED_SEAMS[name]["results"]}
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"results": results}))
    return 0


def isolated_problems(name, case):
    data, out = spawn("--isolate", name)
    if data is None:
        return out
    return out + [f"{i}: {data['results'].get(i)}, expected {want}"
                  for i, want in case["results"].items() if data["results"].get(i) != want]


# ---------------------------------------------------------------- definedness mutations
#
# DEFINEDNESS_MUTATIONS, each patched into a child process through a seam of
# ARCHITECTURE.md §7, as PLANTED_BUGS are: kernel.NATURAL_DOMAINS for E26
# (a)'s table, field._Normaliser.tree and field.norm_num_tree for E26 (b),
# deriv.const_guard for E12's guard, and kernel._charge_formers and
# kernel._encloses for the three position mutations. Each patch is the
# mutation's own text, written here; the parent requires every caught_by
# location among the child's mismatches, and N where the data gives it.

def _row(*bounds):
    """A NATURAL_DOMAINS row, u -> (u op c, ...), from (op, c) pairs."""
    return lambda u: tuple(T.Rel(op, u, T.lit(c)) for op, c in bounds)


# name -> (builtin, the row put in its place; None removes the row)
TABLE_MUTATIONS = {
    "no_ln_former": ("ln", None), "no_sqrt_former": ("sqrt", None),
    "no_tan_former": ("tan", None), "no_asin_former": ("asin", None),
    "no_acos_former": ("acos", None), "no_acosh_former": ("acosh", None),
    "no_atanh_former": ("atanh", None),
    "asin_no_upper_bound": ("asin", _row((">=", -1))),
    "asin_no_lower_bound": ("asin", _row(("<=", 1))),
    "acos_no_upper_bound": ("acos", _row((">=", -1))),
    "acos_no_lower_bound": ("acos", _row(("<=", 1))),
    "atanh_no_upper_bound": ("atanh", _row((">", -1))),
    "atanh_no_lower_bound": ("atanh", _row(("<", 1))),
    "ln_closed_at_0": ("ln", _row((">=", 0))),
    "sqrt_open_at_0": ("sqrt", _row((">", 0))),
    "asin_open": ("asin", _row((">", -1), ("<", 1))),
    "acos_open": ("acos", _row((">", -1), ("<", 1))),
    "acosh_open_at_1": ("acosh", _row((">", 1))),
    "atanh_closed": ("atanh", _row((">=", -1), ("<=", 1))),
}
# name -> (the normaliser it reads the node in: field's or ring's, the node)
ATOM_MUTATIONS = {
    "ring_reads_Int_as_atom": (False, "Integral"),
    "ring_reads_D_as_atom": (False, "Deriv"),
    "field_reads_Int_as_atom": (True, "Integral"),
    "field_reads_D_as_atom": (True, "Deriv"),
}
# name -> which (node, in_domain) E7's refusal lets through
NORM_NUM_MUTATIONS = {
    "norm_num_admits_Int": lambda node, in_domain: type(node) is T.Integral,
    "norm_num_admits_D": lambda node, in_domain: type(node) is T.Deriv,
    "norm_num_ignores_domain": lambda node, in_domain: in_domain,
}


def mutation_patch(name, mock):
    """The child's patch for one DEFINEDNESS_MUTATIONS key. Each seam is
    asserted to exist first."""
    if name in TABLE_MUTATIONS:
        fn, row = TABLE_MUTATIONS[name]
        assert fn in K.NATURAL_DOMAINS, f"seam kernel.NATURAL_DOMAINS[{fn!r}] is missing"
        table = dict(K.NATURAL_DOMAINS)
        if row is None:
            del table[fn]
        else:
            table[fn] = row
        return mock.patch.object(K, "NATURAL_DOMAINS", types.MappingProxyType(table))
    if name in ATOM_MUTATIONS:
        is_field, node = ATOM_MUTATIONS[name]
        assert callable(getattr(FD._Normaliser, "tree", None)), \
            "seam field._Normaliser.tree is missing"
        orig = FD._Normaliser.tree

        def tree(self, t):  # the spike's reading: an atom keyed by the tree
            if self.is_field is is_field and type(t).__name__ == node:
                return self.atom(("tree", t), t)
            return orig(self, t)
        return mock.patch.object(FD._Normaliser, "tree", tree)
    if name in NORM_NUM_MUTATIONS:
        # The data's caught_by for these three names install cases that
        # install's hypothesis gate refuses before E7 runs, so the patch
        # weakens the gate the same way (a hypothesis is read as a domain,
        # in_domain=True). ISOLATED_SEAMS weakens each seam alone.
        for seam in ("norm_num_tree", "hypothesis_tree"):
            assert callable(getattr(FD, seam, None)), f"seam field.{seam} is missing"
        orig, hyp, skip = FD.norm_num_tree, FD.hypothesis_tree, NORM_NUM_MUTATIONS[name]
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(FD, "norm_num_tree", lambda node, in_domain: (
            None if skip(node, in_domain) else orig(node, in_domain))))
        stack.enter_context(mock.patch.object(FD, "hypothesis_tree", lambda node: (
            None if skip(node, True) else hyp(node))))
        return stack
    if name == "deriv_d_const_on_Int_or_D":
        assert callable(getattr(DV, "const_guard", None)), "seam deriv.const_guard is missing"
        return mock.patch.object(DV, "const_guard", lambda t: None)
    if name in ("rewrite_R_former_at_goal_domain", "rewrite_R_former_on_ranges_only"):
        assert callable(getattr(K, "_charge_formers", None)), \
            "seam kernel._charge_formers is missing"
        orig, at_goal = K._charge_formers, name.endswith("goal_domain")

        def charge(buf, term_, dom, goal_dom, anc=None):
            if anc is None:  # not rewrite's R: every other caller omits anc
                return orig(buf, term_, dom, goal_dom)
            if at_goal:
                return orig(buf, term_, goal_dom, goal_dom)
            return orig(buf, term_, dom[len(goal_dom):], goal_dom, anc=anc)
        return mock.patch.object(K, "_charge_formers", charge)
    if name == "limit_former_on_own_range":
        assert callable(getattr(K, "_encloses", None)), "seam kernel._encloses is missing"
        return mock.patch.object(K, "_encloses", lambda slot: True)
    raise KeyError(f"no seam for definedness mutation {name!r}")


def mutation_results():
    """Every DEFINEDNESS_MUTATIONS child, run a few at a time: name ->
    (data, problems), as spawn returns them."""
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=max(2, min(8, os.cpu_count() or 2))) as ex:
        futures = {n: ex.submit(spawn, "--mutate", n) for n in X.DEFINEDNESS_MUTATIONS}
    return {n: f.result() for n, f in futures.items()}


def mutation_problems(mutation, result):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    out += [f"not caught at {c}" for c in map(tuplify, mutation["caught_by"])
            if c not in found]
    if "admissions" in mutation and data["admissions"] != mutation["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {mutation['admissions']}")
    return out


# ---------------------------------------------------------------- beyond P1's data
#
# The suite's own cases, for rules P1's data cannot see: a rule every P1 term
# happens to mask, a refusal path no P1 case takes, and the review's
# soundness and trust findings, each pinned so it stays caught. None of them
# is p1_expected data, and none borrows its "(added)" label. Each expected
# value is read off DESIGN.md or p1_expected's decisions (cited per case),
# and was confirmed to fail on the mutation it guards against.

def emitted_of(r):
    """{key: sources} of a step's emissions, or the refusal as a problem."""
    if not isinstance(r, K.ProofState):
        raise Mismatch(2, ("step",), describe(r))
    return {ob.key: frozenset(ob.sources) for ob in r.last.emitted}


def emitted_problems(got, want):
    """want: {judgement string: sources}; keys compared as trees."""
    want = {T.parse_judgement(j, SIG): frozenset(s) for j, s in want.items()}
    if got == want:
        return []
    return [f"emitted {sorted((T.show(k), sorted(s)) for k, s in got.items())}, "
            f"expected {sorted((T.show(k), sorted(s)) for k, s in want.items())}"]


def field_atom_divisor_problems():
    """SOURCES['field_div']: field owes the divisors inside atom arguments
    (§6.2 rev 7). In P1 each such divisor (sqrt 3 in atan((2x-1)/sqrt 3))
    is also a top-level one, so P1 masks a field that skips them."""
    ds = [T.show(d) for d in FD.field(term("sin(x/y)"), term("sin(x/y)")).divisors]
    return [] if ds == ["y"] else [f"field(sin(x/y), sin(x/y)) owes {ds}, expected ['y']"]


def ftc_F_formers_problems():
    """E9 (ii), E6: ftc charges F's own formers on the closed [a, b]. P1's
    F's have only closed divisors (E5 moves them to domain ()), so this uses
    an F with an x-dependent one."""
    st = K.install(goal("Int[x=1..2] (-1)/x^2 == ?A"))
    got = emitted_of(K.step(st, "ftc", {"F": term("1/x"), "check": "field", "facts": []}))
    out = []
    if "former" not in got.get(T.parse_judgement("x # 0 @ [1, 2]", SIG), ()):
        out.append(f"no former x # 0 @ [1, 2] among {sorted(map(show, got))}")
    if T.parse_judgement("x # 0 @ (1, 2)", SIG) not in got:
        out.append("no d_inv x # 0 @ (1, 2): the closed and open keys must stay distinct")
    return out


def placement_install(g, want):
    return lambda: emitted_problems(emitted_of(K.install(goal(g))), want)


def placement_fact_hyp():
    """§6.4's premises and E9's children for F := sqrt x, checked by field
    with the fact sqrt_sq_val x: the fact's hypothesis lands on the check's
    domain (1, 4), not the goal's, and a non-closed one keeps it (E5). F's
    own sqrt owes x >= 0 on the closed [1, 4] (E26), a different key, and
    the new goal's sqrt 4 and sqrt 1 owe 4 >= 0 and 1 >= 0 (E7)."""
    st = K.install(goal("Int[x=1..4] 1/(2*sqrt x) == ?A"))
    st = K.step(st, "fact", {"entry": "sqrt_sq_val", "inst": {"a": term("x")}, "bind": "h"})
    r = K.step(st, "ftc", {"F": term("sqrt x"), "check": "field", "facts": [st.last.handle]})
    return emitted_problems(emitted_of(r), {
        "sqrt x in C^0([1, 4])": ["ftc_F_C0"], "sqrt x in C^1((1, 4))": ["ftc_F_C1"],
        "D[x](sqrt x) == 1/(2*sqrt x) @ (1, 4)": ["ftc_D"],
        "1/(2*sqrt x) in C^0([1, 4])": ["ftc_f_C0"], "x > 0 @ (1, 4)": ["d_sqrt"],
        "2*sqrt x # 0 @ (1, 4)": ["field_div"], "x >= 0 @ (1, 4)": ["fact_hyp"],
        "x >= 0 @ [1, 4]": ["former"], "4 >= 0": ["former"], "1 >= 0": ["former"]})


def placement_fact_inst(g, entry, inst, value, want):
    """E10 with E6/E26 (a): a fact's inst values' formers are charged by
    the step that uses the fact, at that step's domain, source 'former'."""
    def run():
        st = K.install(goal(g))
        st = K.step(st, "fact", {"entry": entry, "bind": "h",
                                 "inst": {k: term(v) for k, v in inst.items()}})
        r = K.step(st, "close", {"value": term(value), "check": "field",
                                 "facts": [st.last.handle]})
        return emitted_problems(emitted_of(r), want)
    return run


def placement_fact_inst_ftc():
    """E10 with E6/E26 (a) where the using step's domain is not the goal's:
    ftc checks on (a, b), so the inst value's ln x owes x > 0 @ (1, 4), where
    it merges with d_sqrt's key. It does not become a separate x > 0 on the
    goal's empty domain. close passes the goal's domain as both, so only
    ftc can tell the two apart."""
    st = K.install(goal("Int[x=1..4] 1/(2*sqrt x) == ?A"))
    st = K.step(st, "fact", {"entry": "sqrt_sq_val", "inst": {"a": term("x + 0*ln x")}, "bind": "h"})
    r = K.step(st, "ftc", {"F": term("sqrt x"), "check": "field", "facts": [st.last.handle]})
    return emitted_problems(emitted_of(r), {
        "sqrt x in C^0([1, 4])": ["ftc_F_C0"], "sqrt x in C^1((1, 4))": ["ftc_F_C1"],
        "D[x](sqrt x) == 1/(2*sqrt x) @ (1, 4)": ["ftc_D"],
        "1/(2*sqrt x) in C^0([1, 4])": ["ftc_f_C0"],
        "x > 0 @ (1, 4)": ["d_sqrt", "former"],
        "2*sqrt x # 0 @ (1, 4)": ["field_div"],
        "x + 0*ln x >= 0 @ (1, 4)": ["fact_hyp"],
        "x >= 0 @ [1, 4]": ["former"], "4 >= 0": ["former"], "1 >= 0": ["former"]})


def placement_close(g, value, check, want):
    """E6 and E26 (a) for close (§9): the value enters the proof at the goal's
    domain, so its formers are charged there, source 'former'. A former with no
    free variable in the goal domain cannot tell this apart from charging at ()."""
    def run():
        st = K.install(goal(g))
        r = K.step(st, "close", {"value": term(value), "check": check, "facts": []})
        return emitted_problems(emitted_of(r), want)
    return run


# (label, problem function). Every P1 rhs is ?A, no P1 key inside a
# non-literal Int body is x-dependent, P1's one fact hypothesis is closed,
# every P1 orientation is closed (E5 gives it domain ()), no P1 goal nests
# Ints, has a -oo limit, or holds a negative Pow or an RPow, and none holds
# one partial former at two different position domains, so none of these
# placements or formers shows in P1's data.
EMISSION_PLACEMENT = [
    ("one former at two position domains in one term gives two keys (E6, E26)",
     placement_install("(Int[x=0..1] ln(x+2)) - (Int[x=-3..0] ln(x+2)) == ?A",
                       {"x + 2 > 0 @ [0, 1]": ["former"], "x + 2 > 0 @ [-3, 0]": ["former"]})),
    ("install charges both sides' formers when the rhs is not ?A (E6)",
     placement_install("x == x*y/y", {"y # 0": ["former"]})),
    ("a closed key uses no range, so no orientation (ARCHITECTURE.md §4)",
     placement_install("Int[x=0..pi] 1/sqrt 3 == ?A",
                       {"sqrt 3 # 0": ["former"], "3 >= 0": ["former"]})),
    ("a key that uses the range brings its orientation (E4, E6)",
     placement_install("Int[x=1..pi] 1/x == ?A",
                       {"x # 0 @ [1, pi]": ["former"], "1 <= pi": ["orient"]})),
    ("ftc places a fact's hypothesis on the check's domain (E9, E10)",
     placement_fact_hyp),
    ("a negative integer power charges its base's former NonZero (E6, §5.1)",
     placement_install("Int[x=1..2] x^(-2) == ?A", {"x # 0 @ [1, 2]": ["former"]})),
    ("the boundary power n = -1 charges the same former (E6, §5.1)",
     placement_install("Int[x=1..2] x^(-1) == ?A", {"x # 0 @ [1, 2]": ["former"]})),
    ("a real power charges base > 0, strict (E6; GRAMMAR.md RPow owes a > 0)",
     placement_install("Int[x=1..2] x^y == ?A", {"x > 0 @ [1, 2]": ["former"]})),
    ("an infinite lower end is open, the finite end closed, no orientation (E4)",
     placement_install("Int[x=-oo..-1] 1/x == ?A", {"x # 0 @ (-oo, -1]": ["former"]})),
    ("NegInf is the lower end whichever limit it was written as (E4)",
     placement_install("Int[x=-1..-oo] 1/x == ?A", {"x # 0 @ (-oo, -1]": ["former"]})),
    ("literal ends are ordered into [min, max], with no orientation (E4)",
     placement_install("Int[x=1..0] 1/x == ?A", {"x # 0 @ [0, 1]": ["former"]})),
    ("each enclosing Int's orientation is owed, not only the innermost (E4, E6)",
     placement_install("Int[y=1..pi] (Int[x=1..y] 1/(x*y)) == ?A",
                       {"x*y # 0 @ y in [1, pi], x in [1, y]": ["former"],
                        "1 <= pi": ["orient"], "1 <= y @ [1, pi]": ["orient"]})),
    ("an orientation that is not closed keeps the goal's domain (E4, E5)",
     placement_install("Int[x=1..y] 1/x == ?A @ y > 1",
                       {"x # 0 @ y > 1, x in [1, y]": ["former"],
                        "1 <= y @ y > 1": ["orient"]})),
    ("a goal hypothesis's former is charged at the hypotheses before it (E6, E26)",
     placement_install("x == ?A @ x > 0, ln x > 0", {"x > 0 @ x > 0": ["former"]})),
    ("the first hypothesis's former owes on the empty domain (E6)",
     placement_install("x == ?A @ 1/y > 0", {"y # 0": ["former"]})),
    ("an interval hypothesis's ends are charged too (E6, E26)",
     placement_install("x == ?A @ y > 0, x in [0, sqrt y]", {"y >= 0 @ y > 0": ["former"]})),
    ("a fact's inst former lands on the using step's domain (E10, E26)",
     placement_fact_inst("atan(-x) == ?A @ x > 1", "atan_odd", {"u": "x + 0*ln x"},
                         "-atan(x)", {"x > 0 @ x > 1": ["former"]})),
    ("a fact's inst tan u owes cos u # 0 when the fact is used (E10, E26)",
     placement_fact_inst("atan(-3) == ?A", "atan_odd", {"u": "3 + 0*tan(pi/2)"},
                         "-atan(3)", {"cos(pi/2) # 0": ["former"], "2 # 0": ["former", "field_div"]})),
    ("ftc charges a fact's inst former on the check's domain, not the goal's (E10, E26)",
     placement_fact_inst_ftc),
    ("close charges the value's formers at the goal's domain (E6, E26, §9)",
     placement_close("ln x == ?A @ x > 1", "ln x", "ring", {"x > 0 @ x > 1": ["former"]})),
]

# TAG_RULES read as cases, both ways: a tagger that over-tags a false
# obligation passes P1, where only OCCURRENCE_CASE's t >= 0 @ [-1, 0] is
# tagged none. Rows are (judgement, gamma is its domain, want): the kernel
# passes the goal-domain part of a key's domain as gamma (ARCHITECTURE.md
# §5), and no P1 goal has a domain, so P1 never passes a non-empty one.
TAGGER_CASES = [
    # cite fails when the entry's hypothesis is itself tagged none
    ("sqrt x # 0 @ [-1, 0]", False, ("none", ())),
    ("sqrt(x - 1) # 0 @ (0, 1)", False, ("none", ())),
    # a zero constant is accepted only for >= and <= (E20)
    ("x^2 > 0 @ [-1, 1]", False, ("none", ())),
    ("0 < x^2 @ [-1, 1]", False, ("none", ())),
    # a negative content flips p's sign goal (E18)
    ("-2*sqrt x > 0 @ (0, 1)", False, ("none", ())),
    ("-2*x > 0 @ (0, 1)", False, ("none", ())),
    # a closed interval end gives <=, not < (TAG_RULES range, linear)
    ("x > 0 @ [0, 1]", False, ("none", ())),
    # hyp needs prop to follow from gamma, not merely a non-empty gamma
    ("x > 5 @ x > 0", True, ("none", ())),
    # and the same rules where they do close, so a mutant cannot over-correct
    ("sqrt x # 0 @ (0, 1)", False, ("cite", ("sqrt_pos",))),
    ("x^2 >= 0 @ [-1, 1]", False, ("sign", ())),
    # E20 on the goal as written: the normal form has discriminant 0 and an
    # odd monomial, and range sees x^2 as opaque, so only this path closes it
    ("(x - 1)^2 >= 0 @ [-1, 1]", False, ("sign", ())),
    ("-2*sqrt x < 0 @ (0, 1)", False, ("sign product", ("sqrt_pos",))),  # range cannot
    ("x > 1 @ x > 1", True, ("hyp", ())),
    ("t - 2 # 0 @ [0, 1]", False, ("range", ())),  # the e < 0 sense of # 0
    ("x > 0 @ (pi, 5)", False, ("range", ("pi_pos",))),  # a constant only in dom
    # tagger.py's documented deletion-filter order (sign facts dropped
    # first); TAG_RULES does not settle this case, so it pins that choice
    ("pi + x - x > 0 @ (0, pi)", False, ("range", ())),
    # range comes before sign in §5.3's order, with a non-empty gamma
    ("x^2 + 1 > 0 @ x^2 > 3", True, ("range", ())),
]


def tagger_problems():
    out = []
    for s, g, want in TAGGER_CASES:
        k = T.parse_judgement(s, SIG)
        got = TG.tag(k, k.dom if g else ())
        if (got[0], tuple(got[1])) != want:
            out.append(f"tag({s}{', gamma = its domain' if g else ''}) is {got}, "
                       f"expected {want}")
    # _emit passes gamma () when E5 dropped the key's domain: a closed key
    # on a goal with a domain is not 'hyp' because the goal assumes it
    r = K.install(goal("1/(pi - 3) == ?A @ pi - 3 # 0"))
    got = ([(T.show(ob.key), tag_of(ob)) for ob in r.last.emitted]
           if isinstance(r, K.ProofState) else describe(r))
    if got != [("pi - 3 # 0", ("none", ()))]:
        out.append(f"install 1/(pi - 3) == ?A @ pi - 3 # 0 emits {got}, "
                   "expected [('pi - 3 # 0', ('none', ()))]")
    return out


# §6.3's two divisor-owing rules that P1 never reaches with x in the
# divisor: d_inv (@ u # 0) and d_pow_int for n < 0 (@ u # 0). §5.1 wants
# 1/x and x^(-1) to owe the same, the asymmetry revision 1 had. Also rev 7's
# d_const on an x-free App outside a Div: P1 meets x-free Apps only under a
# Div, where d_const already absorbs them, so a walk that sends sin 2 to
# d_sin (or ln 2 to d_ln, emitting 2 > 0) would pass P1.
OFF_P1_DERIV = [
    ("1/x", "-1/x^2", [("d_inv", "1/x", ["x # 0 @ (1, 2)"]), ("d_var", "x", [])]),
    ("x^(-1)", "-x^(-2)", [("d_pow_int", "x^(-1)", ["x # 0 @ (1, 2)"]), ("d_var", "x", [])]),
    ("x^(-2)", "-2*x^(-3)", [("d_pow_int", "x^(-2)", ["x # 0 @ (1, 2)"]), ("d_var", "x", [])]),
    ("x*sin 2", "sin 2", [("d_mul", "x*sin 2", []), ("d_var", "x", []),
                          ("d_const", "sin 2", [])]),
    ("x*ln 2", "ln 2", [("d_mul", "x*ln 2", []), ("d_var", "x", []),
                        ("d_const", "ln 2", [])]),
]


def off_p1_deriv_problems():
    dom = T.parse_judgement("x > 0 @ (1, 2)", SIG).dom
    out = []
    for F, value, want in OFF_P1_DERIV:
        got = DV.deriv(term(F), "x", dom)
        w = Counter((r, term(s), frozenset(T.parse_judgement(j, SIG) for j in em))
                    for r, s, em in want)
        g = Counter((e.rule, e.subterm, frozenset(e.emits)) for e in got.trace)
        if g != w:
            shown = sorted((r, T.show(s), sorted(map(T.show, em))) for r, s, em in g)
            out.append(f"{F}: trace {shown}")
        if not equal_by("field", got.output, term(value))[0]:
            out.append(f"{F}: output {show(got.output)} is not {value} by field")
    # E12's literal output form, which field equality cannot see: x*0, not
    # x*(cos 2 * 0).
    got = DV.deriv(term("x*sin 2"), "x", dom)
    if got.output != term("1*sin 2 + x*0"):
        out.append(f"x*sin 2: output {show(got.output)} is not 1*sin 2 + x*0 literally")
    return out


class LookAlike(str):
    """A name equal to every name, hashing as 'y': two variables become one
    ring atom when a name's type is not checked."""

    def __eq__(self, other):
        return True

    def __ne__(self, other):
        return False

    def __hash__(self):
        return hash("y")


def forged(cls, **fields):
    """A node built round its constructor, whose check it skips."""
    x = object.__new__(cls)
    for k, v in fields.items():
        object.__setattr__(x, k, v)
    return x


def forged_pow(base, n):
    """A Pow built round its constructor, which refuses a non-int n."""
    return forged(T.Pow, base=base, n=n)


def forged_num(n):
    """A Num built round its constructor, which refuses a non-natural n."""
    return forged(T.Num, n=n)


class Lying(int):
    """An int whose text is '2', whatever its value: show() would print the
    fake and the kernel compute with the real one."""

    def __str__(self):
        return "2"

    __repr__ = __str__


def hostile(lhs, dom=()):
    return (T.Rel("==", lhs, T.MVar("A"), dom),)


_x = T.Var("x")
# Goal trees built by hand that check_goal must refuse 'syntax' (GRAMMAR.md
# §7's invariants): each would install and, left alone, print as another
# statement or merge two atoms.
HOSTILE_TREES = [
    ("a Var named '2 + 1': 2 + 1*0 == 0 reads 2 == 0",
     lambda: hostile(T.Mul(T.Var("2 + 1"), T.Num(0)))),
    ("a str-subclass Var: z - y == 0 as one atom",
     lambda: hostile(T.Add(T.Var(LookAlike("z")), T.Neg(T.Var("y"))))),
    ("Var('pi'), which prints as the constant",
     lambda: hostile(T.Integral("x", T.Num(0), T.Num(1), T.Var("pi")))),
    ("Var('sinx'), which is not a name (D4)", lambda: hostile(T.Var("sinx"))),
    ("Const('e'), which is not a constant (D3)", lambda: hostile(T.Const("e"))),
    ("an Int binder that is not a str",
     lambda: hostile(T.Integral(7, T.Num(0), T.Num(1), _x))),
    ("a D binder 'x y'", lambda: hostile(T.Deriv("x y", _x))),
    ("a Call to the builtin name sin", lambda: hostile(T.Call("sin", (_x,)))),
    ("a Call whose args are not a tuple", lambda: hostile(T.Call("f", _x))),
    ("a domain that is a list, aliased into the theorem",
     lambda: hostile(T.Div(_x, _x), [T.Rel(">", _x, T.Num(0))])),
    ("interval flags that are ints",
     lambda: hostile(T.Div(_x, _x), (T.Interval("x", T.Num(0), 1, T.Num(1), 1),))),
    ("(2^0.5)^2 - 2 as an RPow base, its float Pow built round the constructor",
     lambda: hostile(T.RPow(T.Add(T.Pow(forged_pow(T.Num(2), 0.5), 2),
                                  T.Neg(T.Num(2))), T.Var("y")))),
    ("a Num holding an int subclass that prints as 2: 1 + 2 == 2",
     lambda: hostile(T.Add(T.Num(1), forged_num(Lying(3))))),
    ("a Num holding -3, which prints as Neg(Num 3)",
     lambda: hostile(T.Pow(forged_num(-3), 2))),
    ("a Num holding True, which prints as a name", lambda: hostile(forged_num(True))),
    ("an RPow with a literal exponent, which reparses as Pow (D17)",
     lambda: hostile(forged(T.RPow, base=_x, exp=T.Num(2)))),
    ("an Interval with a closed -oo end (D18)",
     lambda: hostile(T.Div(_x, _x), (forged(T.Interval, var="x", lo=T.NEG_INF,
                                            lo_closed=True, hi=T.Num(1),
                                            hi_closed=True),))),
    ("a PosInf subclass as an Int limit: Int[x = oo .. oo] scoped as (-oo, oo)",
     lambda: hostile(T.Integral("x", OtherPosInf(), T.POS_INF, T.Div(T.Num(1), _x)))),
    ("a NegInf subclass as an Interval end",
     lambda: hostile(T.Div(_x, _x), (T.Interval("x", OtherNegInf(), False, T.Num(1),
                                                True),))),
]


def hostile_tree_problems():
    out = []
    for label, build in HOSTILE_TREES:
        r = K.install(build())
        if not isinstance(r, K.Refusal) or r.code != "syntax":
            out.append(f"{label}: {describe(r)}")
    return out


class OtherPosInf(T.PosInf):
    """An oo look-alike: a subclass instance, which isinstance takes for oo."""
    __slots__ = ()


class OtherNegInf(T.NegInf):
    __slots__ = ()


def unset(cls):
    """A node built with object.__new__ and no slot set."""
    return object.__new__(cls)


def hand_int(v, lo, hi, body):
    return T.Integral(v, lo, hi, body)


def raised_code(thunk):
    """The code a thunk refuses with, whether it raises Refused or returns a
    K.Refusal, or a problem string."""
    try:
        r = thunk()
    except T.Refused as e:
        return e.code
    except Exception as e:  # noqa: BLE001 -- a crash, not a refusal
        return "raised " + crash_text(e)
    return r.code if isinstance(r, K.Refusal) else f"accepted {describe(r)}"


_t, _A = T.Var("t"), T.MVar("A")
# (label, thunk, code): refusals called directly, for rules no move reaches
# and for check_goal's own guards, which the parser's copies always beat to
# a parsed goal. subst's cases are GRAMMAR.md §5's and §10's; the hand-built
# goals reach check_goal (through install, or by itself) with trees the
# parser would have refused first.
DIRECT_REFUSALS = [
    ("(D[x] x^2)[x := 1], which is 2 and not D[x](1^2) (GRAMMAR §5)",
     lambda: T.subst(term("D[x] x^2"), {"x": T.Num(1)}), "subst-under-D"),
    ("(D[x](x*y))[y := x]", lambda: T.subst(term("D[x](x*y)"), {"y": _x}),
     "subst-under-D"),
    ("(D[x](x*z))[x := z]", lambda: T.subst(term("D[x](x*z)"), {"x": T.Var("z")}),
     "subst-under-D"),
    ("(2^x)[x := 1], never silently a Pow (GRAMMAR §5, §10)",
     lambda: T.subst(term("2^x"), {"x": T.Num(1)}), "rpow-literal-exponent"),
    ("(x^(-y))[y := 1]", lambda: T.subst(term("x^(-y)"), {"y": T.Num(1)}),
     "rpow-literal-exponent"),
    ("install Int[x = -1 .. 1] x^(-2) == ?A @ x > 5 built by hand: without "
     "D11, ftc and close prove it == -2 on an empty domain",
     lambda: K.install((T.Rel("==", hand_int("x", term("-1"), T.Num(1), term("x^(-2)")),
                              _A, (T.Rel(">", _x, T.Num(5)),)),)), "D11-bound-and-free"),
    ("install Int[t = 0 .. 1] Int[t = 0 .. 1] t built by hand",
     lambda: K.install((T.Rel("==", hand_int("t", T.Num(0), T.Num(1),
                                             hand_int("t", T.Num(0), T.Num(1), _t)), _A),)),
     "shadowing"),
    ("install Int[t = 0 .. t] t built by hand",
     lambda: K.install((T.Rel("==", hand_int("t", T.Num(0), _t, _t), _A),)),
     "bound-in-endpoint"),
    ("check_goal: x == ?A /\\ y == ?A built by hand (D15)",
     lambda: T.check_goal((T.Rel("==", _x, _A), T.Rel("==", T.Var("y"), _A))),
     "mvar-misplaced"),
    ("check_goal: Int[x = 0 .. 1] Int[x = 0 .. 1] x built by hand",
     lambda: T.check_goal((T.Rel("==", hand_int("x", T.Num(0), T.Num(1), hand_int(
         "x", T.Num(0), T.Num(1), _x)), _A),)), "shadowing"),
    ("check_goal: Int[x = 0 .. x] x built by hand",
     lambda: T.check_goal((T.Rel("==", hand_int("x", T.Num(0), _x, _x), _A),)),
     "bound-in-endpoint"),
    ("check_goal: Int[x = 0 .. 1] x == x built by hand",
     lambda: T.check_goal((T.Rel("==", hand_int("x", T.Num(0), T.Num(1), _x), _x),)),
     "D11-bound-and-free"),
]


def direct_refusal_problems():
    return [f"{label}: {got}, expected {code}" for label, thunk, code in DIRECT_REFUSALS
            if (got := raised_code(thunk)) != code]


def unset_slot_problems():
    """Nodes built with object.__new__ and no slot set: check_goal refuses
    them 'syntax' before it reads a slot, so install and step return a
    Refusal and raise nothing (E21; ARCHITECTURE.md §2)."""
    goals = [
        ("an unset Num", lambda: hostile(unset(T.Num))),
        ("an Add whose child is an unset Num", lambda: hostile(T.Add(_x, unset(T.Num)))),
        ("an unset Rel as the judgement", lambda: (unset(T.Rel),)),
        ("an unset Interval in a domain", lambda: hostile(T.Div(_x, _x), (unset(T.Interval),))),
    ]
    out = [f"install, {label}: {got}" for label, build in goals
           if (got := raised_code(lambda: K.install(build()))) != "syntax"]
    st = install("x == ?A", ("unset", "goal"))
    for label, value in (("an unset Num", lambda: unset(T.Num)),
                         ("an Add whose child is an unset Num",
                          lambda: T.Add(_x, unset(T.Num))),
                         ("an unset Add, whose children a walk would read",
                          lambda: unset(T.Add))):
        got = raised_code(lambda: K.step(st, "close", {"value": value(), "check": "ring",
                                                       "facts": []}))
        if got != "syntax":
            out.append(f"step close, {label}: {got}")
    return out + ([] if st.goal == goal("x == ?A") else ["the state changed"])


def unset_handle_problems():
    """A Handle built with object.__new__ and no field set, at the fact
    slot: refused fact-not-minted-handle, not an AttributeError out of step
    (_resolve_fact never raises anything else)."""
    slot = Slot()
    label, outcome, detail = at_slot(slot, "object.__new__(Handle), no fields",
                                     lambda: object.__new__(K.Handle))
    out = [] if outcome == "refusal:fact-not-minted-handle" else [f"{label}: {outcome} ({detail})"]
    return out + slot.post()


def close_theorem_check_problems():
    """close's closing check_goal on the theorem: a value may name, as a
    variable, a symbol the original goal calls, once ftc has removed the
    Call from the current goal. check_names in _check_args sees only the
    current goal, so only this check refuses it (D5-uncalled)."""
    st = K.install(T.parse_goal("Int[x = 0 .. 1] 0*f(x) == ?A", {"f": 1}))
    st = K.step(st, "ftc", {"F": T.Num(0), "check": "ring", "facts": []})
    if not isinstance(st, K.ProofState):
        return [f"ftc F := 0: {describe(st)}"]
    before, before_goal = st.obligations(), st.goal
    r = K.step(st, "close", {"value": term("f - f"), "check": "ring", "facts": []})
    out = [] if isinstance(r, K.Refusal) and r.code == "D5-uncalled" else [describe(r)]
    if st.obligations() != before or st.goal != before_goal:
        out.append("the refused step changed the state (E13)")
    return out


def lookalike_value_problems():
    """The same check at a move argument: a str-subclass close value is
    refused 'syntax' and the state is unchanged (E13)."""
    st = install("x == ?A", ("lookalike", "goal"))
    r = K.step(st, "close", {"value": T.Var(LookAlike("x")), "check": "ring", "facts": []})
    out = [] if isinstance(r, K.Refusal) and r.code == "syntax" else [describe(r)]
    return out + ([] if st.goal == goal("x == ?A") else ["the state changed"])


def pow_exponent_problems():
    """A Pow's exponent is an int where it is built, so a float never reaches
    norm_num, which would decide (2^0.5)^2 - 2 > 0 true from rounding."""
    out = []
    for n in (0.5, True, 2.0):
        try:
            T.Pow(_x, n)
            out.append(f"Pow(x, {n!r}) was built")
        except ValueError:
            pass
    return out


def vars_write_problems():
    """Every record a public accessor returns is frozen and slotted, so
    vars() raises: a display tactic tidying vars(record) cannot rewrite the
    tracker, a shared ancestor's records, or what a handle stands for (§15.3's
    by-accident standard). The Handle alone is not slotted (E17)."""
    records = [("an ENTRIES entry", e) for e in EN.ENTRIES.values()]
    for proof in ("P1.1", "P1.2"):
        st, handles = install(X.PROOFS[proof]["goal"], (proof, "goal")), {}
        for s in X.PROOFS[proof]["steps"]:
            st = take(st, s["move"], s["args"], handles, (proof, s["id"]))
            records += [("obligations()", o) for o in st.obligations()]
            records += [("last", st.last)] + [("last.emitted", o) for o in st.last.emitted]
            records += [("last.trace", e) for e in st.last.trace or ()]
            if st.goal is not None:
                records += [("goal", st.goal[0]), ("goal lhs", st.goal[0].lhs)]
                records += [("a domain item", d) for d in st.goal[0].dom]
        records += [("conclusion(h)", st.conclusion(h)) for h in handles.values()]
    out = sorted({f"vars() of {label} ({type(r).__name__}) returns its dict"
                  for label, r in records if hasattr(r, "__dict__")})
    # The handle-conclusion attack: rewrite what h means, then close with it.
    st = install("pi == ?A", ("vars", "goal"))
    st = K.step(st, "fact", {"entry": "sqrt_sq_val", "inst": {"a": T.Num(3)}, "bind": "h"})
    h = st.last.handle
    with contextlib.suppress(TypeError):
        vars(st.conclusion(h)).update(lhs=T.Const("pi"), rhs=T.Num(3), dom=())
    r = K.step(st, "close", {"value": T.Num(3), "check": "field", "facts": [h]})
    if isinstance(r, K.ProofState):
        out.append(f"pi == 3 closed after a vars() write: {K.report(r)!r}")
    return out


def report_fails_closed_problems():
    """report counts a status that is neither discharged nor admitted as
    open, so 'Proved.' needs every obligation discharged. The statuses are
    changed by the private route (object.__setattr__), test-only, on a fresh
    replay."""
    out = []
    st = K.step(install("1 + 1 == ?A", ("owes nothing", "goal")), "close",
                {"value": T.Num(2), "check": "ring", "facts": []})
    if K.report(st) != "Proved.":  # a goal that owes nothing; no PROOFS run
        out.append(f"1 + 1 == ?A := 2 reports {K.report(st)!r}")
    s6, _ = replay("P1.1", "s6")
    for ob in s6.obligations():
        object.__setattr__(ob, "status", ob.status.capitalize())
    if not K.report(s6).startswith("Stuck"):
        out.append(f"every status unknown, and the report is {K.report(s6)!r}")
    return out


def entries_readonly_problems():
    """ENTRIES is the trusted cite library (§15.2 item 7): registering an
    entry from outside must fail, not extend it."""
    out = []
    try:
        EN.ENTRIES["pi_three"] = EN.Entry("pi_three", T.parse_judgement("pi == 3"), ())
        out.append("ENTRIES took a new entry")
    except TypeError:
        pass
    st = install("pi == ?A", ("pi_three", "goal"))
    r = K.step(st, "rewrite", {"entry": "pi_three", "inst": {}, "at": T.Const("pi")})
    if isinstance(r, K.ProofState):
        out.append("rewrite with pi_three was accepted")
    return out


def app_rules_readonly_problems():
    """deriv.APP_RULES is trusted too in this milestone (§15.2 item 2): a
    helper that 'registers a missing rule' must fail, not extend it. A wrong
    d cosh = cosh would prove Int[x=0..1] cosh x == cosh 1 - cosh 0 with
    both admissions true."""
    out = []
    try:
        DV.APP_RULES["cosh"] = lambda u, du: (T.Mul(T.App("cosh", u), du), ())
        out.append("APP_RULES took a new rule")
    except TypeError:
        pass
    st = install("Int[x = 0 .. 1] cosh x == ?A", ("cosh", "goal"))
    r = K.step(st, "ftc", {"F": term("cosh x"), "check": "ring", "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "deriv-no-rule"):
        out.append(f"ftc with F := cosh x gave {describe(r)}, not deriv-no-rule")
    return out


def rewrite_non_equation_problems():
    """rewrite reads an entry's statement as lhs -> rhs, so it must take
    only an `==` entry: read `pi > 0` as pi -> 0 and 'pi == 0' is Proved.
    Both non-equation entries are tried, one closed and one with a
    hypothesis; each must be refused 'bad-args'."""
    out = []
    for name, inst, at, g in (
            ("pi_pos", {}, T.Const("pi"), "pi == ?A"),
            ("sqrt_pos", {"a": term("3")}, term("sqrt 3"), "sqrt 3 == ?A")):
        st = install(g, (name, "goal"))
        r = K.step(st, "rewrite", {"entry": name, "inst": inst, "at": at})
        if not (isinstance(r, K.Refusal) and r.code == "bad-args"):
            out.append(f"rewrite with {name} gave {describe(r)}, not bad-args")
    return out


def call_args_step_problems():
    """A Call whose args are not a tuple (Call('f', x), a plausible tactic
    slip) is refused 'syntax' in every term slot of a step, as install
    refuses it, never raised as a TypeError (E21)."""
    bad = T.Call("f", _x)
    worse = T.Call("f", 5)
    cases = [
        ("close value", "x == ?A", "close", {"value": bad, "check": "ring", "facts": []}),
        ("rewrite at", "sin 0 == ?A", "rewrite",
         {"entry": "sin_zero", "inst": {}, "at": worse}),
        ("rewrite inst", "sqrt(x^2) == ?A", "rewrite",
         {"entry": "sqrt_sq", "inst": {"u": bad}, "at": term("sqrt(x^2)")}),
        ("fact inst", "x == ?A", "fact",
         {"entry": "sqrt_sq_val", "inst": {"a": bad}, "bind": "h"}),
        ("ftc F", "Int[x = 0 .. 1] x == ?A", "ftc", {"F": bad, "check": "ring", "facts": []}),
    ]
    out = []
    for label, g, move, args in cases:
        st = install(g, (label, "goal"))
        try:
            r = K.step(st, move, args)
        except Exception as e:  # noqa: BLE001 -- the crash is the finding
            out.append(f"{label}: raised {crash_text(e)}")
            continue
        if not (isinstance(r, K.Refusal) and r.code == "syntax"):
            out.append(f"{label}: {describe(r)}")
    return out


def call_name_problems():
    """GRAMMAR.md §7's Call invariant, without a sig: within one statement a
    called name has one arity and is never a variable, or the echo parses
    under no sig and x(y) is an atom independent of a bound x. Checked at
    install and for a term a move brings into the goal."""
    y = T.Var("y")
    cases = [
        ("x(y) + x", hostile(T.Add(T.Call("x", (y,)), _x)), "D5-uncalled"),
        ("f(y) + f(y, x)", hostile(T.Add(T.Call("f", (y,)), T.Call("f", (y, _x)))),
         "D5-arity"),
        ("Int[x = 0 .. 1] (2*x - 1)*x(y)",
         hostile(T.Integral("x", T.Num(0), T.Num(1), T.Mul(
             T.Add(T.Mul(T.Num(2), _x), T.Neg(T.Num(1))), T.Call("x", (y,))))),
         "D5-uncalled"),
    ]
    out = []
    for label, g, code in cases:
        r = K.install(g)
        if not (isinstance(r, K.Refusal) and r.code == code):
            out.append(f"install {label}: {describe(r)}, not {code}")
    st = install("x == ?A", ("x(1)", "goal"))
    r = K.step(st, "close", {"value": T.Call("x", (T.Num(1),)), "check": "ring",
                             "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "D5-uncalled"):
        out.append(f"close x == ?A with x(1): {describe(r)}, not D5-uncalled")
    st = install("Int[x = 0 .. 1] 2*x == ?A", ("F := x(y)", "goal"))
    r = K.step(st, "ftc", {"F": T.Call("x", (y,)), "check": "ring", "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "D5-uncalled"):
        out.append(f"ftc with F := x(y): {describe(r)}, not D5-uncalled")
    return out


def schema_call_problems():
    """E23's Call exclusion, which the empty P1 SIG keeps out of every data
    case: erf(1) == ?A closed with erf(1) by refl is the empty theorem."""
    sig = {"erf": 1}
    st = K.install(T.parse_goal("erf(1) == ?A", sig))
    if not isinstance(st, K.ProofState):
        return [f"install erf(1) == ?A: {describe(st)}"]
    r = K.step(st, "close", {"value": T.parse_term("erf(1)", sig), "check": "ring",
                             "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "close-schema-not-closed"):
        return [f"close with erf(1): {describe(r)}"]
    return []


# REWRITE_RULE step 9(a)'s subterm clause, called directly: no entry in
# ENTRIES has a strict hypothesis (sqrt_sq and sqrt_sq_val owe >= 0, refused
# before the clause is reached), and ENTRIES is read-only, so no move reaches
# it until such an entry joins. E11's counterexamples are the first two.
OPEN_IN_CASES = [
    ("sqrt x + 1 > 0", False), ("sqrt x + 1 # 0", False), ("asin x < 1", False),
    ("acos x > 0", False), ("acosh x > 0", False), ("D[x] x^2 > 0", False),
    ("Int[t = 0 .. x] t > 0", False), ("x >= 0", False),
    ("x + 1 > 0", True), ("x # 0", True),
    ("sqrt 3 + x > 0", True),  # an x-free sqrt subterm is allowed
]


def open_in_problems():
    return [f"_open_in({s}, x) is {not want}" for s, want in OPEN_IN_CASES
            if K._open_in(T.parse_judgement(s, SIG), "x") is not want]


def reversed_ftc_problems():
    """§6.4's F(b) - F(a) uses the Int's own limits, b its upper one, even
    when E4 orders literal ends into [0, 1]: Int[x=1..0] 2*x is -1, and
    reading b and a off the sorted interval would prove it 1."""
    st = install("Int[x=1..0] 2*x == ?A", ("reversed", "goal"))
    st = take(st, "ftc", {"F": "x^2", "check": "ring", "facts": []}, {},
              ("reversed", "ftc"))
    out = []
    if st.goal != goal("0^2 - 1^2 == ?A"):
        out.append(f"goal after ftc: {show(st.goal)}, expected 0^2 - 1^2 == ?A")
    r = K.step(st, "close", {"value": term("1"), "check": "ring", "facts": []})
    if not (isinstance(r, K.Refusal) and r.code == "close-check-failed"):
        out.append(f"close with 1: {describe(r)}")
    r = K.step(st, "close", {"value": term("-1"), "check": "ring", "facts": []})
    if not isinstance(r, K.ProofState) or r.theorem != goal("Int[x=1..0] 2*x == -1"):
        out.append(f"close with -1: {describe(r)}")
    return out


def occurrence_k_problems():
    """OCCURRENCE_CASE 'one' with occurrence 1: the second Int is rewritten,
    so a kernel that ignores k and takes the first is seen."""
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(X.OCCURRENCE_CASE["goal"], ("occurrence 1", "goal"))
    move, args = X.OCCURRENCE_CASE["one"]["move"]
    st2 = take(st, move, dict(args, occurrence=1), {}, ("occurrence 1", move))
    if st2.last.occurrences != 1:
        out.append(f"occurrences {st2.last.occurrences}, expected 1")
    if st2.goal != goal("(Int[t = 0 .. 1] sqrt(t^2)) + (Int[t = -1 .. 0] t) == ?A"):
        out.append(f"goal_after: got {show(st2.goal)}")
    compare_emitted(miss, "occurrence 1", move,
                    [("t >= 0", "[-1, 0]", (X.S_SQRT_SQ,), X.ADMITTED, X.T_NONE, True)],
                    st2.last.emitted, keys_of(st))
    return out


def unit_test_problems():
    """test_field.py and test_grammar.py, in a child process: the cases
    that cover field, whose bug would be a false Proved."""
    here = os.path.dirname(os.path.abspath(__file__))
    r = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", here,
                        "-t", here], capture_output=True, text=True, cwd=here,
                       timeout=1800)
    return [] if r.returncode == 0 else r.stderr.splitlines()[-30:]


# ---------------------------------------------------------------- the parser

PARSERS ={"term": T.parse_term, "judgement": T.parse_judgement, "goal": T.parse_goal}


def sx(x):
    """A tree in GRAMMAR.md §9's S-expression notation, written here and not
    taken from the kernel, so it is an independent reading of the tree."""
    if isinstance(x, tuple):
        return tuple(map(sx, x))
    if isinstance(x, T.Num):
        return str(x.n)
    if isinstance(x, (T.Const, T.Var)):
        return x.name
    if isinstance(x, T.MVar):
        return "?" + x.name
    if isinstance(x, T.PosInf):
        return "oo"
    if isinstance(x, T.NegInf):
        return "-oo"
    if isinstance(x, T.Neg):
        return f"(neg {sx(x.a)})"
    if isinstance(x, (T.Add, T.Mul, T.Div)):
        return f"({type(x).__name__.lower()} {sx(x.a)} {sx(x.b)})"
    if isinstance(x, T.Pow):
        return f"(pow {sx(x.base)} {x.n})"
    if isinstance(x, T.RPow):
        return f"(rpow {sx(x.base)} {sx(x.exp)})"
    if isinstance(x, T.App):
        return f"({x.fn} {sx(x.arg)})"
    if isinstance(x, T.Call):
        return f"({x.fn} {' '.join(map(sx, x.args))})"
    if isinstance(x, T.Deriv):
        return f"(D {x.var} {sx(x.body)})"
    if isinstance(x, T.Integral):
        return f"(Int {x.var} {sx(x.lo)} {sx(x.hi)} {sx(x.body)})"
    if isinstance(x, T.Interval):
        return (f"(iv{'[' if x.lo_closed else '('}{']' if x.hi_closed else ')'} "
                f"{x.var} {sx(x.lo)} {sx(x.hi)})")
    dom = f" [{' '.join(map(sx, x.dom))}]" if x.dom else ""
    if isinstance(x, T.Rel):
        return f"({x.op} {sx(x.lhs)} {sx(x.rhs)}{dom})"
    if isinstance(x, T.NonZero):
        return f"(# {sx(x.e)}{dom})"
    if isinstance(x, T.Reg):
        return f"(reg {sx(x.e)} {x.k}{dom})"
    raise TypeError(f"no S-expression for {x!r}")


def round_trip_problems():
    out = []
    for kind, s in X.ROUND_TRIP:
        sig = X.ROUND_TRIP_SIGS.get(s, SIG)
        try:
            t = PARSERS[kind](s, sig)
            back = PARSERS[kind](T.show(t), sig)
        except T.ParseError as e:
            out.append(f"{kind} {s!r}: refused {e.code}")
            continue
        if back != t:
            out.append(f"{kind} {s!r} prints {T.show(t)!r}, which parses to another tree")
    return out


def tree_problems(rows):
    """rows of (kind, string, sig, tree)."""
    out = []
    for kind, s, sig, tree in rows:
        try:
            got = sx(PARSERS[kind](s, sig))
        except T.ParseError as e:
            out.append(f"{s!r}: refused {e.code}")
            continue
        if got != tree:
            out.append(f"{s!r} is {got}, expected {tree}")
    return out


def print_exact_problems():
    out = []
    for inp, printed, never in X.PRINT_EXACT:
        got = T.show(T.parse_term(inp, SIG))
        if got != printed or got == never:
            out.append(f"{inp!r} prints {got!r}, expected {printed!r}, never {never!r}")
    return out


def refusal_problems(rows, parse):
    out = []
    for s, sig, code in rows:
        try:
            t = parse(s, sig)
        except T.ParseError as e:
            if e.code != code:
                out.append(f"{s!r} with {sig}: refused {e.code}, expected {code}")
        except Exception as e:  # noqa: BLE001 -- not a ParseError
            out.append(f"{s!r}: {crash_text(e)}")
        else:
            out.append(f"{s!r} with {sig}: accepted as {sx(t)}, expected {code}")
    return out


# GRAMMAR.md §1 codes that no p1_expected parse case names, as the suite's
# own rows (s, sig, code) per entry point. D13-unnamed-interval and
# hash-nonzero are also in test_grammar.py, which the coverage check cannot
# read. The parse_goal rows reach the parser's own D11 and D15 checks.
SUITE_PARSE_REFUSALS = {
    "goal": [("Int[x = 0 .. 1] x == x", {}, "D11-bound-and-free"),
             ("x == ?A /\\ y == ?A", {}, "mvar-misplaced")],
    "term": [("Int[x = 0 .. x] x", {}, "bound-in-endpoint"),
             ("Int[x = 0 .. 1] Int[x = 0 .. 1] x", {}, "shadowing"),
             ("x + ?A", {}, "mvar-misplaced"),
             ("é", {}, "non-ascii"),
             ("Sum[n = 0 .. 1] n", {}, "D2-deferred"),
             ("log x", {}, "reserved-hint"),
             ("f", {"f": 0}, "D5-sig-arity0"),
             ("sin -x", {}, "D6-neg-operand"),
             ("sin f(x)^2", {"f": 1}, "D6-app-as-base")],
    "judgement": [("0 < x < 1", {}, "chained-cmp"),
                  ("1 > 0 @ [0, 1]", {}, "D13-unnamed-interval"),
                  ("a # (0)", {}, "hash-nonzero")],
}
# D16: a goal-level refusal carries its token's offset too, not None.
GOAL_OFFSETS = [("Int[x = 0 .. 1] x == x", 4),
                ("D[x] x^2 + (Int[x = 0 .. 1] x) == ?A", 16),
                ("x == ?A /\\ y == ?A", 16)]


def suite_parse_refusal_problems():
    out = [p for kind, rows in SUITE_PARSE_REFUSALS.items()
           for p in refusal_problems(rows, PARSERS[kind])]
    for s, at in GOAL_OFFSETS:
        try:
            T.parse_goal(s, SIG)
            out.append(f"{s!r}: accepted")
        except T.ParseError as e:
            if e.offset != at:
                out.append(f"{s!r}: {e.code} at offset {e.offset}, expected {at}")
    return out


def echo_noncanonical_problems():
    """ECHO_NONCANONICAL: an echo copied from the input would fail."""
    inp, want = X.ECHO_NONCANONICAL
    st = install(inp, ("ECHO_NONCANONICAL", "goal"))
    echo = T.show_goal(st.goal)
    out = []
    if echo != want:
        out.append(f"echo {echo!r}, expected {want!r}")
    if T.parse_goal(echo, SIG) != st.goal or st.goal != goal(X.P1_2_GOAL):
        out.append("the installed tree is not P1_2_GOAL's")
    return out


# ---------------------------------------------------------------- main

def by_item(run, item):
    return [fmt(w, d) for i, w, d in run.found if i == item]


def main():
    suite = Suite()
    print("proof_of_life: readiness P1 against p1_expected.py (WHAT.md Done-when 1-6)")
    print("protection in force (§15.3): "
          + (K.HANDLES_IN_FORCE if K is not None
             else "unknown (the kernel did not import)"))
    print("  fact slots take only the handle `fact` minted, by identity (E17); a "
          "proof state demands the kernel-private _TOKEN, which is enough because a "
          "finished state is only ever produced by step(), and §15.3's realistic "
          "threat, a buggy tactic building a result object, is refused; §16.3's API "
          "boundary, not built here, will replace in-process states with ids")
    suite.check(1, "the kernel imports, and its HANDLES_IN_FORCE, VERDICT and "
                "ADMISSION_REASON are p1_expected's",
                lambda: [f"{n} is {getattr(K, n)!r}" for n in
                         ("HANDLES_IN_FORCE", "VERDICT", "ADMISSION_REASON")
                         if getattr(K, n) != getattr(X, n)])
    suite.check(1, "the §6.8 entries are pinned as NAMED_ENTRIES states them",
                entries_problems)

    runs = {}
    for name, p in X.PROOFS.items():
        print(f"\n{name}{' (fallback)' if p['fallback'] else ''}")
        if K is None:
            for item in (1, 2, 6):
                suite.check(item, f"{name}", lambda: [])
            continue
        try:
            run = runs[name] = run_proof(name)
        except Exception as e:  # noqa: BLE001 -- a kernel crash mid-proof
            suite.record(1, f"{name} runs", ["crash: " + crash_text(e)])
            continue
        suite.record(6, f"{name}: the goal is echoed from the installed tree "
                     "before s1", by_item(run, 6))
        suite.record(1, f"{name}: {len(p['steps'])} steps accepted, closes with "
                     f"?A := {X.ANSWERS[name]}, N = {X.ADMISSIONS[name]}, "
                     f"'{X.VERDICTS[name]}'", by_item(run, 1))
        suite.record(2, f"{name}: every step's obligations (sources, status, tag, "
                     "new), deriv's trace, the final tracker, no tag none",
                     by_item(run, 2))
        suite.check(1, f"{name}: the answer is the integral (math module)",
                    lambda name=name: numeric_problems(name), needs_kernel=False)

    print("\nMatching, occurrences and deriv")
    for m in X.MATCH_ACCEPTS:
        suite.check(2, f"MATCH_ACCEPTS {m['id']}", lambda m=m: match_problems(m))
    for c in X.DEFINEDNESS_CASES:
        suite.check(2, f"DEFINEDNESS_CASES {c['id']}: {c['goal']} -> {c['report']!r}",
                    lambda c=c: definedness_problems(c))
    for which in ("all", "one"):
        suite.check(2, f"OCCURRENCE_CASE {which}: {X.OCCURRENCE_CASE[which]['occurrences']}"
                    " occurrence(s)", lambda w=which: occurrence_problems(w))
    suite.check(2, "OCCURRENCE_CASE one with occurrence 1 rewrites the second Int",
                occurrence_k_problems)

    print("\nBeyond P1's data: rules P1 masks")
    suite.check(2, "field owes divisors inside atom arguments: sin(x/y)",
                field_atom_divisor_problems)
    suite.check(2, "ftc charges F's formers on [a, b] (E9 ii): 1/x on [1, 2]",
                ftc_F_formers_problems)
    for label, fn in EMISSION_PLACEMENT:
        suite.check(2, f"emission placement: {label}", fn)
    suite.check(2, "ftc on a reversed literal range: F(b) - F(a) from the Int's own "
                "limits (§6.4, E4)", reversed_ftc_problems)
    suite.check(2, f"TAG_RULES both ways: {len(TAGGER_CASES)} tagger cases",
                tagger_problems)
    suite.check(4, "deriv off P1: the divisor-owing rules (1/x, x^(-1), x^(-2)) and "
                "d_const on an x-free App (x*sin 2, x*ln 2)", off_p1_deriv_problems)

    print("\nWrong answers")
    for w in X.WRONG_ANSWERS:
        suite.check(4, f"{w['id']}{' (added)' if w.get('added') else ''}: {w['what']}"
                    f" -> {w['refusal']}, residual {w['residual']}",
                    lambda w=w: wrong_answer_problems(w))
    suite.check(4, "W1: deriv's trace and output on sin t - t*cos t", w1_deriv_problems)

    print("\nBad moves")
    for b in X.BAD_MOVES:
        suite.check(5, f"{b['id']}{' (added)' if b.get('added') else ''} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for b in SUITE_BAD_MOVES:
        suite.check(5, f"{b['id']} (suite) -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for name, c in BACKSTOPS.items():
        suite.check(5, f"{name}: {c['case']} with {c['seam']} weakened -> {c['refusal']} "
                    "(a child process)", lambda n=name, c=c: backstop_problems(n, c))
    for name, c in ISOLATED_SEAMS.items():
        suite.check(5, f"{name}: {c['seam']} weakened alone; {len(c['results'])} moves "
                    "(a child process)", lambda n=name, c=c: isolated_problems(n, c))

    print("\nForgeries")
    for f in X.FORGERIES:
        suite.check(5, f"{f['id']}{' (added)' if f.get('added') else ''}: accepts "
                    f"{', '.join(f['accept'])}", lambda f=f: forgery_problems(f))
    suite.check(5, "every REFUSAL_CODES code, every kernel-local code and every "
                "GRAMMAR.md §1 code is asserted", refusal_coverage_problems)
    suite.check(5, f"{len(DIRECT_REFUSALS)} refusals called directly: subst under D "
                "and into RPow, and check_goal's scope guards on hand-built goals",
                direct_refusal_problems)
    suite.check(5, "state-not-minted and proof-finished, by direct calls",
                unminted_finished_problems)

    print("\nTrust (the suite's own cases)")
    suite.check(5, f"{len(HOSTILE_TREES)} hand-built goal trees are refused 'syntax' "
                "at install (GRAMMAR.md §7)", hostile_tree_problems)
    suite.check(5, "a str-subclass close value is refused 'syntax' at step",
                lookalike_value_problems)
    suite.check(5, "nodes with unset slots are refused 'syntax' at install and step, "
                "not raised", unset_slot_problems)
    suite.check(5, "an unset Handle at the fact slot is refused fact-not-minted-handle",
                unset_handle_problems)
    suite.check(5, "close's closing check_goal refuses a value naming a called "
                "symbol (D5-uncalled)", close_theorem_check_problems)
    suite.check(5, "Pow refuses a float or bool exponent where it is built",
                pow_exponent_problems)
    suite.check(5, "no record an accessor returns has a __dict__ for vars() to write",
                vars_write_problems)
    suite.check(5, "report fails closed: an unknown status blocks 'Proved.'",
                report_fails_closed_problems)
    suite.check(5, "ENTRIES is read-only: no lemma can be registered from outside",
                entries_readonly_problems)
    suite.check(5, "deriv.APP_RULES is read-only: no rule can be registered from outside",
                app_rules_readonly_problems)
    suite.check(5, "rewrite refuses a non-equation entry (pi_pos, sqrt_pos) 'bad-args'",
                rewrite_non_equation_problems)
    suite.check(5, "a Call with non-tuple args is refused 'syntax' in every step slot",
                call_args_step_problems)
    suite.check(5, "a called name has one arity and is never a variable (GRAMMAR.md §7)",
                call_name_problems)
    suite.check(5, "E23: a Call is off the closed whitelist (erf(1) == ?A := erf(1))",
                schema_call_problems)
    suite.check(5, f"REWRITE_RULE 9(a)'s subterm clause, directly: {len(OPEN_IN_CASES)} "
                "hypotheses", open_in_problems)

    print("\nParser")
    rt = X.ROUND_TRIP
    suite.check(6, f"parse(show(t)) == t over ROUND_TRIP's {len(rt)} strings",
                round_trip_problems, needs_kernel=False)
    what4 = X.ROUND_TRIP_EXTRA[:4]
    suite.check(6, "WHAT.md's four: " + ", ".join(s for _, s, _ in what4),
                lambda: tree_problems([(k, s, SIG, t) for k, s, t in what4]),
                needs_kernel=False)
    suite.check(6, f"trees of ROUND_TRIP_EXTRA's other {len(X.ROUND_TRIP_EXTRA) - 4}, "
                "ROUND_TRIP_SCHEMAS and ROUND_TRIP_GRAMMAR",
                lambda: tree_problems([(k, s, SIG, t) for k, s, t in X.ROUND_TRIP_EXTRA[4:]]
                                      + [(k, s, SIG, t) for k, s, t in X.ROUND_TRIP_SCHEMAS]
                                      + X.ROUND_TRIP_GRAMMAR),
                needs_kernel=False)
    suite.check(6, "PRINT_EXACT: Neg bases and operands keep their brackets",
                print_exact_problems, needs_kernel=False)
    suite.check(6, f"PARSE_REFUSALS: {len(X.PARSE_REFUSALS)} refused by code, "
                "undeclared symbols among them",
                lambda: refusal_problems(X.PARSE_REFUSALS, T.parse_term),
                needs_kernel=False)
    suite.check(6, f"PARSE_REFUSALS_JUDGEMENT: {len(X.PARSE_REFUSALS_JUDGEMENT)} "
                "misplaced infinities",
                lambda: refusal_problems(X.PARSE_REFUSALS_JUDGEMENT, T.parse_judgement),
                needs_kernel=False)
    suite.check(6, f"the suite's own parse refusals: {sum(map(len, SUITE_PARSE_REFUSALS.values()))} "
                "GRAMMAR.md §1 codes P1 names nowhere, and goal-level offsets (D16)",
                suite_parse_refusal_problems)
    suite.check(6, "ECHO_NONCANONICAL is echoed from the tree, not the input",
                echo_noncanonical_problems)

    print("\nPlanted bugs (each in a child process)")
    suite.check(3, "control: the child, unpatched, finds nothing", control_problems)
    for name, bug in X.PLANTED_BUGS.items():
        suite.check(3, f"{name}: caught at {len(bug['caught_by'])} location(s)",
                    lambda n=name, b=bug: planted_problems(n, b))
    print("\nDefinedness mutations (E26; each in a child process)")
    results = mutation_results() if K is not None else {}
    for name, m in X.DEFINEDNESS_MUTATIONS.items():
        suite.check(3, f"{name}: {m['mutation']}; caught at {len(m['caught_by'])} "
                    "location(s)", lambda n=name, m=m: mutation_problems(m, results[n]))
    suite.check(3, "the unmutated run is clean afterwards", clean_after_problems)

    print("\nUnit tests (a child process)")
    suite.check(UNIT, UNIT_TEXT, unit_test_problems, needs_kernel=False)

    print("\nSummary")
    for item, text in [*ITEMS.items(), (UNIT, UNIT_TEXT)]:
        rows = [r for r in suite.rows if r[0] == item]
        bad = sum(bool(r[2]) for r in rows)
        state = "PASS" if rows and not bad else "FAIL"
        name = "" if item == UNIT else f"item {item}: "
        print(f"  {state}  {name}{text} ({len(rows) - bad}/{len(rows)} checks)")
    failed = suite.failed()
    print(f"\n{'PASS' if not failed else 'FAIL'}: {len(suite.rows) - len(failed)} of "
          f"{len(suite.rows)} checks passed")
    print("\nVerdicts")
    for name in X.PROOFS:
        run = runs.get(name)
        if run is None or run.n is None:
            why = "the kernel did not import" if K is None else "did not close"
            print(f"  {name:<14} ({why})")
        else:
            print(f"  {name:<14} {K.report(run.state)}")
    return 1 if failed else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["--plant"] and len(sys.argv) == 3:
        sys.exit(child(sys.argv[2]))
    if sys.argv[1:2] == ["--mutate"] and len(sys.argv) == 3:
        sys.exit(child(sys.argv[2], "mutate"))
    if sys.argv[1:] == ["--control"]:
        sys.exit(child(None, "control"))
    if sys.argv[1:2] == ["--backstop"] and len(sys.argv) == 3:
        sys.exit(backstop_child(sys.argv[2]))
    if sys.argv[1:2] == ["--isolate"] and len(sys.argv) == 3:
        sys.exit(isolated_child(sys.argv[2]))
    sys.exit(main())
