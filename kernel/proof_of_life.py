"""The proof-of-life's done script, and the kernel's regression suite.

    python3 kernel/proof_of_life.py                 run every Done-when check
    python3 kernel/proof_of_life.py --plant NAME    one planted bug (a child)
    python3 kernel/proof_of_life.py --mutate NAME   one definedness mutation (a child)
    python3 kernel/proof_of_life.py --control       the same child, unpatched
    python3 kernel/proof_of_life.py --backstop NAME one closing check_goal, reached through a seam (a child)
    python3 kernel/proof_of_life.py --isolate NAME  one E26 (b) seam weakened alone (a child)
    python3 kernel/proof_of_life.py --s0-seam NAME  the problem files under one P1 seam (a child)
    python3 kernel/proof_of_life.py --discharge-plant NAME  one discharge planted bug (a child)
    python3 kernel/proof_of_life.py --discharge-control     the same child, unpatched
    python3 kernel/proof_of_life.py --int-subst NAME   one int_subst planted bug or re-traced seam (a child)
    python3 kernel/proof_of_life.py --int-subst-control   the same child, unpatched
    python3 kernel/proof_of_life.py --consolidation NAME  one int_flip, E53, E54 or E56 planted bug (a child)
    python3 kernel/proof_of_life.py --consolidation-control  the same child, unpatched

It asserts every item of WHAT.md's "Done when" against p1_expected.py, which
was written before the kernel and is never changed to fit it. The header
prints the protection in force, handles for facts and the sentinel for
proof states, with the reason the sentinel is enough for states. It was written
from kernel/ARCHITECTURE.md, the skeletons' signatures and p1_expected.py
alone, not from the kernel's code, so it tests the contract rather than
mirroring the implementation.

  1  proves P1.1, its fallback, P1.2, P1.2-alt and P1.1-sheet (in PROOFS
     since E52, ROUTE['P1.1']): every step accepted, each goal_after as a
     tree, the theorem, N and the verdict string;
  2  every step's obligation list (key, sources, status, tag, reason, new),
     deriv's trace and output, the final tracker, and no admission tagged
     none; also MATCH_ACCEPTS, DEFINEDNESS_CASES (E26: installation's and
     the close's lists, the final tracker, the report exactly), OCCURRENCE_CASE
     and the pinned entries, and
     the suite's own cases for what P1's data masks: field's divisors in
     atom arguments, ftc's charge of F's formers, emission placement, and
     TAG_RULES read both ways;
  3  each PLANTED_BUGS mutation, each DEFINEDNESS_MUTATIONS one (both as
     DISCHARGE_PLANTED_BUGS and DISCHARGE_MUTATION_CHANGES re-trace them),
     and each DISCHARGE_NEW_PLANTED_BUGS one, patched into a child process
     through the seams of ARCHITECTURE.md §7, is caught at every
     `caught_by` location, with N as the data gives it;
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
     E27's evaluated-form check (each e27 refusal's code, residual subterm
     as a tree and message from E27_MESSAGES, its clause through
     schema.evaluated_offence, the ordering case refused by the check
     first, and every EVALUATED_ACCEPTS value closing by refl),
     each FORGERIES case by its
     accept rule, and the review's trust cases:
     hand-built trees, vars() writes, a report that fails closed, a
     read-only cite library and deriv rule table;
  6  the echo of each goal, ROUND_TRIP, the S-expression trees, PRINT_EXACT
     and the parse refusals.
  7  stage 0's problem files S1-S3 (WHAT.md "Start here"), read by the
     untrusted kernel/loader.py and driven through install() and step(),
     against kernel/problems/stage0/expected.py, written by hand before
     they ran: the file against its data, the echo, each step's goal and
     obligation list (prop, dom, sources, status, tag, new), deriv's trace,
     the final tracker, N, the verdict, the theorem and answer, the entries
     used, the loader against a direct drive, a math-module check, and each
     of its WRONG_ANSWERS refused with its code and residual (S2-W3 and
     S3-W3's E27 residual compared as a tree, with its message). Also the four
     stage-0 entries pinned in entries.py, and the tagger's sign facts
     against ENTRIES.
  S  int_subst (p1_expected section 12, INT_SUBST_SWITCH): every
     INT_SUBST_ACCEPTS case with its continuation, and every
     INT_SUBST_BAD_MOVES case by code, message and residual; its planted
     bugs and the three re-traced seams run under item 3, and stage 1's
     problem files (stage1/SUB1, S2R, SUB2) under item 7, with their own
     floor. P1.1-sheet, staged here until E52, is in PROOFS now.
  C  the consolidation (p1_expected sections 13-14, CONSOLIDATION_SWITCH,
     the constant CONSOLIDATED below): CONSOLIDATION_ENTRIES pinned, E27's
     reading of pyth and pyth_cos, every INT_FLIP_ACCEPTS and E56_ACCEPTS
     case with its continuation, every INT_FLIP_BAD_MOVES and E56_BAD_MOVES
     case; E53's and E54's checker cases are item D's, QC1
     (problems/consolidation/) item 7's, with its own floor and its two
     wrong answers, and CONSOLIDATION_PLANTED_BUGS and E56_PLANTED_BUGS item
     3's, with E56_CHANGES, CONSOLIDATION_CHANGES and P1_1_SHEET_TRACES
     applied to every table they name.
  D  discharge's parts (p1_expected section 11), called directly as well
     as through kernel._emit, with E49's sqrt_nonneg label: the pinned sqrt_zero
     and cos_zero, every certificate the data gives accepted with its tag
     and proposed by the search, every must-reject certificate rejected for
     its reason, every must-accept neighbour, every decided-false message,
     every undecided admission, and DISCHARGE_PROPERTY_TEST, all from
     test_discharge.py. The E27 cases are asserted as DISCHARGE_E27_CHANGES
     switches them, since entries.py now holds cos_zero and sqrt_zero.

Discharge is wired into kernel._emit (DISCHARGE_SWITCH (2), the constant
DISCHARGE_WIRED below): items 1-7 assert the post-discharge tables, each
obligation's reason and certificate, the re-traced cases (decided-false
refusals by code and message) and the re-traced planted bugs and mutations.
The pre-discharge tables stay in the data files as the stub phase's record.

It also runs the unit tests (test_field.py, test_grammar.py,
test_discharge.py) in a child process, as one check of its own beside items 1-6: field's planted bugs
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
import itertools
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
    import schema as SC
    import tagger as TG
    KERNEL_ERROR = None
except Exception as e:  # noqa: BLE001 -- reported, never swallowed
    DV = EN = FD = K = SC = TG = None
    KERNEL_ERROR = "".join(traceback.format_exception_only(type(e), e)).strip()


def _import_stage0():
    """Item 7's two imports, apart from the kernel's so that items 1-6 run
    whatever they do: the untrusted loader, and the problem files' expected
    data, which is loaded by path because kernel/problems is not a package.
    Only this script imports the data; no kernel file does."""
    import importlib.util
    import loader
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "problems", "stage0", "expected.py")
    spec = importlib.util.spec_from_file_location("stage0_expected", path)
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    return loader, data, os.path.dirname(path)


try:
    LD, S0, STAGE0_DIR = _import_stage0()
    STAGE0_ERROR = None
except Exception as e:  # noqa: BLE001 -- reported by every item-7 check
    LD = S0 = STAGE0_DIR = None
    STAGE0_ERROR = "".join(traceback.format_exception_only(type(e), e)).strip()

# The discharge checks called directly: test_discharge.py holds them, and
# this script runs them one case at a time (item D), and its property test
# under the discharge planted bugs (item 3). Imported apart, so
# that items 1-7 run whatever it does.
try:
    import test_discharge as TD
    DISCHARGE_ERROR = None
except Exception as e:  # noqa: BLE001 -- reported by every item-D check
    TD = None
    DISCHARGE_ERROR = "".join(traceback.format_exception_only(type(e), e)).strip()

SIG = X.SIG
ITEMS = {
    1: "proves P1.1 == 2 and P1.2 in both forms",
    2: "obligation lists, domains and tags",
    3: "fails on the planted bugs",
    4: "rejects wrong answers, asserting the residual",
    5: "refuses bad moves and forgeries",
    6: "round-trips the parser, echoes each goal",
    7: "problem files S1-S3 as stage0/expected.py states them",
    "D": "discharge's checkers, search and refutation, called directly",
    "S": "int_subst (p1_expected section 12): the accepted and refused moves",
    "C": "the consolidation (p1_expected sections 13-14): int_flip, E56's "
         "orientation, E54's entries",
    "R": "regularity (p1_expected section 17): the Int and D formers, the atom "
         "algebra, the refusals",
    "P": "int_parts and ftc at an occurrence (p1_expected section 19)",
    "I": "int_improper, limits.py and the sign node (p1_expected section 20)",
    "T": "trig_norm, field's ordered facts and the trig entries (p1_expected "
         "section 22)",
    "L": "order goals, taylor_lagrange, bound and C^k (p1_expected section 25)",
    "U": "verify, hyperbolic derivatives and unit 00's goals (p1_expected "
         "section 26)",
    "G": "field reads an atom's argument up to exact cancellation "
         "(p1_expected section 27)",
    "K": "strict Taylor bounds and bound's scale (p1_expected section 28)",
    "Q": "clearing a denominator of certified sign (p1_expected section "
         "29)",
    "O": "assumptions on declared functions and the ODE rules (p1_expected "
         "section 30)",
}
UNIT, UNIT_TEXT = "unit", ("unit tests: test_field.py, test_grammar.py, "
                           "test_discharge.py")  # beside 1-6
MAX_SHOWN = 12  # detail lines printed under one failed check


def _e27_switched():
    """BAD_MOVES and EVALUATED_ACCEPTS as DISCHARGE_E27_CHANGES gives them.
    DISCHARGE_SWITCH (1) pins cos_zero and sqrt_zero in entries.py, and E27
    reads entries.ENTRIES, so the E27 cases switch in the same commit:
    e27_no_entry_in_force (cos 0 accepted) leaves EVALUATED_ACCEPTS,
    e27_goal_lhs_before_close is refused at cos 0 naming cos_zero, and
    e27_cos_zero and e27_sqrt_zero join BAD_MOVES. Every other case is
    p1_expected's as it stands."""
    ch = X.DISCHARGE_E27_CHANGES
    moves = [dict(b, e27=ch["BAD_MOVES_replace"][b["id"]]["e27"])
             if b["id"] in ch["BAD_MOVES_replace"] else b for b in X.BAD_MOVES]
    imp = X.IMPROPER_E27_CHANGES  # atan_zero (E80), the same way
    gone = ch["EVALUATED_ACCEPTS_remove"] + imp["EVALUATED_ACCEPTS_remove"]
    accepts = [c for c in X.EVALUATED_ACCEPTS if c["id"] not in gone]
    return (moves + list(ch["BAD_MOVES_add"]) + list(imp["BAD_MOVES_add"]),
            accepts)


BAD_MOVES, EVALUATED_ACCEPTS = _e27_switched()

# TRIG_NORM_SWITCH: QC1-W1 leaves the consolidation's wrong answers (E88);
# trig_checks asserts its move accepted.
CONSOLIDATION_WRONG_ANSWERS = [] if S0 is None else [
    w for w in S0.CONSOLIDATION_WRONG_ANSWERS
    if w["id"] not in X.TRIG_NORM_SWITCH["CONSOLIDATION_WRONG_ANSWERS_remove"]]

# DISCHARGE_SWITCH (2): the one constant. With discharge wired into
# kernel._emit, the suite asserts p1_expected's and stage 0's post-discharge
# tables (DISCHARGE_OBLIGATIONS, DISCHARGE_FINAL_TRACKER, DISCHARGE_ADMISSIONS,
# DISCHARGE_VERDICTS), each obligation's reason and certificate, and the
# re-traced cases, planted bugs and mutations. The pre-discharge tables stay
# in both data files as the stub phase's record and are no longer asserted.
DISCHARGE_WIRED = True
if DISCHARGE_WIRED:
    OBLIGATIONS, FINAL = X.DISCHARGE_OBLIGATIONS, X.DISCHARGE_FINAL_TRACKER
    ADMISSIONS, VERDICTS = X.DISCHARGE_ADMISSIONS, X.DISCHARGE_VERDICTS
else:
    OBLIGATIONS, FINAL = X.EXPECTED_OBLIGATIONS, X.FINAL_TRACKER
    ADMISSIONS, VERDICTS = X.ADMISSIONS, X.VERDICTS
# FORGERY_STATE's tracker, derived from FINAL exactly as p1_expected derives
# TRACKER_AT_FORGERY_STATE from FINAL_TRACKER: P1.2's final tracker without
# the two keys s9 mints.
TRACKER_AT_FORGERY_STATE = [ob for ob in FINAL["P1.2"]
                            if ob[0] not in ("3*sqrt 3 # 0", "2 > 0")]


def _turn(obs, table):
    """A per-step list (6-tuples) or final tracker (4-tuples) with each key
    `table` names given its (status, tag): section 11b's rule, "a case not
    named here keeps every expected value, with each admission it lists
    that DISCHARGE_* names turned DISCHARGED"."""
    out = []
    for ob in obs:
        hit = table.get((ob[0], ob[1]))
        if hit is None:
            out.append(ob)
        elif len(ob) == 6:
            out.append((ob[0], ob[1], ob[2], hit[0], hit[1], ob[5]))
        else:
            out.append((ob[0], ob[1], hit[0], hit[1]))
    return out


def _cases_switched():
    """MATCH_ACCEPTS, DEFINEDNESS_CASES, OCCURRENCE_CASE and the BAD_MOVES
    additions as section 11b re-traces them under DISCHARGE_RULE. Each case
    gains `certificates` ({(prop, dom): certificate}, the data's, where a
    key discharged by a §5.3 method needs one) and `reasons` where the data
    names an admission's reason. A refused case gains `refusal`, `at` and
    `message` (DECIDED_FALSE_MESSAGES' template and parts)."""
    match, defn = [], []
    for c in X.MATCH_ACCEPTS:
        table = X.DISCHARGE_MATCH_ACCEPTS.get(c["id"], {})
        turned = {pd: (X.DISCHARGED, tag) for pd, (tag, _) in table.items()}
        match.append(dict(c, goal_emits=_turn(c["goal_emits"], turned),
                          emits=_turn(c["emits"], turned),
                          certificates={pd: cert for pd, (_, cert) in table.items()}))
    for c in X.DEFINEDNESS_CASES:
        d = X.DISCHARGE_DEFINEDNESS_CASES.get(c["id"])
        if d is None:  # literal where it emits (E7), and unchanged
            defn.append(dict(c, certificates={}))
        elif "refusal" in d:
            defn.append(dict(c, refusal=d["refusal"], at=d["at"], message=d["message"]))
        else:
            turned = {(o[0], o[1]): (o[3], o[4]) for o in d["goal_emits"]}
            turned.update({(f[0], f[1]): (f[2], f[3]) for f in d["final"]})
            defn.append(dict(c, goal_emits=d["goal_emits"],
                             emits=_turn(c["emits"], turned), final=d["final"],
                             report=d["report"],
                             certificates=d.get("certificates", {})))
    oc, doc = X.OCCURRENCE_CASE, X.DISCHARGE_OCCURRENCE_CASE
    occurrence = dict(oc, goal_emits=doc["goal_emits"],
                      goal_certificates=doc["goal_certificates"],
                      all=dict(oc["all"], refusal=doc["all"]["refusal"],
                               message=doc["all"]["message"]),
                      one=dict(oc["one"], emits=doc["one"]["emits"],
                               certificates=doc["one"]["certificates"]))
    return match, defn, occurrence


# F3_ROOTS_CHANGES applied (E50, REVIEW_SWITCH), as test_discharge.py
# applies them for item D.
_ROOTS = X.F3_ROOTS_CHANGES
DISCHARGE_UNDECIDED = [c for c in X.DISCHARGE_UNDECIDED
                       if c["id"] not in _ROOTS["DISCHARGE_UNDECIDED_remove"]] \
    + list(X.F3_ROOTS_UNDECIDED)
DISCHARGE_BAD_MOVES_ADDED = list(X.DISCHARGE_BAD_MOVES_ADDED) \
    + list(_ROOTS["DISCHARGE_BAD_MOVES_ADDED_add"])
# The review's three test-gap cases join section 12's tables (REVIEW_SWITCH).
SUBST_ACCEPTS = list(X.INT_SUBST_ACCEPTS) + list(X.REVIEW_ACCEPTS)
SUBST_BAD_MOVES = list(X.INT_SUBST_BAD_MOVES) + list(X.REVIEW_BAD_MOVES)

if DISCHARGE_WIRED:
    MATCH_ACCEPTS, DEFINEDNESS_CASES, OCCURRENCE_CASE = _cases_switched()
    BAD_MOVES = [dict(b, **{k: X.DISCHARGE_BAD_MOVES_CHANGED[b["id"]][k]
                            for k in ("refusal", "at", "message")})
                 if b["id"] in X.DISCHARGE_BAD_MOVES_CHANGED else b
                 for b in BAD_MOVES] + list(DISCHARGE_BAD_MOVES_ADDED) \
        + list(X.F3_ROOTS_CASES)  # REVIEW_SWITCH: beside BAD_MOVES_ADDED (E50)
    UNDECIDED = list(DISCHARGE_UNDECIDED)  # with F3_ROOTS_CHANGES applied
    REFUSAL_CODES = {**X.REFUSAL_CODES, **X.REFUSAL_CODES_DISCHARGE,
                     **X.REFUSAL_CODES_INT_SUBST}  # INT_SUBST_SWITCH
else:
    MATCH_ACCEPTS, DEFINEDNESS_CASES = X.MATCH_ACCEPTS, X.DEFINEDNESS_CASES
    OCCURRENCE_CASE, UNDECIDED, REFUSAL_CODES = X.OCCURRENCE_CASE, [], X.REFUSAL_CODES

# CONSOLIDATION_SWITCH (p1_expected sections 13 and 14): the one constant.
# With int_flip, E56's one orientation rule, E53's non-strict sign product
# and E54's entries built, the suite merges P1.1-sheet into PROOFS
# (P1_1_SHEET_JOIN, E52), applies E56_CHANGES and CONSOLIDATION_CHANGES to
# the tables they name, and asserts sections 13 and 14's cases (item C),
# planted bugs (item 3) and QC1 (item 7).
CONSOLIDATED = True
J = X.P1_1_SHEET_JOIN
E56 = X.E56_CHANGES
SHEET = "P1.1-sheet"
if CONSOLIDATED:
    PROOFS = {**X.PROOFS, SHEET: J["PROOFS"]}
    OBLIGATIONS = {**OBLIGATIONS, SHEET: J["DISCHARGE_OBLIGATIONS"]}
    FINAL = {**FINAL, SHEET: J["DISCHARGE_FINAL_TRACKER"]}
    ADMISSIONS = {**ADMISSIONS, SHEET: J["DISCHARGE_ADMISSIONS"]}
    VERDICTS = {**VERDICTS, SHEET: X.VERDICT.format(n=J["DISCHARGE_ADMISSIONS"])}
    ANSWERS = {**X.ANSWERS, SHEET: J["ANSWERS"]}
    ECHO = {**X.ECHO, SHEET: J["ECHO"]}
    NUMERIC = {**X.NUMERIC, SHEET: J["NUMERIC"]}
    EXPECTED = {**X.DISCHARGE_EXPECTED, SHEET: J["DISCHARGE_EXPECTED"]}
    ROUTE = {**X.ROUTE, **J["ROUTE"]}
    # the sheet leaves INT_SUBST_PROOFS; the int_subst children run it from
    # PROOFS (SUBST_PROOFS: the PROOFS entries int_subst reaches)
    INT_SUBST_PROOFS = {n: p for n, p in X.INT_SUBST_PROOFS.items() if n != SHEET}
    SUBST_PROOFS = (SHEET,)
    # E56_CHANGES and CONSOLIDATION_CHANGES on the case tables
    BAD_MOVES = [dict(b, refusal=E56["DISCHARGE_BAD_MOVES_CHANGED rewrite_under_D_through_Int"]
                      ["new"][1][0], at="install",
                      message=E56["DISCHARGE_BAD_MOVES_CHANGED rewrite_under_D_through_Int"]
                      ["new"][1])
                 if b["id"] == "rewrite_under_D_through_Int" else b
                 for b in BAD_MOVES if b["id"] != "decided_false_reversed_range"]
    DISCHARGE_BAD_MOVES_ADDED = [c for c in DISCHARGE_BAD_MOVES_ADDED
                                 if c["id"] != "decided_false_reversed_range"]
    _REVERSED = E56["REVIEW_BAD_MOVES reverse_symbolic_old_range_reversed"]["new"]
    _CC = X.CONSOLIDATION_CHANGES["INT_SUBST_ACCEPTS cos_theta_canonical"]

    def _consolidated_accept(c):
        """cos_theta_canonical as CONSOLIDATION_CHANGES gives it: the goal's
        list, the one changed row, the added certificates, no reasons."""
        if c["id"] != "cos_theta_canonical":
            return c
        row = _CC["emits_change"]
        emits = [row if (e[0], e[1]) == (row[0], row[1]) else e for e in c["emits"]]
        c = dict(c, goal_emits=_CC["goal_emits"], emits=emits,
                 certificates={**c["certificates"], **_CC["certificates_add"]})
        c.pop("goal_reasons", None)
        c.pop("reasons", None)
        return c

    def _moved_accept(b):
        """REVIEW_BAD_MOVES reverse_symbolic_old_range_reversed, which E56
        moves to INT_SUBST_ACCEPTS with its new values."""
        return {"id": b["id"], "goal": b["goal"], "move": b["move"],
                "goal_emits": _REVERSED["goal_emits"],
                "goal_after": _REVERSED["goal_after"], "emits": _REVERSED["emits"],
                "certificates": _REVERSED["certificates"]}

    SUBST_ACCEPTS = [_consolidated_accept(c) for c in SUBST_ACCEPTS] + [
        _moved_accept(b) for b in X.REVIEW_BAD_MOVES
        if b["id"] == "reverse_symbolic_old_range_reversed"]
    _UNDECIDED_NEW = E56["INT_SUBST_BAD_MOVES orientation_undecided"]["new"]
    SUBST_BAD_MOVES = [dict(b, refusal=_UNDECIDED_NEW[0], message=_UNDECIDED_NEW[1])
                       if b["id"] == "orientation_undecided" else b
                       for b in SUBST_BAD_MOVES
                       if b["id"] != "reverse_symbolic_old_range_reversed"]
    REFUSAL_CODES = {c: v for c, v in {**REFUSAL_CODES, **X.REFUSAL_CODES_INT_FLIP,
                                       **X.REFUSAL_CODES_E56}.items()
                     if c != "int-subst-orientation-undecided"}
    MESSAGES = {**{k: v for k, v in X.INT_SUBST_MESSAGES.items()
                   if k != "int-subst-orientation-undecided"},
                **X.INT_FLIP_MESSAGES, **X.E56_MESSAGES}
else:
    PROOFS, ANSWERS, ECHO, NUMERIC = X.PROOFS, X.ANSWERS, X.ECHO, X.NUMERIC
    EXPECTED, ROUTE, INT_SUBST_PROOFS = X.DISCHARGE_EXPECTED, X.ROUTE, X.INT_SUBST_PROOFS
    SUBST_PROOFS, MESSAGES = tuple(X.INT_SUBST_PROOFS), X.INT_SUBST_MESSAGES

# REG_SWITCH (p1_expected section 17, E70): the one constant. With the
# regularity checker, its search and E63 wired into kernel._emit, the Int
# and D formers (E64), ring and field's tree atoms (E66 (1)) and E57's
# relaxation built, the suite asserts REG_OBLIGATIONS, REG_FINAL_TRACKER,
# REG_ADMISSIONS and REG_VERDICTS for PROOFS and the problem files, every
# Reg's certificate, and every case, bad move, forgery and planted bug as
# REG_CASE_CHANGES, REG_BAD_MOVES_CHANGED, REG_E57_CHANGES,
# REG_SUITE_CHANGES, REG_FORGERY_CHANGES and REG_BUG_RETRACE give them. The
# pre-regularity tables stay in the data files as the record.
REGULARITY = True
REG_ACCEPTED_MOVES = []  # BAD_MOVES cases the switch turns into accepts
# Every Reg key's regularity certificate the data gives: the cases', then
# each proof's (a case may hold a proof's key, as sum_second_occurrence).
REG_CERTS = ({**{k: v for p in X.REG_EXPECTED.values() for k, v in p.items()},
              **X.REG_CASE_CERTS} if REGULARITY else {})
# Reg rows the data left without a certificate or an admission, each a gap
# reported by the check that reads it (a data_change_request).
REG_GAPS = []


def _reg_row(row):
    """One expected row under the switch: a pre-regularity Reg row (admitted
    ('reg', ())) turned DISCHARGED with REG_CASE_CERTS' tag, or kept
    ADMITTED with REG_CASE_ADMITTED's; any other row as it is."""
    six = len(row) == 6
    prop, dom = row[0], row[1]
    status, tag = (row[3], row[4]) if six else (row[2], row[3])
    if not REGULARITY or " in C^" not in prop or (status, tag) != (X.ADMITTED, X.T_REG):
        return row
    k = (prop, dom)
    if k in X.REG_CASE_ADMITTED:
        status, tag = X.ADMITTED, X.REG_CASE_ADMITTED[k][0]
    elif k in REG_CERTS:
        status, tag = X.DISCHARGED, REG_CERTS[k][0]
    else:
        REG_GAPS.append(k)
        return row
    return (prop, dom, row[2], status, tag, row[5]) if six else (prop, dom, status, tag)


def _reg_rows(rows, not_new=(), adds=()):
    out = []
    for row in map(_reg_row, rows):
        if (row[0], row[1]) in not_new:
            row = row[:5] + (False,)
        out.append(row)
    return out + list(adds)


def _reg_report(case, lists):
    """The report after the switch by the rule 'its report loses those
    admissions': N counts the distinct keys the case's lists leave
    admitted."""
    status = {}
    for rows in lists:
        for row in rows:
            status[(row[0], row[1])] = row[3] if len(row) == 6 else row[2]
    n = sum(v == X.ADMITTED for v in status.values())
    return X.VERDICT.format(n=n) if n else X.PROVED


def reg_case(table, c, change=None):
    """A case under REG_SWITCH: every Reg row it lists turned as _reg_row
    says; REG_CASE_CHANGES' goal_emits_add, emits_add and then_add rows
    appended, its not_new keys cleared ('goal', 'emits' or a continuation
    step's index) and its certificates added; the report its own new one
    where given, else derived (_reg_report); every admitted Reg key's reason
    REG_CASE_ADMITTED's."""
    if not REGULARITY:
        return c
    ch = change if change is not None else X.REG_CASE_CHANGES.get(table, {}).get(c["id"], {})
    ch = ch if isinstance(ch, dict) else {}
    nn = ch.get("not_new", {})
    c = dict(c)
    lists = []
    if "goal_emits" in c or "goal_emits_add" in ch:
        c["goal_emits"] = _reg_rows(c.get("goal_emits", ()), set(nn.get("goal", ())),
                                    ch.get("goal_emits_add", ()))
        lists.append(c["goal_emits"])
    if "emits" in c:
        c["emits"] = _reg_rows(c["emits"], set(nn.get("emits", ())),
                               ch.get("emits_add", ()))
        lists.append(c["emits"])
    if "then" in c:
        then = []
        for i, st in enumerate(c["then"]):
            st = dict(st, emits=_reg_rows(st.get("emits", ()), set(nn.get(i, ())),
                                          ch.get("then_add", {}).get(i, ())))
            then.append(st)
            lists.append(st["emits"])
        c["then"] = then
    if "final" in c:
        c["final"] = [_reg_row(r) for r in c["final"]]
    if "certificates" in c or "certificates" in ch:
        c["certificates"] = {**c.get("certificates", {}), **ch.get("certificates", {})}
    reasons = dict(c.get("reasons", {}))
    goal_reasons = dict(c.get("goal_reasons", {}))
    for rows, where in ((c.get("goal_emits", ()), goal_reasons),
                        *((rows, reasons) for rows in lists[1:])):
        for row in rows:
            if (row[0], row[1]) in X.REG_CASE_ADMITTED and row[3] == X.ADMITTED:
                where[(row[0], row[1])] = X.REG_CASE_ADMITTED[(row[0], row[1])][1]
    if reasons:
        c["reasons"] = reasons
    if goal_reasons or "goal_reasons" in c:
        c["goal_reasons"] = goal_reasons
    if "report" in ch:
        c["report"] = ch["report"]
    elif "report" in c:
        c["report"] = _reg_report(c, [c["final"]] if "final" in c else lists)
    for name in ("timing_bound",):
        if name in ch:
            c[name] = ch[name]
    return c


if REGULARITY:
    OBLIGATIONS, FINAL = X.REG_OBLIGATIONS, X.REG_FINAL_TRACKER
    ADMISSIONS, VERDICTS = X.REG_ADMISSIONS, X.REG_VERDICTS
    EXPECTED = {p: {**EXPECTED.get(p, {}), **X.REG_EXPECTED.get(p, {})}
                for p in set(EXPECTED) | set(X.REG_EXPECTED)}
    MATCH_ACCEPTS = [reg_case("MATCH_ACCEPTS", c) for c in MATCH_ACCEPTS]
    DEFINEDNESS_CASES = [reg_case("DEFINEDNESS_CASES", c) for c in DEFINEDNESS_CASES]
    _OC = OCCURRENCE_CASE
    OCCURRENCE_CASE = dict(reg_case("OCCURRENCE_CASE", dict(_OC, id="OCCURRENCE_CASE"),
                                    X.REG_CASE_CHANGES["OCCURRENCE_CASE"]),
                           one=reg_case("OCCURRENCE_CASE", dict(_OC["one"], id="one"), {}))
    UNDECIDED = [reg_case("F3_ROOTS_UNDECIDED", c) if c["id"] in
                 X.REG_CASE_CHANGES["F3_ROOTS_UNDECIDED"] else reg_case("DISCHARGE_UNDECIDED", c)
                 for c in UNDECIDED]
    DISCHARGE_BAD_MOVES_ADDED = [reg_case("DISCHARGE_BAD_MOVES_ADDED", c)
                                 for c in DISCHARGE_BAD_MOVES_ADDED]
    _BMC = X.REG_BAD_MOVES_CHANGED
    _SC = X.REG_SUITE_CHANGES

    def _reg_bad_move(b):
        """A BAD_MOVES case under REG_BAD_MOVES_CHANGED and REG_SUITE_CHANGES:
        a new refusal (with its residual and installation list where given),
        or None when it becomes an accepted case (REG_REG_ACCEPTED_MOVES)."""
        b = reg_case("BAD_MOVES", b, X.REG_CASE_CHANGES["DISCHARGE_BAD_MOVES_ADDED"]
                     .get(b["id"], {}))
        ch = _BMC.get(b["id"])
        if b["id"] in ("rewrite_under_D_through_Int_R_former",
                       "rewrite_under_D_through_Int_R_former_ln"):
            return dict(b, refusal="orientation-undecided", at="install",
                        message=("orientation-undecided", {"lo": "1", "hi": "x"}))
        if not isinstance(ch, dict):
            return b
        new = ch["new"]
        if isinstance(new, tuple) and new[0] == "refused":
            b = dict(b, refusal=new[1])
            if "residual" in ch:
                b["residual"], b["compare"] = ch["residual"][0], (ch["residual"][1], ())
            if "goal_emits" in ch:
                b["goal_emits"] = ch["goal_emits"]
            return b
        return None

    for _b in BAD_MOVES:
        _ch = _BMC.get(_b["id"])
        if isinstance(_ch, dict) and isinstance(_ch["new"], dict):
            REG_ACCEPTED_MOVES.append(reg_case("REG_BAD_MOVES_CHANGED", dict(
                {k: v for k, v in _b.items() if k not in ("refusal", "message", "residual",
                                                         "compare", "setup", "e27")},
                **_ch["new"]), {}))
    BAD_MOVES = [nb for nb in map(_reg_bad_move, BAD_MOVES) if nb is not None] \
        + list(X.REG_BAD_MOVES_ADDED)
    _REVIEW_IDS = {c["id"] for c in X.REVIEW_ACCEPTS}
    SUBST_ACCEPTS = [reg_case("REVIEW_ACCEPTS" if c["id"] in _REVIEW_IDS
                              else "INT_SUBST_ACCEPTS", c) for c in SUBST_ACCEPTS]
    SUBST_BAD_MOVES = [reg_case("INT_SUBST_BAD_MOVES", b, {}) for b in SUBST_BAD_MOVES]
    TRACKER_AT_FORGERY_STATE = [ob for ob in FINAL["P1.2"]
                                if ob[0] not in ("3*sqrt 3 # 0", "2 > 0")]

CASES = {"BAD_MOVES": BAD_MOVES, "DEFINEDNESS_CASES": DEFINEDNESS_CASES,
         "MATCH_ACCEPTS": MATCH_ACCEPTS}


def case_certs(case, name="certificates"):
    """A case's certificates as certificate_problem reads them, or None
    before the switch. Under REG_SWITCH every Reg key's certificate the data
    gives (REG_CERTS) is among them."""
    if not DISCHARGE_WIRED:
        return None
    rows = list(case.get(name, {}).items())
    if REGULARITY:
        rows = [(k, c) for k, (_, c) in REG_CERTS.items()] + rows
    return cert_table(rows)


def case_reasons(case):
    return {key(p, d): r for (p, d), r in case.get("reasons", {}).items()}


def _message_field(v):
    """A message part: a GRAMMAR.md string shown after parsing, or, where it
    is not a term ('the lower limit', 'oo'), the text itself."""
    try:
        return T.show(T.parse_term(v, SIG))
    except T.ParseError:
        return v


def expected_message(spec):
    """A refusal's message from its (template, parts): INT_SUBST_MESSAGES',
    INT_FLIP_MESSAGES' and E56_MESSAGES' for those codes (MESSAGES), filled
    with each part shown after parsing,
    else DECIDED_FALSE_MESSAGES' (test_discharge.expected_message)."""
    how, parts = spec
    if how in MESSAGES:
        return MESSAGES[how].format(
            **{k: _message_field(v) for k, v in parts.items()})
    return TD.expected_message(spec)


def residual_problems_of(r, case, parse=None):
    """A case's residual (E14) equal to the refusal's under its `compare`,
    and not zero, where the case gives one."""
    if "residual" not in case or "compare" not in case:
        return []
    if r.residual is None:
        return ["the refusal carries no residual"]
    method = case["compare"][0]
    want = (parse or term)(case["residual"])
    ok, note = equal_by(method, r.residual, want)
    out = [] if ok else [f"residual {show(r.residual)} is not {case['residual']} "
                         f"under {method}{note}"]
    zero, note = equal_by(method, r.residual, T.Num(0))
    if zero or note:
        out.append(f"residual {show(r.residual)} is zero under {method}{note}")
    return out


def refusal_problems_of(r, case):
    """A Refusal against a case's `refusal` code and, when it gives one, its
    decided-false `message`, filled from DECIDED_FALSE_MESSAGES."""
    if not isinstance(r, K.Refusal):
        return [f"not refused: {describe(r)}"]
    out = [] if r.code == case["refusal"] else [f"refused {r.code}: {r.message}"]
    if isinstance(case.get("message"), tuple):  # a (template, parts) message
        want = expected_message(case["message"])
        if r.message != want:
            out.append(f"message {r.message!r}, expected {want!r}")
    return out


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
        if k in ("at", "F", "value", "sub", "lo", "hi", "f"):
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
    """The state after step `through` of PROOFS[proof] (or of
    p1_expected's INT_SUBST_PROOFS[proof]), and the handles bound on the way. Each call is
    a fresh install, so a fresh lineage."""
    p = PROOFS[proof] if proof in PROOFS else X.INT_SUBST_PROOFS[proof]
    st, handles = install(p["goal"], (proof, "goal")), {}
    for s in p["steps"]:
        st = take(st, s["move"], s["args"], handles, (proof, s["id"]))
        if s["id"] == through:
            return st, handles
    raise ValueError(f"{proof} has no step {through!r}")


def keys_of(state):
    return frozenset(o.key for o in state.obligations())


# ---------------------------------------------------------------- comparisons

def expected_reason(status, tag, k, reasons=None):
    """An admission's reason under the switch (E32): the case's own where it
    names one, else REASON_REG for a Reg, REASON_NONE for a key tagged
    none, and REASON_REJECTED otherwise, which no unmutated run produces."""
    if status != X.ADMITTED:
        return None
    if not DISCHARGE_WIRED:
        return X.ADMISSION_REASON
    if reasons and k in reasons:
        return reasons[k]
    if REGULARITY:  # REASON_REG is retired (E60)
        return X.REASON_NONE if tag == X.T_NONE else X.REASON_REJECTED
    return (X.REASON_REG if tag == X.T_REG else
            X.REASON_NONE if tag == X.T_NONE else X.REASON_REJECTED)


def certificate_problem(ob, k, certs):
    """The obligation's certificate against the data's (DISCHARGE_EXPECTED
    and the cases' certificates), compared as DISCHARGE_RULE says; a key the
    data gives no certificate for must carry none. `certs` None: nothing to
    compare."""
    if not DISCHARGE_WIRED or certs is None:
        return None
    want = certs.get(k)
    if want is None:
        return None if ob.certificate is None else \
            f"{ob.certificate!r}, expected no certificate"
    return "; ".join(TD.cert_differences(ob.certificate, TD.cert_of(want))) or None


def cert_table(rows):
    """{key: spec certificate} from ((prop, dom), certificate) pairs."""
    return {key(p, d): c for (p, d), c in rows}


def compare_emitted(miss, proof, sid, expected, emitted, prev_keys, keyf=None,
                    certs=None, reasons=None, with_dom=False):
    """One step's `last.emitted` against its expected list, as a set of keys
    (KEYING). `new` is computed here from the previous state's tracker, never
    taken from the kernel. The locations are PLANTED_BUGS' caught_by shapes:
    (proof, step, prop, dom) for an absent key, (proof, step, prop, what)
    for a key present with a wrong field. `keyf` parses an expected (prop,
    dom); it is `key` unless another data file supplies its own. `certs`
    and `reasons` are the data's certificates and admission reasons for its
    keys (expected_reason, certificate_problem). `with_dom` puts the dom in
    a field's location, (proof, sid, prop, dom, what), the shape
    INT_SUBST_SEAMS names."""
    keyf = keyf or key
    got = {}
    for ob in emitted:
        if ob.key in got:
            miss(2, (proof, sid, "duplicate", T.show(ob.key)),
                 "listed twice in one step's emissions")
        got[ob.key] = ob
    want = set()
    for prop, dom, sources, status, tag, new in expected:
        k = keyf(prop, dom)
        want.add(k)
        ob = got.get(k)
        if ob is None:
            miss(2, (proof, sid, prop, dom), "not emitted")
            continue
        at = (proof, sid, prop, dom) if with_dom else (proof, sid, prop)
        if frozenset(ob.sources) != frozenset(sources):
            miss(2, at + ("sources",),
                 f"{sorted(ob.sources)}, expected {sorted(sources)}")
        if ob.status != status:
            miss(2, at + ("status",),
                 f"{ob.status}, expected {status}")
        if tag_of(ob) != tag:
            miss(2, at + ("tag",), f"{tag_of(ob)}, expected {tag}")
        reason = expected_reason(status, tag, k, reasons)
        if ob.status == status and ob.reason != reason:
            miss(2, at + ("reason",),
                 f"{ob.reason!r}, expected {reason!r}")
        bad = certificate_problem(ob, k, certs) if ob.status == status else None
        if bad:
            miss(2, at + ("certificate",), bad)
        if (k not in prev_keys) != new:
            miss(2, at + ("new",),
                 f"new is {k not in prev_keys}, expected {new}")
    for k, ob in got.items():
        if k not in want:
            miss(2, (proof, sid, "extra", T.show(k)),
                 f"{ob.status} {tag_of(ob)} from {sorted(ob.sources)}")


def tracker_problems(obs, expected, sources=None, keyf=None, certs=None,
                     reasons=None):
    """obligations() against a FINAL_TRACKER-shaped list of (prop, dom,
    status, tag). Returns (location suffix, detail) pairs. An absent key's
    suffix is ((prop, dom),), which is caught_by's FINAL_TRACKER shape.
    `sources`, when given, maps each key to the union of its expected
    sources over the steps (E8: add merges sources)."""
    keyf = keyf or key
    out, got, want = [], {}, set()
    for ob in obs:
        if ob.key in got:
            out.append((("duplicate", T.show(ob.key)), "listed twice"))
        got[ob.key] = ob
    for prop, dom, status, tag in expected:
        k = keyf(prop, dom)
        want.add(k)
        ob = got.get(k)
        if ob is None:
            out.append((((prop, dom),), "absent"))
            continue
        if ob.status != status:
            out.append((((prop, dom), "status"), f"{ob.status}, expected {status}"))
        if tag_of(ob) != tag:
            out.append((((prop, dom), "tag"), f"{tag_of(ob)}, expected {tag}"))
        reason = expected_reason(status, tag, k, reasons)
        if ob.reason != reason:
            out.append((((prop, dom), "reason"), f"{ob.reason!r}, expected "
                        f"{reason!r}"))
        bad = certificate_problem(ob, k, certs) if ob.status == status else None
        if bad:
            out.append((((prop, dom), "certificate"), bad))
        # A key no step's list names has no expected sources: reported, not
        # raised, so the rest of the comparison still prints.
        want_src = frozenset(sources.get(k, ())) if sources is not None else None
        if sources is not None and frozenset(ob.sources) != want_src:
            out.append((((prop, dom), "sources"),
                        f"{sorted(ob.sources)}, expected {sorted(want_src)}"))
    for k, ob in got.items():
        if k not in want:
            out.append((("extra", T.show(k)), f"{ob.status} {tag_of(ob)}"))
    return out


def expected_sources(proof, tb=None):
    out = {}
    for obs in (tb or P1_TABLES).OBLIGATIONS[proof].values():
        for prop, dom, sources, *_ in obs:
            out.setdefault(key(prop, dom), set()).update(sources)
    return out


def multiset_text(c, show_one):
    return ", ".join(f"{show_one(x)}" + (f" x{n}" if n > 1 else "")
                     for x, n in c.items())


def deriv_problems(F, trace, output, d=None):
    """deriv's trace (a multiset of (rule, subterm), and what each firing
    emitted), its output as a tree, and its emissions, against DERIV, or
    against the DERIV-shaped row `d` another data file gives."""
    d = d or DERIV_BY_F[F]
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


def proof_certs(name, tb=None):
    """The certificates DISCHARGE_EXPECTED (or INT_SUBST_EXPECTED) gives for
    a proof's keys."""
    if not DISCHARGE_WIRED:
        return None
    table = (tb or P1_TABLES).EXPECTED
    return cert_table((pd, c) for pd, (_, c) in table[name].items())


class Tables:
    """The tables one family of proofs is asserted against: PROOFS and its
    DISCHARGE_* tables (items 1-2), or INT_SUBST_PROOFS and its INT_SUBST_*
    tables (item S). `deriv(name, step)` is a step's DERIV row."""

    def __init__(self, **kw):
        self.__dict__.update(kw)


def _p1_deriv(name, s):
    """A PROOFS step's DERIV row: an int_subst step's is INT_SUBST_DERIV's,
    keyed (proof, step), since it has no F (P1.1-sheet's s1, E52); an ftc
    step's is DERIV's for its F."""
    if (name, s["id"]) in X.INT_SUBST_DERIV:
        return X.INT_SUBST_DERIV[(name, s["id"])]
    return DERIV_BY_F[s["args"]["F"]]


P1_TABLES = Tables(
    PROOFS=PROOFS, OBLIGATIONS=OBLIGATIONS, FINAL=FINAL, ADMISSIONS=ADMISSIONS,
    VERDICTS=VERDICTS, ANSWERS=ANSWERS, ECHO=ECHO, EXPECTED=EXPECTED,
    deriv=_p1_deriv)
# What int_subst's children run: after E52, P1.1-sheet from PROOFS's tables
# (INT_SUBST_PROOFS keeps no proof); before it, INT_SUBST_PROOFS', whose
# P1.1-sheet echoes as the fallback (the same goal).
SUBST_TABLES = P1_TABLES if CONSOLIDATED else Tables(
    PROOFS=X.INT_SUBST_PROOFS, OBLIGATIONS=X.INT_SUBST_OBLIGATIONS,
    FINAL=X.INT_SUBST_FINAL_TRACKER, ADMISSIONS=X.INT_SUBST_ADMISSIONS,
    VERDICTS=X.INT_SUBST_VERDICTS, ANSWERS=X.INT_SUBST_ANSWERS,
    ECHO={"P1.1-sheet": X.ECHO["P1.1-fallback"]}, EXPECTED=X.INT_SUBST_EXPECTED,
    deriv=lambda name, s: X.INT_SUBST_DERIV[(name, s["id"])])


def run_proof(name, strict=True, out=print, tb=None):
    """Install PROOFS[name], echo it, run its steps, and compare everything
    with p1_expected. `strict` adds what holds only of an unmutated run: the
    echo checks and no admission tagged none (the tag data's own rule).
    A Mismatch stops the run and is recorded. Any other exception is a
    kernel crash and propagates."""
    run = Run(name)
    try:
        _run_proof(run, strict, out, tb or P1_TABLES)
    except Mismatch as m:
        run.miss(m.item, m.where, m.detail)
    return run


def _run_proof(run, strict, out, tb):
    name, p = run.name, tb.PROOFS[run.name]
    exp = tb.OBLIGATIONS[name]
    certs = proof_certs(name, tb)
    installed = goal(p["goal"])
    st = install(p["goal"], (name, "goal"))
    run.state = st
    # Done-when 6: the echo is printed from the installed tree, before s1.
    echo = T.show_goal(st.goal)
    run.lines.append(echo)
    out(echo)
    if strict:
        if run.lines[0] != tb.ECHO[name]:
            run.miss(6, (name, "echo"), f"{run.lines[0]!r}, expected {tb.ECHO[name]!r}")
        if T.parse_goal(echo, SIG) != st.goal:
            run.miss(6, (name, "echo", "reparse"), "does not parse back to the tree")
    if st.goal != installed or st.original != installed:
        run.miss(1, (name, "goal", "installed"), f"got {show(st.goal)}")
    if st.last.move != "install":
        run.miss(1, (name, "goal", "move"), f"last.move is {st.last.move!r}")
    compare_emitted(run.miss, name, "goal", exp["goal"], st.last.emitted,
                    frozenset(), certs=certs)
    seen = list(st.last.emitted)
    handles = {}
    for s in p["steps"]:
        prev = st
        st = take(prev, s["move"], s["args"], handles, (name, s["id"]))
        run.state = st
        _check_step(run, s, prev, st, tb)
        compare_emitted(run.miss, name, s["id"], exp[s["id"]], st.last.emitted,
                        keys_of(prev), certs=certs)
        seen += st.last.emitted
    obs = st.obligations()
    for suffix, detail in tracker_problems(obs, tb.FINAL[name],
                                           expected_sources(name, tb), certs=certs):
        run.miss(2, ("FINAL_TRACKER", name) + suffix, detail)
    if strict:  # WHAT.md: an admission tagged none fails the milestone
        nones = {T.show(o.key) for o in seen + list(obs)
                 if o.status == X.ADMITTED and o.tag[0] == "none"}
        for k in sorted(nones):
            run.miss(2, ("NONE_TAG", name, k), "admitted and tagged none")
    if st.goal is not None:
        raise Mismatch(1, (name, "closed"), f"goal still open: {show(st.goal)}")
    run.n = sum(o.status == X.ADMITTED for o in obs)
    if run.n != tb.ADMISSIONS[name]:
        run.miss(1, ("N", name), f"{run.n} admissions, expected {tb.ADMISSIONS[name]}")
    verdict = K.report(st)
    if verdict != tb.VERDICTS[name]:
        run.miss(1, ("VERDICT", name), f"{verdict!r}, expected {tb.VERDICTS[name]!r}")
    if st.theorem != goal(p["theorem"]):
        run.miss(1, ("THEOREM", name), f"got {show(st.theorem)}")
    if T.instantiate(installed, term(tb.ANSWERS[name])) != goal(p["theorem"]):
        run.miss(1, ("ANSWER", name), "ANSWERS disagrees with the theorem")


def _check_step(run, s, prev, st, tb):
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
    if s["move"] in ("ftc", "int_subst"):
        d = tb.deriv(run.name, s)
        for what, detail in deriv_problems(d["F"], last.trace, last.output, d):
            run.miss(2, where + (what,), detail)


# ---------------------------------------------------------------- the checks

# REG_SWITCH locations the rules do not reach as the data writes them, each
# left failing with its evidence until the data changes (a
# data_change_request): a failing check whose label or detail names one of
# these gets the note.
REG_DATA_CHANGE_REQUESTS = {
    "non_monotone_divergent":
        "data_change_request (regularity): INT_SUBST_BAD_MOVES non_monotone_divergent's "
        "message. Step 13's forward C^0 premise Reg(1/t^2, 0, [-1, 1]) is emitted "
        "before step 14's new-integral formers (INT_SUBST_RULE's order), and a Reg "
        "now goes through REG_DISCHARGE_ORDER, whose E63 refutes it through its "
        "div side t^2 # 0 at t = 0; so the refusal's message is "
        "_reg_undefined('1/t^2 in C^0([-1, 1])', 't^2 # 0 @ [-1, 1]', the old "
        "_point message), not the bare point message REG_BAD_MOVES_CHANGED's "
        "'unchanged, re-traced' (INT_SUBST_BAD_MOVES) assumed",
    "flip_sum_second_occurrence":
        "data_change_request (regularity): REG_CASE_CHANGES INT_FLIP_ACCEPTS "
        "flip_sum_second_occurrence adds the row 0 <= pi/2 (orient, DISCHARGED, "
        "T_LINEAR_PI) to goal_emits with no certificate, and the case has none: "
        "its 'certificates' needs ('0 <= pi/2', 'true'): _PI_HALF, as every "
        "other case adding that row has (the rule 'every added row ... has its "
        "certificate in certificates')",
    "tracker_drops_one":
        "data_change_request (regularity): PLANTED_BUGS tracker_drops_one's "
        "'step_lists_changed': False no longer holds. REG_BUG_RETRACE says the "
        "wrapper drops every emission of 1/(1 + x^3) in C^0([0, 1]), now first "
        "emitted at installation; so at P1.2's and P1.2-alt's s2 the key is not "
        "in the tracker and its row reads new, where REG_NOT_NEW makes it not "
        "new: the step lists change at (P1.2|P1.2-alt, s2, '1/(1 + x^3) in "
        "C^0([0, 1])', 'new'). Those two are new catch locations",
    "int_subst_no_orientation":
        "data_change_request (regularity): INT_SUBST_PLANTED_BUGS "
        "int_subst_no_orientation's catch at INT_SUBST_BAD_MOVES "
        "orientation_undecided no longer fires. With step 8's orientation "
        "skipped, step 14's new integral Int[t = 0 .. 1/y] still owes its "
        "former (E64), which uses its range, so E68 decides the order there and "
        "refuses 'orientation-undecided' naming 0 and 1/y, the case's own code "
        "and message. The mutation stays caught at its other two locations",
    "rewrite_tree_branch_skips_E57":
        "data_change_request (regularity): REVIEW2_PLANTED_BUGS "
        "rewrite_tree_branch_skips_E57's location (E57_BAD_MOVES, pyth_erases_D) "
        "no longer exists: REG_E57_CHANGES moves pyth_erases_D to "
        "REG_E57_ACCEPTS, where the D passes step 2a on every branch, so the "
        "mutation changes nothing there. It stays caught at "
        "pyth_erases_divergent_Int",
}


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
        if problems and REGULARITY:
            text = label + " " + " ".join(map(str, problems))
            problems = list(problems) + [v for k, v in REG_DATA_CHANGE_REQUESTS.items()
                                         if k in text]
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
    # P1's entries must be there. Stage 0's four are pinned by item 7, so a
    # broken stage-0 import cannot fail this item.
    want = set(X.NAMED_ENTRIES) | set(X.ADDED_ENTRIES)
    if not want <= set(EN.ENTRIES):
        out.append(f"entries lack {sorted(want - set(EN.ENTRIES))}")
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

    certs = case_certs(case)
    st = install(case["goal"], (case["id"], "goal"))
    compare_emitted(miss, case["id"], "goal", case["goal_emits"], st.last.emitted,
                    frozenset(), certs=certs)
    move, args = case["move"]
    st2 = take(st, move, args, {}, (case["id"], move))
    if st2.goal != goal(case["goal_after"]):
        out.append(f"goal_after: got {show(st2.goal)}")
    compare_emitted(miss, case["id"], move, case["emits"], st2.last.emitted,
                    keys_of(st), certs=certs)
    return out


def occurrence_problems(which):
    """OCCURRENCE_CASE: installation's list where the data gives it, then the
    rewrite, accepted with its lists or refused with its message."""
    c = OCCURRENCE_CASE[which]
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(OCCURRENCE_CASE["goal"], ("OCCURRENCE_CASE", "goal"))
    if "goal_emits" in OCCURRENCE_CASE:
        compare_emitted(miss, "OCCURRENCE_CASE", "goal", OCCURRENCE_CASE["goal_emits"],
                        st.last.emitted, frozenset(),
                        certs=case_certs(OCCURRENCE_CASE, "goal_certificates"))
    move, args = c["move"]
    if "refusal" in c:
        before = st.obligations()
        out += refusal_problems_of(K.step(st, move, build_args(args, {})), c)
        if st.obligations() != before:
            out.append("the refused step changed the state (E13)")
        return out
    st2 = take(st, move, args, {}, ("OCCURRENCE_CASE", which))
    if st2.last.occurrences != c["occurrences"]:
        out.append(f"occurrences {st2.last.occurrences}, expected {c['occurrences']}")
    if st2.goal != goal(c["goal_after"]):
        out.append(f"goal_after: got {show(st2.goal)}")
    compare_emitted(miss, "OCCURRENCE_CASE", which, c["emits"], st2.last.emitted,
                    keys_of(st), certs=case_certs(c))
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

    if case.get("at") == "install":  # decided false at installation (E33)
        return refusal_problems_of(K.install(goal(case["goal"])), case)
    certs = case_certs(case)
    st = install(case["goal"], (case["id"], "goal"))
    compare_emitted(miss, case["id"], "goal", case["goal_emits"], st.last.emitted,
                    frozenset(), certs=certs)
    move, args = case["move"]
    st2 = take(st, move, args, {}, (case["id"], move))
    compare_emitted(miss, case["id"], move, case["emits"], st2.last.emitted,
                    keys_of(st), certs=certs)
    out += [fmt((case["id"], "final") + sfx, d)
            for sfx, d in tracker_problems(st2.obligations(), case["final"],
                                           certs=certs)]
    if st2.goal is not None:
        out.append(f"the goal is still open: {show(st2.goal)}")
    if K.report(st2) != case["report"]:
        out.append(f"report {K.report(st2)!r}, expected {case['report']!r}")
    if st2.theorem != goal(case["theorem"]):
        out.append(f"theorem {show(st2.theorem)}, expected {case['theorem']}")
    return out


def undecided_problems(case):
    """DISCHARGE_UNDECIDED: installed, its installation list asserted with
    each admission's tag and reason; not closed."""
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    st = install(case["goal"], (case["id"], "goal"))
    compare_emitted(miss, case["id"], "goal", case["goal_emits"], st.last.emitted,
                    frozenset(), certs={}, reasons=case_reasons(case))
    return out


def route_problems(runs):
    """P1_1_SHEET_JOIN's ROUTE: P1.1's route is P1.1-sheet, P1.2's is P1.2;
    each names a PROOFS entry that ran to a close here, with ANSWERS' value
    for the problem it routes."""
    out = [] if ROUTE == {"P1.1": SHEET, "P1.2": "P1.2"} else [f"ROUTE is {ROUTE}"]
    for problem, proof in ROUTE.items():
        run = runs.get(proof)
        if proof not in PROOFS or run is None or run.n is None:
            out.append(f"{problem}: its route {proof} did not close")
        elif term(ANSWERS[proof]) != term(X.ANSWERS[problem]):
            out.append(f"{problem}: its route closes with {ANSWERS[proof]}, "
                       f"ANSWERS says {X.ANSWERS[problem]}")
    return out


def numeric_problems(name):
    """A math-module check that the answer is the integral: NUMERIC against
    the theorem's right side evaluated, and against Simpson's rule on the
    goal's integral. It shares no code with the kernel."""
    base = "P1.1" if name.startswith("P1.1") else "P1.2"
    want = NUMERIC[base]
    out = []
    answer = value(goal(PROOFS[name]["theorem"])[0].rhs)
    if abs(answer - want) > 1e-12 * max(1.0, abs(want)):
        out.append(f"the answer is {answer!r}, NUMERIC says {want!r}")
    integral = value(goal(PROOFS[name]["goal"])[0].lhs)
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
    # field.py's power bound (POWER_BOUND, BITS_BOUND, TERMS_BOUND): a literal
    # power ring or norm_num would expand without end, or into a number no
    # message can print, is refused. The skeptic's two: int_subst's upper
    # image 2^20000 raised ValueError from the residual's message, and close
    # meets the same power in its check.
    {"id": "power_beyond_bound_int_subst", "goal": "Int[x = 0 .. 1] x == ?A",
     "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^20000", "new_var": "t",
                            "lo": "0", "hi": "2", "check": "ring", "facts": []}),
     "refusal": "power-too-large"},
    {"id": "power_beyond_bound_close", "goal": "x == ?A @ x > 0", "setup": [],
     "move": ("close", {"value": "2^20000", "check": "ring", "facts": []}),
     "refusal": "power-too-large"},
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
    {"id": "goal_not_equation", "goal": "x # 0", "setup": [],  # E96: x > 0 installs
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
if REGULARITY:  # REG_SUITE_CHANGES, the suite's own cases under the switch
    SUITE_BAD_MOVES = [
        dict(b, refusal="shadowing") if b["id"] == "rewrite_inst_shadows" else
        dict(b, refusal="orientation-undecided", at="install",
             message=("orientation-undecided", {"lo": "1", "hi": "x"}))
        if b["id"] in ("rewrite_under_D_through_Int_R_former",
                       "rewrite_under_D_through_Int_R_former_ln") else b
        for b in SUITE_BAD_MOVES]

KERNEL_LOCAL_CODES = ("state-not-minted", "proof-finished", "bad-move", "bad-args",
                      "goal-shape", "ftc-no-integral", "close-no-mvar",
                      "field-fact-shape", "power-too-large")
DIRECT_CODES = ("state-not-minted", "proof-finished")  # unminted_finished_problems


# GRAMMAR.md §1's table: every parse code, each of which some case must name.
GRAMMAR_CODES = (
    "D1-decimal", "implicit-mul", "non-ascii", "D2-deferred", "D3-bare-e",
    "reserved-hint", "D4-not-a-name", "D5-undeclared", "D5-arity",
    "D5-uncalled", "D5-sig-collision", "D5-sig-arity0",
    "D6-ambiguous-app-power", "D6-neg-operand", "D6-app-as-base",
    "D7-int-in-arith", "D8-pow-chain", "D8-neg-exponent", "bound-in-endpoint",
    "shadowing", "D11-bound-and-free", "D13-unnamed-interval", "oo-misplaced",
    "chained-cmp", "hash-nonzero", "mvar-misplaced", "syntax",
    "nesting-too-deep")


def refusal_coverage_problems():
    """Each case asserts its own code, so a code that no case names is a
    refusal path nothing exercises. p1_expected's "unreachable in P1" notes
    are true of P1's proofs, not of the kernel: every REFUSAL_CODES code
    needs a case too, from DIRECT_REFUSALS when no move reaches it."""
    named = {c["refusal"] for c in BAD_MOVES + X.WRONG_ANSWERS + SUITE_BAD_MOVES
             + SUBST_BAD_MOVES + (X.INT_FLIP_BAD_MOVES + X.E56_BAD_MOVES
                                  + X.E57_BAD_MOVES + X.E56_REVIEW_CASES["bad_moves"]
                                  + X.SECOND_REVIEW_BAD_MOVES
                                  if CONSOLIDATED else [])}
    if S0 is not None:
        named |= {c["refusal"] for c in S0.INT_SUBST_WRONG_ANSWERS
                  + S0.INT_SUBST_S0_REFUSALS
                  + (CONSOLIDATION_WRONG_ANSWERS if CONSOLIDATED else [])}
    named |= {a.split(":", 1)[1] for f in X.FORGERIES for a in f["accept"]
              if a.startswith("refusal:")}
    named |= set(DIRECT_CODES) | {"syntax"}  # HOSTILE_TREES
    named |= {c for _, _, c in DIRECT_REFUSALS}
    named |= {r[-1] for r in X.PARSE_REFUSALS + X.PARSE_REFUSALS_JUDGEMENT}
    named |= {r[-1] for rows in SUITE_PARSE_REFUSALS.values() for r in rows}
    return [f"{c}: no case asserts it" for c in REFUSAL_CODES
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
    """One BAD_MOVES case: refused with its code (and, for a decided-false
    refusal, its message), the state unchanged. A case decided false at
    installation (move install, or at: install) is refused there; a case
    with goal_emits asserts installation's list first, with its
    certificates and reasons."""
    move, args = b["move"]
    if move == "install" or b.get("at") == "install":
        try:
            g = goal(b["goal"])
        except T.ParseError as e:  # parse_goal is part of installing
            return [] if e.code == b["refusal"] else [f"parse refused {e.code}"]
        r = K.install(g)
        if isinstance(r, K.ProofState):
            return ["installed"]
        return refusal_problems_of(r, b)
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    if "state" in b:
        st, handles = replay(*b["state"])
        if st.original != goal(b["goal"]):
            out.append("the state's original goal is not the entry's goal")
    else:
        st, handles = install(b["goal"], (b["id"], "goal")), {}
        if "goal_emits" in b:
            compare_emitted(miss, b["id"], "goal", b["goal_emits"], st.last.emitted,
                            frozenset(), certs=case_certs(b), reasons=case_reasons(b))
        for s in b["setup"]:
            st = take(st, s["move"], s["args"], handles, (b["id"], s["id"]))
    before, before_goal = st.obligations(), st.goal
    r = K.step(st, move, build_args(args, handles))
    if isinstance(r, K.ProofState):
        return out + ["accepted"]
    out += refusal_problems_of(r, b) + residual_problems_of(r, b)
    if st.obligations() != before or st.goal != before_goal:
        out.append("the refused step changed the state (E13)")
    if "e27" in b:
        out += e27_refusal_problems(r, b["e27"], term)
    return out


def e27_refusal_problems(r, e27, parse):
    """EVALUATED_RULE, Reporting: the residual is the offending subterm
    `at`, as a tree, and the message is E27_MESSAGES[clause[0]] filled with
    show(residual) and the entry. The printer's output is asserted only
    through that template (PRINT_EXACT's convention)."""
    out = []
    if r.residual != parse(e27["at"]):
        out.append(f"residual {show(r.residual)} is not the subterm "
                   f"{e27['at']} as a tree")
    want = X.E27_MESSAGES[e27["clause"][0]].format(term=show(r.residual),
                                                   entry=e27.get("entry"))
    if r.message != want:
        out.append(f"message {r.message!r}, expected {want!r}")
    return out


def e27_cases():
    return [b for b in BAD_MOVES if "e27" in b]


def e27_clause_problems():
    """Each e27 case's clause ('a', 'b1' to 'b4'), subterm and entry, read
    through schema.evaluated_offence (ARCHITECTURE.md §3) on the value
    alone: the refusal carries only the code, message and residual, and
    'which of b1-b4' is part of the rule (1 + 1 is b1, tried before b2)."""
    out = []
    for b in e27_cases():
        e = b["e27"]
        got = SC.evaluated_offence(term(b["move"][1]["value"]))
        want = (e["clause"], term(e["at"]), e["entry"])
        if got != want:
            out.append(f"{b['id']}: {got and (got[0], show(got[1]), got[2])}, "
                       f"expected {(e['clause'], e['at'], e['entry'])}")
    return out


def e27_order_problems(b):
    """EVALUATED_RULE, Order in close: a value both wrong and unevaluated is
    refused by the check, with the residual lhs - value (E14), not by E27,
    which runs last. The value must be one E27 would refuse, or the case
    would not test the order."""
    g, v = goal(b["goal"])[0], term(b["move"][1]["value"])
    out = [] if SC.evaluated_offence(v) is not None else [
        f"{show(v)} is fully evaluated, so the order is not what is tested"]
    st = install(b["goal"], (b["id"], "goal"))
    r = K.step(st, "close", build_args(b["move"][1], {}))
    if not isinstance(r, K.Refusal):
        return out + [describe(r)]
    if r.code != b["refusal"]:
        out.append(f"refused {r.code}: {r.message}")
    if r.residual is None:
        return out + ["the refusal carries no residual"]
    ok, note = equal_by("ring", r.residual, T.Add(g.lhs, T.Neg(v)))
    if not ok:
        out.append(f"residual {show(r.residual)} is not lhs - value "
                   f"{show(g.lhs)} - ({show(v)}) under ring{note}")
    zero, note = equal_by("ring", r.residual, T.Num(0))
    if zero or note:
        out.append(f"residual {show(r.residual)} is zero under ring{note}")
    return out


def evaluated_accept_problems(c):
    """One EVALUATED_ACCEPTS case: refl on V == ?A with value V is accepted,
    goal None and theorem V == V as a tree. The verdict is not asserted
    (sqrt(y^2) owes y^2 >= 0, pi/pi owes pi # 0: no part of E27)."""
    st = install(c["goal"], (c["id"], "goal"))
    move, args = c["move"]
    r = K.step(st, move, build_args(args, {}))
    if not isinstance(r, K.ProofState):
        return [describe(r)]
    out = []
    if r.goal is not None:
        out.append(f"the goal is still open: {T.show_goal(r.goal)}")
    if r.theorem != goal(c["theorem"]):
        out.append(f"theorem {show(r.theorem)}, expected {c['theorem']}")
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
               tracker_problems(self.state.obligations(), TRACKER_AT_FORGERY_STATE)]
        outcome, r = self.attempt(self.h)
        if outcome != "accepted":
            out.append(f"the genuine h_sqrt3 no longer closes the slot: {outcome}")
        elif K.report(r) != VERDICTS["P1.2-alt"]:
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
             tracker_problems(st2.obligations(), TRACKER_AT_FORGERY_STATE)]
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


def forgery_state(case):
    """The finished state the two admission-bearing forgeries attack, with
    what its tracker and report must stay: P1.1 at s6 before regularity; and
    since every proof reads 'Proved.' (E69), REG_FORGERY_STATE, REG_Q23_CASES
    d_atoms_cancel_undefined after its close (N = 1). Also the admission
    tracker_write deletes and the key it marks discharged."""
    if REGULARITY:
        c = next(q for q in REG_Q23 if q["id"] == X.REG_FORGERY_STATE[1])
        st = install(c["goal"], (case["id"], "goal"))
        move, args = c["move"]
        st = take(st, move, args, {}, (case["id"], move))
        k = key("abs x in C^1(true)", "true")
        return (st, [("abs x in C^1(true)", "true", X.ADMITTED, X.T_NONE)],
                X.VERDICT.format(n=1), k, k)
    return (replay(*case["state"])[0], FINAL["P1.1"], VERDICTS["P1.1"],
            key("t >= 0", "[0, pi/2]"), key("0 <= pi/2", "true"))


def tracker_write(st, delete, mark):
    """Public API only: delete the admission `delete` from what
    obligations() returns, and mark `mark` discharged, by attribute and
    then through vars(), which looks like a copy but is the record's own
    dict when it has one. Returns what raised."""
    raised = []
    obs = st.obligations()
    try:
        del obs[next(i for i, o in enumerate(obs) if o.key == delete)]
    except Exception as e:  # noqa: BLE001
        raised.append(("delete", crash_text(e)))
    target = next(o for o in obs if o.key == mark)
    try:
        target.status = X.DISCHARGED
    except Exception as e:  # noqa: BLE001
        raised.append(("mark discharged", crash_text(e)))
    try:
        vars(target)["status"] = X.DISCHARGED
    except Exception as e:  # noqa: BLE001
        raised.append(("mark discharged through vars()", crash_text(e)))
    return raised


def p1_1_post(st, final, verdict):
    out = [fmt(("FINAL_TRACKER", "forgery state") + sfx, d) for sfx, d in
           tracker_problems(st.obligations(), final)]
    if K.report(st) != verdict:
        out.append(f"the report is {K.report(st)!r}")
    return out


def forge_tracker_write(case):
    st, final, verdict, delete, mark = forgery_state(case)
    raised = tracker_write(st, delete, mark)
    outcome = "raise_at_mutation" if raised else "no_effect"
    detail = "; ".join(f"{op} raised {e}" for op, e in raised) or "both completed"
    return ([("delete an admission and mark one discharged", outcome, detail)],
            p1_1_post(st, final, verdict))


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
    st, final, verdict, delete, mark = forgery_state(case)
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
        tracker_write(st, delete, mark)
        text = K.report(st)
        reports.append(text)
        attempts.append(("(c) report after a tracker write",
                         "refused" if text == verdict else "returned",
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
    post = [f"a report is {t!r}, not {verdict!r}" for t in reports
            if t != verdict]
    post += [f"a report contains 'Proved.': {t!r}" for t in reports
             if "Proved." in str(t)]
    post += [f"{f.__name__}(state) contains 'Proved.'" for f in (str, repr)
             if "Proved." in f(st)]
    if "Proved." in captured.getvalue():
        post.append("'Proved.' was printed")
    return attempts, post + p1_1_post(st, final, verdict)


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
            tracker_problems(st.obligations(), TRACKER_AT_FORGERY_STATE)]
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


def _planted_switched():
    """PLANTED_BUGS as DISCHARGE_PLANTED_BUGS re-traces them: its admissions,
    drop_keys, retagged (with statuses) and refused replace the old, and its
    caught_by does unless it says 'unchanged'."""
    out = {}
    for name, bug in X.PLANTED_BUGS.items():
        d = X.DISCHARGE_PLANTED_BUGS.get(name, {}) if DISCHARGE_WIRED else {}
        b = dict(bug, **{k: d[k] for k in ("admissions", "drop_keys", "retagged",
                                           "refused") if k in d})
        if isinstance(d.get("caught_by"), list):
            b["caught_by"] = d["caught_by"]
        out[name] = b
    return out


def _mutations_switched():
    """DEFINEDNESS_MUTATIONS as DISCHARGE_MUTATION_CHANGES re-traces them:
    caught_by less 'drop' plus 'add', and admissions the change's or, by
    default, 3 in every proof."""
    out = {}
    for name, m in X.DEFINEDNESS_MUTATIONS.items():
        if not DISCHARGE_WIRED:
            out[name] = m
            continue
        ch = X.DISCHARGE_MUTATION_CHANGES.get(name, {})
        drop = {tuplify(c) for c in ch.get("drop", ())}
        out[name] = dict(m, caught_by=[c for c in map(tuplify, m["caught_by"])
                                       if c not in drop]
                         + [tuplify(c) for c in ch.get("add", ())],
                         admissions=ch.get("admissions", dict(X._D3)))
    return out


def _with_sheet(name, bug):
    """One planted bug or mutation as P1_1_SHEET_TRACES re-traces it for
    P1.1-sheet in PROOFS (E52): its N there beside the other proofs' (None:
    refused, and left out, as the data writes a refused proof), checked for
    every child as `sheet_N`; its added caught_by locations; and its
    retagged and refused rows, where the trace gives them. A name the
    traces do not list is N default_N with nothing added."""
    if not CONSOLIDATED:
        return bug
    t = J["traces"].get(name, {"N": J["default_N"], "add": []})
    b = dict(bug, sheet_N=t["N"],
             caught_by=[tuplify(c) for c in bug["caught_by"]]
             + [tuplify(c) for c in t["add"]])
    if "admissions" in bug:
        b["admissions"] = {**bug["admissions"],
                           **({SHEET: t["N"]} if t["N"] is not None else {})}
    if "retagged" in t:
        b["retagged"] = {**bug.get("retagged", {}), SHEET: list(t["retagged"])}
    if "refused" in t:
        b["refused"] = {**bug.get("refused", {}), SHEET: t["refused"]}
    return b


def _e56_planted(name, bug, change):
    """A bug E56_CHANGES re-traces with E53 built: its new admissions,
    retagged rows, refusals, caught_by and certificate replace the old."""
    if not CONSOLIDATED:
        return bug
    new = E56[change]["new"]
    return dict(bug, **{k: new[k] for k in ("admissions", "retagged", "refused",
                                            "caught_by", "certificate") if k in new})


PLANTED_BUGS = _planted_switched()
DEFINEDNESS_MUTATIONS = _mutations_switched()
if CONSOLIDATED:
    PLANTED_BUGS["pi_pos_not_in_constraint_set"] = _e56_planted(
        "pi_pos_not_in_constraint_set", PLANTED_BUGS["pi_pos_not_in_constraint_set"],
        "DISCHARGE_PLANTED_BUGS pi_pos_not_in_constraint_set")
    # the admissions E56_CHANGES gives already hold the sheet's
    PLANTED_BUGS = {n: _with_sheet(n, b) for n, b in PLANTED_BUGS.items()}
    DEFINEDNESS_MUTATIONS = {n: _with_sheet(n, b)
                             for n, b in DEFINEDNESS_MUTATIONS.items()}
DISCHARGE_BUGS = {n: _with_sheet(n, b) for n, b in X.DISCHARGE_NEW_PLANTED_BUGS.items()}
if CONSOLIDATED:
    DISCHARGE_BUGS["search_scales_wrongly"] = _with_sheet(
        "search_scales_wrongly", _e56_planted(
            "search_scales_wrongly", X.DISCHARGE_NEW_PLANTED_BUGS["search_scales_wrongly"],
            "DISCHARGE_NEW_PLANTED_BUGS search_scales_wrongly"))


# REG_BUG_RETRACE: under the switch a proof's N under a bug is its
# post-discharge N minus the Reg keys it had, each now discharged under the
# bug as without it, except where the retrace lists otherwise; caught_by
# unchanged except its drops and adds; ring_reads_D_as_atom and
# field_reads_D_as_atom retired (vacuous: the kernel itself reads every D
# node as an atom, E66 (1)).
REG_COUNT = {"P1.1": 3, "P1.1-fallback": 3, "P1.2": 3, "P1.2-alt": 3, SHEET: 5,
             "S1": 3, "S2": 3, "S3": 3, "S3-ring": 3, "SUB1": 5, "SUB2": 5,
             "QC1": 5, "S2R": 4}
_RT = X.REG_BUG_RETRACE
REG_RETIRED = ("ring_reads_D_as_atom", "field_reads_D_as_atom")
# The data's scope names -> the suite's tables of bugs they re-trace.
# P1_1_SHEET_TRACES' entries apply wherever a child runs PROOFS.
_RT_SCOPES = {
    "PLANTED_BUGS": ("P1",), "E56_CHANGES": ("P1",),
    "DISCHARGE_NEW_PLANTED_BUGS": ("DISCHARGE",),
    "DISCHARGE_MUTATION_CHANGES": ("MUTATIONS",), "DEFINEDNESS_MUTATIONS": ("MUTATIONS",),
    "P1_1_SHEET_TRACES": ("P1", "DISCHARGE", "MUTATIONS"),
    "INT_SUBST_PLANTED_BUGS": ("SUBST",), "REVIEW_PLANTED_BUGS": ("SUBST",),
    "INT_SUBST_SEAMS": ("SUBST_SEAMS",),
    "CONSOLIDATION_PLANTED_BUGS": ("CONSOLIDATION",), "E56_PLANTED_BUGS": ("CONSOLIDATION",),
    "REVIEW2_PLANTED_BUGS": ("CONSOLIDATION",),
}


def _rt_entries():
    """REG_BUG_RETRACE read as (scope, bug name) -> [entry, ...], each entry
    a dict of any of 'admissions' (merged over the rule's N), 'drop' and
    'add' (caught_by locations) and 'step_lists_changed'. A key names its
    table and then one bug, or several separated by ', '; an entry whose
    'add' or 'drop' is a dict names its bugs inside ({bug: locations})."""
    out = {}
    for k, v in _RT.items():
        if not isinstance(v, dict):
            continue
        table, _, rest = k.replace(",", " ,", 1).partition(" ")
        scopes = _RT_SCOPES.get(table.rstrip(","))
        if scopes is None:
            continue
        per_bug = {f: v[f] for f in ("add", "drop") if isinstance(v.get(f), dict)}
        if per_bug:
            names = {n for d in per_bug.values() for n in d}
            items = {n: {f: d.get(n, ()) for f, d in per_bug.items()} for n in names}
        else:
            names = [n.strip() for n in rest.lstrip(" ,").split(",")]
            items = {n: {f: v[f] for f in ("admissions", "add", "drop",
                                           "step_lists_changed") if f in v}
                     for n in names}
        for n, e in items.items():
            for sc in scopes:
                out.setdefault((sc, n), []).append(e)
    return out


_RT_ENTRIES = _rt_entries() if REGULARITY else {}


def _reg_retrace(name, bug, scope):
    """One planted bug, mutation or seam as REG_BUG_RETRACE re-traces it:
    the rule (N less the Reg keys each proof had, the sheet's too), then
    every entry the retrace records for it in this scope, applied the same
    way (admissions merged, drop and add on caught_by, step_lists_changed)."""
    if not REGULARITY:
        return bug
    b = dict(bug)
    if "admissions" in b:
        b["admissions"] = {p: n - REG_COUNT[p] for p, n in b["admissions"].items()}
    if b.get("sheet_N") is not None:
        b["sheet_N"] -= REG_COUNT[SHEET]
    caught = [tuplify(c) for c in b["caught_by"]]
    for e in _RT_ENTRIES.get((scope, name), ()):
        if "admissions" in e:
            b["admissions"] = {**b.get("admissions", {}), **e["admissions"]}
            if SHEET in e["admissions"] and "sheet_N" in b:
                b["sheet_N"] = e["admissions"][SHEET]
        drop = {tuplify(c) for c in e.get("drop", ())}
        caught = [c for c in caught if c not in drop] + [
            tuplify(c) for c in e.get("add", ()) if tuplify(c) not in caught]
        if "step_lists_changed" in e:
            b["step_lists_changed"] = e["step_lists_changed"]
    b["caught_by"] = caught
    return b


if REGULARITY:
    PLANTED_BUGS = {n: _reg_retrace(n, b, "P1") for n, b in PLANTED_BUGS.items()}
    DEFINEDNESS_MUTATIONS = {n: _reg_retrace(n, b, "MUTATIONS")
                             for n, b in DEFINEDNESS_MUTATIONS.items()
                             if n not in REG_RETIRED}
    DISCHARGE_BUGS = {n: _reg_retrace(n, b, "DISCHARGE") for n, b in DISCHARGE_BUGS.items()}


def closed_admissions(data):
    """The child's N per proof, a proof it refused left out, which is how
    the data writes a mutation's admissions."""
    return {p: n for p, n in data["admissions"].items() if n is not None}
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
    (proof, sid, prop, flag), = PLANTED_BUGS["tracker_drops_reemitted"][
        "caught_by"]
    steps = OBLIGATIONS[proof]
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
            drop = {key(p, d) for p, d in PLANTED_BUGS[name]["drop_keys"]}
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
        for c in CASES[table]:
            try:
                problems = globals()[fn](c)
            except Mismatch as m:
                problems = [str(m)]
            if problems:
                out.append([table, c["id"]])
    if REGULARITY and TD is not None:  # REG_BUG_RETRACE's adds name these
        out += TD.reg_must_reject_verdicts()
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
        found, admissions, final, refusals, runs = [], {}, {}, {}, {}
        with ctx:
            for p in PROOFS:
                run = runs[p] = run_proof(p, strict=False, out=lambda line: None)
                found += [where for _, where, _ in run.found]
                refusals.update({"/".join(where): detail for _, where, detail
                                 in run.found if where[-1] == "refused"})
                admissions[p] = run.n
                final[p] = None if run.n is None else [
                    [T.show(o.key), o.status, o.tag[0], list(o.tag[1])]
                    for o in run.state.obligations()]
            if kind != "plant":
                found += case_failures()
            bug = PLANTED_BUGS.get(name, {}) if kind == "plant" else {}
            certs = retag_certificate_problems(bug, runs)
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions, "final": final,
                      "refusals": refusals, "certificates": certs}))
    return 0


def retag_certificate_problems(bug, runs):
    """A bug whose data gives the certificate of its retagged keys
    (E56_CHANGES' pi_pos_not_in_constraint_set, E53's content split): each
    retagged key discharged in the child's run carries it."""
    out = []
    if "certificate" not in bug:
        return out
    want = TD.cert_of(bug["certificate"])
    for proof, rows in bug.get("retagged", {}).items():
        run = runs.get(proof)
        if run is None or run.n is None:
            continue
        obs = {o.key: o for o in run.state.obligations()}
        for row in rows:
            ob = obs.get(key(row[0], row[1]))
            if ob is not None and ob.status == X.DISCHARGED:
                diff = TD.cert_differences(ob.certificate, want)
                if diff:
                    out.append(f"{proof}: {row[0]} @ {row[1]}: {'; '.join(diff)}")
    return out


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
    if closed_admissions(data) != bug["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {bug['admissions']}")
    out += refused_problems(data, bug)
    out += sheet_n_problems(data, bug)
    out += data.get("certificates", [])
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
        for row in retags:  # (prop, dom, tag), or (prop, dom, status, tag)
            p, d, tag = row[0], row[1], row[-1]
            got = rows.get(T.show(key(p, d)))
            if got is None or got[1] != tag or (len(row) == 4 and got[0] != row[2]):
                out.append(f"{proof}: {p} @ {d} is {got}, expected {row[2:]}")
    if bug.get("step_lists_changed") is False:
        out += [f"a step list changed: {m}" for m in found if m[0] in PROOFS]
    for proof in bug.get("affects", ()):
        if not any(proof in m[:2] for m in found):
            out.append(f"{proof} is listed as affected and shows no mismatch")
    return out


def refused_problems(data, bug):
    """Each refusal a bug's data names, (step, message spec) per proof: the
    child's refusal there, by code and message. A message spec whose
    template is a refusal code (orientation-undecided, E56) is that code's;
    any other is DECIDED_FALSE_MESSAGES', code obligation-decided-false."""
    out = []
    for proof, (sid, msg) in bug.get("refused", {}).items():
        got = data.get("refusals", {}).get(f"{proof}/{sid}/refused")
        code = msg[0] if msg[0] in MESSAGES else X.OBLIGATION_DECIDED_FALSE
        want = f"refused {code}: {expected_message(msg)}"
        if got != want:
            out.append(f"{proof} {sid}: {got!r}, expected {want!r}")
    return out


def sheet_n_problems(data, bug):
    """P1.1-sheet's N under the bug, as P1_1_SHEET_TRACES gives it (None:
    refused), for every child that runs PROOFS (E52)."""
    if "sheet_N" not in bug:
        return []
    got = data["admissions"].get(SHEET)
    return [] if got == bug["sheet_N"] else [
        f"{SHEET}: N = {got}, expected {bug['sheet_N']} (P1_1_SHEET_TRACES)"]


def control_problems():
    """The child harness, unpatched, finds nothing, in the proofs or in the
    cases a definedness mutation can name: so what a planted or mutated run
    catches comes from its patch, not from the child."""
    data, out = spawn("--control")
    if data is None:
        return out
    out += [f"unpatched child found {m}" for m in sorted(data["mismatches"], key=str)]
    if data["admissions"] != ADMISSIONS:
        out.append(f"unpatched admissions {data['admissions']}")
    return out


def clean_after_problems():
    """The unmutated suite, run again in this process after the planted runs:
    nothing leaked, and unittest.mock was never imported here."""
    out = []
    for p in PROOFS:
        run = run_proof(p, out=lambda line: None)
        out += [f"{p}: {fmt(w, d)}" for _, w, d in run.found]
        if run.n != ADMISSIONS[p]:
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
    # REWRITE_RULE step 3, made lax, and E57's step 2a with it (REVIEW2_CHANGES):
    # the case's Int reaches the rewrite through an inst value
    "rewrite_closing_check_goal": {
        "case": "rewrite_inst_shadows",
        "seam": "field.ring_equal and kernel._no_trees_erased",
        "refusal": "shadowing"},
    "ftc_closing_check_goal_Int_in_F": {
        "case": "ftc_F_holds_Int_binder", "seam": "deriv.const_guard",  # E12's guard, off
        "refusal": "D11-bound-and-free"},
}


def backstop_patch(name, mock):
    """The child's patch for one BACKSTOPS case. The seam is asserted to
    exist first."""
    seam = BACKSTOPS[name]["seam"]
    if seam == "field.ring_equal and kernel._no_trees_erased":
        assert callable(getattr(FD, "ring_equal", None)), "seam field.ring_equal is missing"
        assert callable(getattr(K, "_no_trees_erased", None)), \
            "seam kernel._no_trees_erased is missing"
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(FD, "ring_equal", lambda a, b: True))
        stack.enter_context(mock.patch.object(K, "_no_trees_erased",
                                              lambda lhs, inst, at: None))
        return stack
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
        cases = {c["id"]: c for c in [*SUITE_BAD_MOVES, *BAD_MOVES]}
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
        # the one table the formers and the regularity checker both read
        # (domains.NATURAL_DOMAINS, E61), so the patch reaches both
        import domains as DM
        fn, row = TABLE_MUTATIONS[name]
        assert fn in DM.NATURAL_DOMAINS, f"seam domains.NATURAL_DOMAINS[{fn!r}] is missing"
        table = dict(DM.NATURAL_DOMAINS)
        if row is None:
            del table[fn]
        else:
            table[fn] = row
        return mock.patch.object(DM, "NATURAL_DOMAINS", types.MappingProxyType(table))
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
        futures = {n: ex.submit(spawn, "--mutate", n) for n in DEFINEDNESS_MUTATIONS}
    return {n: f.result() for n, f in futures.items()}


# DEFINEDNESS_MUTATIONS locations the rules no longer reach, each left
# failing with its evidence until the data changes (a data_change_request).
_E57_DCR = (
    "data_change_request: E57_RULE's step 2a refuses "
    "'Int-or-D-not-normalisable' when the target `at` holds an Int or D node, "
    "before step 3's ring_nf runs; {case}'s target {at} holds one, so the case "
    "is refused with its own code under this mutation too, and the location "
    "cannot catch a ring_nf mutation any more. REVIEW2_CHANGES' 'nothing "
    "changes' missed it: drop ('BAD_MOVES', '{case}') from {name}'s caught_by "
    "(the mutation stays caught at its other locations)")
MUTATION_DATA_CHANGE_REQUESTS = {
    ("ring_reads_Int_as_atom", ("BAD_MOVES", "match_refuses_Int")): _E57_DCR.format(
        case="match_refuses_Int", at="atan((Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1))",
        name="ring_reads_Int_as_atom"),
    ("ring_reads_D_as_atom", ("BAD_MOVES", "match_refuses_D")): _E57_DCR.format(
        case="match_refuses_D", at="atan(D[x](abs x) - D[x](abs x))",
        name="ring_reads_D_as_atom"),
}


def mutation_problems(mutation, result, name=None):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    for c in map(tuplify, mutation["caught_by"]):
        if c not in found:
            out.append(f"not caught at {c}")
            if (name, c) in MUTATION_DATA_CHANGE_REQUESTS:
                out.append(MUTATION_DATA_CHANGE_REQUESTS[(name, c)])
    if "admissions" in mutation and closed_admissions(data) != mutation["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {mutation['admissions']}")
    return out + sheet_n_problems(data, mutation)


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


def placement_refused(g, code):
    def run():
        r = K.install(goal(g))
        return [] if isinstance(r, K.Refusal) and r.code == code else [
            f"installed or refused otherwise: {describe(r)}"]
    return run


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


# (label, problem function). Since discharge (E33) refuses a step whose
# obligation is decided false, each case's goal emits only keys that hold:
# five were changed for that when discharge was wired in, each keeping the
# placement it tests (the second range [-1, 0], not [-3, 0]; a stated
# y > 0 for x*y/y; the reversed literal range [2, 1], not [1, 0]; the
# divisor y^2 + 1, not y, on the empty domain; tan 1, not tan(pi/2), in the
# fact's inst, whose cos 1 # 0 is true and undecided).
# Every P1 rhs is ?A, no P1 key inside a
# non-literal Int body is x-dependent, P1's one fact hypothesis is closed,
# every P1 orientation is closed (E5 gives it domain ()), no P1 goal nests
# Ints, has a -oo limit, or holds a negative Pow or an RPow, and none holds
# one partial former at two different position domains, so none of these
# placements or formers shows in P1's data.
EMISSION_PLACEMENT = [
    ("one former at two position domains in one term gives two keys (E6, E26)",
     placement_install("(Int[x=0..1] ln(x+2)) - (Int[x=-1..0] ln(x+2)) == ?A",
                       {"x + 2 > 0 @ [0, 1]": ["former"], "x + 2 > 0 @ [-1, 0]": ["former"],
                        "ln(x + 2) in C^0([0, 1])": ["former"],
                        "ln(x + 2) in C^0([-1, 0])": ["former"]})),
    ("install charges both sides' formers when the rhs is not ?A (E6)",
     placement_install("x == x*y/y @ y > 0", {"y # 0 @ y > 0": ["former"]})),
    # E64: each statable Int also owes its integrand in C^0 on its range,
    # after the term's E6/E26 formers, and that key uses the range (E68)
    ("a closed key uses no range; the Int's own former does (ARCHITECTURE.md §4, E68)",
     placement_install("Int[x=0..pi] 1/sqrt 3 == ?A",
                       {"sqrt 3 # 0": ["former"], "3 >= 0": ["former"],
                        "1/sqrt 3 in C^0(x in [0, pi])": ["former"], "0 <= pi": ["orient"]})),
    # E56: 1 <= pi is not provable from pi_pos alone, so these two use
    # 1 + pi, whose order is linear with pi_pos
    ("a key that uses the range brings its orientation (E56, E6)",
     placement_install("Int[x=1..1 + pi] 1/x == ?A",
                       {"x # 0 @ [1, 1 + pi]": ["former"], "1 <= 1 + pi": ["orient"],
                        "1/x in C^0([1, 1 + pi])": ["former"]})),
    ("a reversed symbolic range is built from the order discharge proves (E56)",
     placement_install("Int[x=1 + pi..1] 1/x == ?A",
                       {"x # 0 @ [1, 1 + pi]": ["former"], "1 <= 1 + pi": ["orient"],
                        "1/x in C^0([1, 1 + pi])": ["former"]})),
    ("ftc places a fact's hypothesis on the check's domain (E9, E10)",
     placement_fact_hyp),
    ("a negative integer power charges its base's former NonZero (E6, §5.1)",
     placement_install("Int[x=1..2] x^(-2) == ?A", {"x # 0 @ [1, 2]": ["former"],
                                                     "x^(-2) in C^0([1, 2])": ["former"]})),
    ("the boundary power n = -1 charges the same former (E6, §5.1)",
     placement_install("Int[x=1..2] x^(-1) == ?A", {"x # 0 @ [1, 2]": ["former"],
                                                     "x^(-1) in C^0([1, 2])": ["former"]})),
    ("a real power charges base > 0, strict (E6; GRAMMAR.md RPow owes a > 0)",
     placement_install("Int[x=1..2] x^y == ?A", {"x > 0 @ [1, 2]": ["former"],
                                                  "x^y in C^0(x in [1, 2])": ["former"]})),
    ("an infinite lower end is open, the finite end closed, no orientation (E4)",
     placement_install("Int[x=-oo..-1] 1/x == ?A", {"x # 0 @ (-oo, -1]": ["former"]})),
    ("NegInf is the lower end whichever limit it was written as (E4)",
     placement_install("Int[x=-1..-oo] 1/x == ?A", {"x # 0 @ (-oo, -1]": ["former"]})),
    ("literal ends are ordered into [min, max], with no orientation (E4)",
     placement_install("Int[x=2..1] 1/x == ?A", {"x # 0 @ [1, 2]": ["former"],
                                                  "1/x in C^0([1, 2])": ["former"]})),
    ("each enclosing Int's orientation is owed, not only the innermost (E56, E6)",
     placement_install("Int[y=1..1 + pi] (Int[x=1..y] 1/(x*y)) == ?A",
                       {"x*y # 0 @ y in [1, 1 + pi], x in [1, y]": ["former"],
                        "1 <= 1 + pi": ["orient"], "1 <= y @ [1, 1 + pi]": ["orient"],
                        # E64 in pre-order: the outer Int's former (no rule
                        # for its Int body, so admitted none), then the inner's
                        "Int[x = 1 .. y] 1/(x*y) in C^0([1, 1 + pi])": ["former"],
                        "1/(x*y) in C^0(y in [1, 1 + pi], x in [1, y])": ["former"]})),
    ("an undecided order is refused at installation once the Int's own former "
     "uses the range (E68)",
     placement_refused("Int[x=1..pi] 2*x == ?A", "orientation-undecided")),
    ("an orientation that is not closed keeps the goal's domain (E4, E5)",
     placement_install("Int[x=1..y] 1/x == ?A @ y > 1",
                       {"x # 0 @ y > 1, x in [1, y]": ["former"],
                        "1 <= y @ y > 1": ["orient"],
                        "1/x in C^0(y > 1, x in [1, y])": ["former"]})),
    ("a goal hypothesis's former is charged at the hypotheses before it (E6, E26)",
     placement_install("x == ?A @ x > 0, ln x > 0", {"x > 0 @ x > 0": ["former"]})),
    ("the first hypothesis's former owes on the empty domain (E6)",
     placement_install("x == ?A @ 1/(y^2 + 1) > 0", {"y^2 + 1 # 0": ["former"]})),
    ("an interval hypothesis's ends are charged too (E6, E26)",
     placement_install("x == ?A @ y > 0, x in [0, sqrt y]", {"y >= 0 @ y > 0": ["former"]})),
    ("a fact's inst former lands on the using step's domain (E10, E26)",
     placement_fact_inst("atan(-x) == ?A @ x > 1", "atan_odd", {"u": "x + 0*ln x"},
                         "-atan(x)", {"x > 0 @ x > 1": ["former"]})),
    ("a fact's inst tan u owes cos u # 0 when the fact is used (E10, E26)",
     placement_fact_inst("atan(-3) == ?A", "atan_odd", {"u": "3 + 0*tan 1"},
                         "-atan(3)", {"cos 1 # 0": ["former"]})),
    ("a fact's inst pi/2 owes its divisor as a former, and field owes it too (E10, §6.2)",
     placement_fact_inst("atan(-3) == ?A", "atan_odd", {"u": "3 + 0*sin(pi/2)"},
                         "-atan(3)", {"2 # 0": ["former", "field_div"]})),
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
        st, handles = install(PROOFS[proof]["goal"], (proof, "goal")), {}
        for s in PROOFS[proof]["steps"]:
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
    d asinh = asinh would prove Int[x=0..1] asinh x == asinh 1 - asinh 0
    with both admissions true. (cosh was the example until section 26 gave
    it a rule, E116; asinh still has none, E124.)"""
    out = []
    try:
        DV.APP_RULES["asinh"] = lambda u, du: (T.Mul(T.App("asinh", u), du), ())
        out.append("APP_RULES took a new rule")
    except TypeError:
        pass
    st = install("Int[x = 0 .. 1] asinh x == ?A", ("asinh", "goal"))
    r = K.step(st, "ftc", {"F": term("asinh x"), "check": "ring", "facts": []})
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


# Review D1: a close value of 500 nested Negs made close raise
# RecursionError out of step(), through the printer that formats the
# refusal's message (E27's, and E23's close-schema-not-closed). A crash is a
# kernel bug, not a refusal (E21), so each must come back as a Refusal.
DEEP_NEGS = 500
DEEP_NEG_CLOSES = [
    # (goal, value, code, residual): 500 Negs over pi is pi, so ring proves
    # the refl and E27 refuses it, b4's Neg over a Neg at the root (the
    # maximal sum has one summand, pi).
    ("-" * DEEP_NEGS + "pi == ?A", "-" * DEEP_NEGS + "pi", "close-not-evaluated",
     "-" * DEEP_NEGS + "pi"),
    # The whitelist refuses the Int, and its message prints the value.
    ("0 == ?A", "-" * DEEP_NEGS + "(Int[t = 0 .. 1] t)", "close-schema-not-closed",
     None),
]


def deep_neg_close_problems():
    out = []
    for g, v, code, res in DEEP_NEG_CLOSES:
        where = f"{DEEP_NEGS} Negs over {v.lstrip('-')}"
        try:
            st = K.install(goal(g))
            if not isinstance(st, K.ProofState):
                out.append(f"{where}: install: {describe(st)}")
                continue
            r = K.step(st, "close", {"value": term(v), "check": "ring", "facts": []})
        except RecursionError:
            out.append(f"{where}: RecursionError, not a Refusal (E21)")
            continue
        if not (isinstance(r, K.Refusal) and r.code == code):
            out.append(f"{where}: {describe(r)}, expected {code}")
        elif res is not None:
            if r.residual != term(res):
                out.append(f"{where}: the residual is not the whole value")
            want = X.E27_MESSAGES["b"].format(term=T.show(r.residual))
            if r.message != want:
                out.append(f"{where}: the message is not E27_MESSAGES' (b)")
    return out


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
    if DISCHARGE_WIRED:
        # The second Int's range [-1, 0] makes t >= 0 false (F3 at t = -1),
        # so the rewrite is refused naming that range: the refusal shows
        # occurrence 1 chose the second Int, as occurrence 0's accepted
        # rewrite of [0, 1] (OCCURRENCE_CASE one) shows it chose the first.
        before = st.obligations()
        r = K.step(st, move, build_args(dict(args, occurrence=1), {}))
        out += refusal_problems_of(r, {
            "refusal": X.OBLIGATION_DECIDED_FALSE,
            "message": X._point("t >= 0 @ [-1, 0]", "-1 >= 0", t="-1")})
        if st.obligations() != before:
            out.append("the refused step changed the state (E13)")
        # The same move where the second range makes t >= 0 true, so that
        # the accepted step's occurrence count and goal are asserted too.
        st = install("(Int[t = 0 .. 1] sqrt(t^2)) + (Int[t = 1 .. 2] sqrt(t^2)) == ?A",
                     ("occurrence 1", "goal"))
        st2 = take(st, move, dict(args, occurrence=1), {}, ("occurrence 1", move))
        if st2.last.occurrences != 1:
            out.append(f"occurrences {st2.last.occurrences}, expected 1")
        if st2.goal != goal("(Int[t = 0 .. 1] sqrt(t^2)) + (Int[t = 1 .. 2] t) == ?A"):
            out.append(f"goal_after: got {show(st2.goal)}")
        compare_emitted(miss, "occurrence 1", move,
                        [("t >= 0", "[1, 2]", (X.S_SQRT_SQ,), X.DISCHARGED, X.T_RANGE,
                          True)], st2.last.emitted, keys_of(st))
        return out
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


# ---------------------------------------------------------------- item 7: problem files
#
# Stage 0's S1-S3 (WHAT.md "Start here") as problem files: read by the
# untrusted loader, driven through install() and step(), and asserted
# against kernel/problems/stage0/expected.py (S0 here), which was written
# by hand before they ran. S0's strings are parsed and compared as trees,
# as p1_expected's are. Every state a check reads is one the loader got back
# from the kernel; the loader builds none.

def s0_base(proof):
    """S0 keys GOALS, ECHO, THEOREMS and NUMERIC by problem: S3-ring is S3."""
    return proof.split("-")[0]


def s0_key(prop, dom):
    return T.parse_judgement(S0.judgement_string(prop, dom), S0.SIG)


# (before the switch, after it): expected.py's names for each table
_S0_TABLES = {
    "OBLIGATIONS": ("EXPECTED_OBLIGATIONS", "DISCHARGE_OBLIGATIONS"),
    "FINAL": ("FINAL_TRACKER", "DISCHARGE_FINAL_TRACKER"),
    "ADMISSIONS": ("ADMISSIONS", "DISCHARGE_ADMISSIONS"),
    "VERDICTS": ("VERDICTS", "DISCHARGE_VERDICTS")}


def s0_table(name):
    """Stage 0's table under DISCHARGE_SWITCH: expected.py's DISCHARGE_*
    counterpart once discharge is wired (PF17)."""
    return getattr(S0, _S0_TABLES[name][DISCHARGE_WIRED])


class Book:
    """One set of problem files and the expected.py tables that state them:
    stage 0's S1-S3 (sections 1-11), stage 1's int_subst files (section 12,
    INT_SUBST_*, p1_expected INT_SUBST_SWITCH), or the consolidation's QC1
    (section 13, CONSOLIDATION_*, p1_expected CONSOLIDATION_SWITCH). Item
    7's checks read everything through one, so every set is asserted the
    same way. `stage1` is true of both later sets: tables prefixed, files
    under kernel/problems/<dir>/, steps' DERIV rows keyed (proof, step), no
    USED_ENTRIES."""

    PREFIX = {"stage0": "", "stage1": "INT_SUBST_", "consolidation": "CONSOLIDATION_"}

    def __init__(self, kind):
        pre = self.PREFIX[kind]
        self.kind, self.stage1, self.SIG, self.pre = kind, kind != "stage0", S0.SIG, pre
        for name in ("PROOF_FILES", "GOALS", "ECHO", "STEPS", "THEOREMS",
                     "ANSWERS", "NUMERIC"):
            setattr(self, name, getattr(S0, pre + name))
        self.root = os.path.dirname(STAGE0_DIR) if self.stage1 else STAGE0_DIR
        self.EXPECTED_REFUSALS = () if self.stage1 else S0.EXPECTED_REFUSALS
        self.WRONG_ANSWERS = {
            "stage0": lambda: S0.WRONG_ANSWERS,
            "stage1": lambda: S0.INT_SUBST_WRONG_ANSWERS + S0.INT_SUBST_S0_REFUSALS,
            "consolidation": lambda: CONSOLIDATION_WRONG_ANSWERS}[kind]()

    def table(self, name):
        if REGULARITY:  # stage0/expected.py section 14, every problem file
            return getattr(S0, {"OBLIGATIONS": "REG_OBLIGATIONS", "FINAL": "REG_FINAL_TRACKER",
                                "ADMISSIONS": "REG_ADMISSIONS",
                                "VERDICTS": "REG_VERDICTS"}[name])
        if not self.stage1:
            return s0_table(name)
        return getattr(S0, self.pre + {"OBLIGATIONS": "OBLIGATIONS",
                                       "FINAL": "FINAL_TRACKER",
                                       "ADMISSIONS": "ADMISSIONS",
                                       "VERDICTS": "VERDICTS"}[name])

    def certs(self, proof):
        if not DISCHARGE_WIRED:
            return None
        table = getattr(S0, self.pre + "EXPECTED") if self.stage1 else \
            S0.DISCHARGE_EXPECTED
        rows = dict(table[proof])
        if REGULARITY:
            rows.update(S0.REG_EXPECTED[proof])
        return {s0_key(p, d): c for (p, d), (_, c) in rows.items()}

    def deriv(self, proof, sid):
        """The DERIV row of a step: stage 0 keys its one ftc by proof, the
        later sets each ftc and int_subst step by (proof, step)."""
        if self.stage1:
            return getattr(S0, self.pre + "DERIV")[(proof, sid)]
        return S0.DERIV[proof]


def book(stage1=False, kind=None):
    return Book(kind or ("stage1" if stage1 else "stage0"))


def s0_file(proof, B=None):
    """(Problem, the loader's name for the proof) for a PROOF_FILES row."""
    B = B or book()
    where = B.PROOF_FILES[proof]
    problem = LD.load(os.path.join(B.root, where[0]))
    return problem, (LD.REFERENCE if where[1] == "reference_proof" else where[2])


def s0_sources(proof, B=None):
    out = {}
    for obs in (B or book()).table("OBLIGATIONS")[proof].values():
        for prop, dom, sources, *_ in obs:
            out.setdefault(s0_key(prop, dom), set()).update(sources)
    return out


def s0_entries_problems():
    """NEW_ENTRIES' pinned statements against entries.py, and every entry a
    proof uses is in ENTRIES."""
    out = []
    for name, e in S0.NEW_ENTRIES.items():
        got = EN.ENTRIES.get(name)
        if got is None:
            out.append(f"{name} is not in ENTRIES")
            continue
        if got.statement != T.parse_judgement(e["statement"], S0.SIG):
            out.append(f"{name}: statement {show(got.statement)}")
        if tuple(got.schema) != tuple(e["schema"]):
            out.append(f"{name}: schema {got.schema}")
        for side in ("lhs", "rhs"):
            if side in e and getattr(got.statement, side) != T.parse_term(e[side], S0.SIG):
                out.append(f"{name}: {side} {show(getattr(got.statement, side))}")
        if tuple(got.hyps) != tuple(T.parse_judgement(h, S0.SIG) for h in e["hyps"]):
            out.append(f"{name}: hyps {[show(h) for h in got.hyps]}")
    for proof, names in S0.USED_ENTRIES.items():
        out += [f"{proof} uses {n}, which is not in ENTRIES"
                for n in names if n not in EN.ENTRIES]
    return out


def s0_sign_fact_problems():
    """The tagger's sign facts are ENTRIES' statements, e_gt_one's for
    e_const as pi_pos's for pi, so the tags that cite them come out by rule
    (FINDINGS: 'e_gt_one in the tagger's sign-fact table')."""
    out = []
    if TG.SIGN_FACTS.get("e_const", (None,))[0] != "e_gt_one":
        out.append(f"SIGN_FACTS['e_const'] is {TG.SIGN_FACTS.get('e_const')!r}")
    for const, (name, fact) in TG.SIGN_FACTS.items():
        e = EN.ENTRIES.get(name)
        if e is None or e.statement != fact:
            out.append(f"SIGN_FACTS[{const!r}] = {name}: {show(fact)}, but ENTRIES "
                       f"has {show(e.statement) if e else 'no such entry'}")
    return out


def s0_file_problems(proof, B=None):
    """The file itself: its goal and declarations are the data's, its steps'
    ids and moves are STEPS', ftc's F (and int_subst's sub) is DERIV's, and,
    for stage 0, the entries its steps name plus the cites in its run's tags
    are USED_ENTRIES'."""
    B = B or book()
    problem, name = s0_file(proof, B)
    out = []
    if problem.sig != B.SIG:
        out.append(f"declarations.functions is {problem.sig}, expected {B.SIG}")
    if problem.goal() != T.parse_goal(B.GOALS[proof], B.SIG):
        out.append(f"goal {problem.goal_text!r}, expected {B.GOALS[proof]!r}")
    steps = problem.proofs[name]
    got = [(s["id"], s["move"]) for s in steps]
    want = [(s["id"], s["move"]) for s in B.STEPS[proof]]
    if got != want:
        out.append(f"steps {got}, expected {want}")
    for s in steps:
        arg = {"ftc": "F", "int_subst": "sub"}.get(s["move"])
        if arg and T.parse_term(s["args"][arg], B.SIG) != \
                T.parse_term(B.deriv(proof, s["id"])["F"], B.SIG):
            out.append(f"{s['id']}: {arg} is {s['args'][arg]!r}, DERIV has "
                       f"{B.deriv(proof, s['id'])['F']!r}")
    results, _ = LD.replay(problem, name)
    if B.stage1:  # expected.py's section 12 states no USED_ENTRIES
        return out
    used = {s["args"]["entry"] for s in steps if "entry" in s["args"]}
    for _, r in results:
        if isinstance(r, K.ProofState):
            used |= {c for ob in r.last.emitted for c in ob.tag[1]
                     if c in EN.ENTRIES}
    if used != set(S0.USED_ENTRIES[proof]):
        out.append(f"entries used {sorted(used)}, expected "
                   f"{sorted(S0.USED_ENTRIES[proof])}")
    return out


def s0_run(proof, B=None):
    """Replay one problem-file proof through the loader and compare
    everything. Items in run.found: 6 the echo, 1 the outcome, 2 the
    obligations, as in P1's rows; all are recorded under item 7."""
    run = Run(proof)
    try:
        _s0_run(run, B or book())
    except Mismatch as m:
        run.miss(m.item, m.where, m.detail)
    return run


def _s0_run(run, B):
    proof, base = run.name, s0_base(run.name)
    exp, steps = B.table("OBLIGATIONS")[proof], B.STEPS[proof]
    certs = B.certs(proof)
    if B.EXPECTED_REFUSALS:
        raise Mismatch(1, (proof, "EXPECTED_REFUSALS"),
                       "names refusals, which this check does not replay")
    problem, name = s0_file(proof, B)
    results, _ = LD.replay(problem, name)
    # Each step is compared as it comes, and a refusal stops the run where
    # it happens, as a PROOFS run does (take), so that what was built
    # before it is still checked.
    if not isinstance(results[0][1], K.ProofState):
        raise Mismatch(1, (proof, "goal", "refused"), describe(results[0][1]))
    if len(results) != len(steps) + 1 and isinstance(results[-1][1], K.ProofState):
        raise Mismatch(1, (proof, "steps"), f"{len(results) - 1} steps fed, "
                       f"expected {len(steps)}")
    installed = T.parse_goal(B.GOALS[proof], B.SIG)
    st = results[0][1]
    run.state = st
    echo = T.show_goal(st.goal)
    if echo != B.ECHO[base]:
        run.miss(6, (proof, "echo"), f"{echo!r}, expected {B.ECHO[base]!r}")
    if T.parse_goal(echo, B.SIG) != st.goal:
        run.miss(6, (proof, "echo", "reparse"), "does not parse back to the tree")
    if st.goal != installed or st.last.move != "install":
        run.miss(1, (proof, "goal", "installed"), f"got {show(st.goal)}, "
                 f"last.move {st.last.move!r}")
    compare_emitted(run.miss, proof, "goal", exp["goal"], st.last.emitted,
                    frozenset(), keyf=s0_key, certs=certs)
    seen = list(st.last.emitted)
    for s, (sid, st) in zip(steps, results[1:]):
        if not isinstance(st, K.ProofState):
            raise Mismatch(1, (proof, sid, "refused"), describe(st))
        prev, where, last = run.state, (proof, sid), st.last
        run.state = st
        if sid != s["id"]:
            raise Mismatch(1, where + ("id",), f"expected step {s['id']}")
        if last.move != s["move"]:
            run.miss(1, where + ("move",), f"last.move is {last.move!r}")
        want = None if s["goal_after"] is None else T.parse_goal(s["goal_after"], B.SIG)
        if st.goal != want:
            run.miss(1, where + ("goal_after",), f"got {show(st.goal)}")
        if "occurrences" in s and last.occurrences != s["occurrences"]:
            run.miss(1, where + ("occurrences",),
                     f"{last.occurrences}, expected {s['occurrences']}")
        if s["move"] in ("ftc", "int_subst"):
            d = B.deriv(proof, sid)
            for what, detail in deriv_problems(d["F"], last.trace, last.output, d):
                run.miss(2, where + (what,), detail)
        compare_emitted(run.miss, proof, sid, exp[sid], last.emitted,
                        keys_of(prev), keyf=s0_key, certs=certs)
        seen += last.emitted
    obs = st.obligations()
    for suffix, detail in tracker_problems(obs, B.table("FINAL")[proof],
                                           s0_sources(proof, B), keyf=s0_key,
                                           certs=certs):
        run.miss(2, ("FINAL_TRACKER", proof) + suffix, detail)
    nones = {T.show(o.key) for o in seen + list(obs)
             if o.status == K.ADMITTED and o.tag[0] == "none"}
    for k in sorted(nones):
        run.miss(2, ("NONE_TAG", proof, k), "admitted and tagged none")
    if st.goal is not None:
        raise Mismatch(1, (proof, "closed"), f"goal still open: {show(st.goal)}")
    run.n = sum(o.status == K.ADMITTED for o in obs)
    if run.n != B.table("ADMISSIONS")[proof]:
        run.miss(1, ("N", proof), f"{run.n} admissions, expected "
                 f"{B.table('ADMISSIONS')[proof]}")
    if K.report(st) != B.table("VERDICTS")[proof]:
        run.miss(1, ("VERDICT", proof), f"{K.report(st)!r}, expected "
                 f"{B.table('VERDICTS')[proof]!r}")
    theorem = T.parse_goal(B.THEOREMS[proof], B.SIG)
    if st.theorem != theorem:
        run.miss(1, ("THEOREM", proof), f"got {show(st.theorem)}")
    if T.instantiate(installed, T.parse_term(B.ANSWERS[proof], B.SIG)) != theorem:
        run.miss(1, ("ANSWER", proof), "ANSWERS disagrees with THEOREMS")


def s0_direct_problems(proof, B=None):
    """The loader against a drive that does not use it: the same file's
    steps fed by this script's own build_args, with fresh handles. Each
    step's goal and emissions, and the final tracker, must be the same."""
    B = B or book()
    problem, name = s0_file(proof, B)
    results, _ = LD.replay(problem, name)
    st, handles, out = install(B.GOALS[proof], (proof, "goal")), {}, []
    pairs = [("goal", st)]
    for s in problem.proofs[name]:
        st = take(st, s["move"], s["args"], handles, (proof, s["id"]))
        pairs.append((s["id"], st))
    if [sid for sid, _ in results] != [sid for sid, _ in pairs]:
        return [f"the loader fed {[sid for sid, _ in results]}"]
    for (sid, a), (_, b) in zip(results, pairs):
        if a.goal != b.goal or a.last.emitted != b.last.emitted:
            out.append(f"{sid}: the loader's state differs from the direct drive's")
    if results[-1][1].obligations() != pairs[-1][1].obligations():
        out.append("the final trackers differ")
    return out


def s0_numeric_problems(proof, B=None):
    """A math-module check that the answer is the integral, sharing no code
    with the kernel: NUMERIC against the theorem's right side, and against
    Simpson's rule on the goal's integral."""
    B = B or book()
    want, out = B.NUMERIC[s0_base(proof)], []
    answer = value(T.parse_goal(B.THEOREMS[proof], B.SIG)[0].rhs)
    if abs(answer - want) > 1e-12 * max(1.0, abs(want)):
        out.append(f"the answer is {answer!r}, NUMERIC says {want!r}")
    integral = value(T.parse_goal(B.GOALS[proof], B.SIG)[0].lhs)
    if abs(integral - want) > 1e-4:
        out.append(f"Simpson gives {integral!r}, NUMERIC says {want!r}")
    return out


def s0_wrong_answer_problems(w, B=None):
    """One S0.WRONG_ANSWERS case: refused with its code, the state unchanged
    (E13), its message where it gives one, and the residual equal to the
    expected one under `compare` and not zero (E14). The move goes through
    the loader, as a file's would."""
    B = B or book()
    if "state" in w:
        problem, name = s0_file(w["state"][0], B)
        results, handles = LD.replay(problem, name, through=w["state"][1])
        st, sig = results[-1][1], problem.sig
        if not isinstance(st, K.ProofState) or results[-1][0] != w["state"][1]:
            return [f"the replay to {w['state']} stopped: {describe(st)}"]
    else:
        st, handles, sig = install(w["goal"], (w["id"], "goal")), {}, S0.SIG
    before, before_goal = st.obligations(), st.goal
    move, args = w["move"]
    r = LD.feed(st, {"move": move, "args": args}, handles, sig)
    if isinstance(r, K.ProofState):
        return ["accepted: the wrong answer went through"]
    out = refusal_problems_of(r, w)
    if st.obligations() != before or st.goal != before_goal:
        out.append("the refused step changed the state (E13)")
    if "residual" not in w:  # a decided-false refusal carries none
        return out
    if r.residual is None:
        return out + ["the refusal carries no residual"]
    method, names = w["compare"]
    if method == "tree":
        # E27's residual is the offending subterm, not lhs - rhs, so it is
        # compared as a tree, and the message through E27_MESSAGES filled
        # with show(residual) and the entry, as p1_expected's E27 cases are.
        e27 = {"at": w["residual"], "entry": w.get("entry"),
               "clause": "a" if w.get("entry") is not None else "b"}
        return out + e27_refusal_problems(
            r, e27, lambda s: T.parse_term(s, S0.SIG))
    facts = fact_pairs(st, handles, names)
    ok, note = equal_by(method, r.residual, T.parse_term(w["residual"], S0.SIG), facts)
    if not ok:
        out.append(f"residual {show(r.residual)} is not {w['residual']} under "
                   f"{method}{note}")
    zero, note = equal_by(method, r.residual, T.Num(0), facts)
    if zero or note:
        out.append(f"residual {show(r.residual)} is zero under {method}{note}")
    return out


def s0_loader_problems():
    """The loader resolves ["handle", name] to the handle the kernel minted
    for that bind, which no S1-S3 step needs: (sqrt 3)^2 == ?A by fact
    sqrt_sq_val then close by field with it, whose one obligation 3 >= 0 is
    discharged, so the report is 'Proved.'. It refuses what is not a
    calc-problem/0 file (PF2's closed key set) and a fact no earlier step
    bound, rather than guess."""
    import tempfile
    with open(os.path.join(STAGE0_DIR, "S1.json"), encoding="utf-8") as f:
        good = json.load(f)
    with_fact = {**good, "goal": "(sqrt 3)^2 == ?A", "reference_proof": [
        {"id": "s1", "move": "fact",
         "args": {"entry": "sqrt_sq_val", "inst": {"a": "3"}, "bind": "h"}},
        {"id": "s2", "move": "close",
         "args": {"value": "3", "check": "field", "facts": [["handle", "h"]]}}]}
    step = good["reference_proof"][0]
    bad = {"unknown key": {**good, "hint": "u = x^2"},
           "missing key": {k: v for k, v in good.items() if k != "goal"},
           "wrong format": {**good, "format": "calc-problem/1"},
           "other schema": {**good, "answer_schema": "closed + erf"},
           "top-level list": [good],
           "reference_proof as a string": {**good, "reference_proof": "ftc; close"},
           "step without id": {**good, "reference_proof": [
               {k: v for k, v in step.items() if k != "id"}]},
           "duplicate goal key": '{"goal": "x == ?A", ' + json.dumps(good)[1:],
           "extra step key": {**good, "reference_proof": [{**step, "by": "ring"}]},
           "extra declarations key": {**good, "declarations": {"functions": {},
                                                               "variables": {}}},
           "functions as a list": {**good, "declarations": {"functions": ["f"]}},
           "alternative named reference": {**good, "alternative_proofs": {
               "reference": {"why": "", "steps": good["reference_proof"]}}}}
    out = []
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "p.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(with_fact, f)
        results, handles = LD.replay(LD.load(path))
        st = results[-1][1]
        if not isinstance(st, K.ProofState) or st.goal is not None:
            out.append(f"the fact proof did not close: {describe(st)}")
        elif (K.report(st) != "Proved." or handles.get("h") is not results[1][1].last.handle
              or st.theorem != T.parse_goal("(sqrt 3)^2 == 3", S0.SIG)):
            out.append(f"the fact proof reports {K.report(st)!r}, theorem "
                       f"{show(st.theorem)}")
        for label, data in bad.items():
            with open(path, "w", encoding="utf-8") as f:
                f.write(data if isinstance(data, str) else json.dumps(data))
            try:
                LD.load(path)
                out.append(f"{label}: loaded")
            except ValueError:
                pass
            except Exception as e:  # noqa: BLE001 -- the docstring says ValueError
                out.append(f"{label}: raised {type(e).__name__}, not ValueError")
    st = install(S0.GOALS["S1"], ("loader", "goal"))
    try:
        LD.feed(st, {"move": "close", "args": {"value": "2", "check": "field",
                                               "facts": [["handle", "h"]]}}, {}, {})
        out.append("an unbound ['handle', 'h'] was fed")
    except ValueError:
        pass
    return out


def s1_floor_problems(B=None):
    """A later set's floor (INT_SUBST_SWITCH for stage1/, CONSOLIDATION_SWITCH
    for consolidation/): its directory holds exactly the files its
    PROOF_FILES names, and every one of its tables is keyed by the same
    proofs, and its DERIV by their ftc and int_subst steps, so a new file
    or a dropped row cannot pass unchecked."""
    B, out = B or book(True), []
    want, pre = set(B.PROOF_FILES), B.pre
    for table in ("GOALS", "ECHO", "STEPS", "THEOREMS", "OBLIGATIONS", "EXPECTED",
                  "FINAL_TRACKER", "ADMISSIONS", "VERDICTS", "ANSWERS", "NUMERIC"):
        if set(getattr(S0, pre + table)) != want:
            out.append(f"{pre + table} is keyed {sorted(getattr(S0, pre + table))}")
    steps = {(p, s["id"]) for p, rows in B.STEPS.items() for s in rows
             if s["move"] in ("ftc", "int_subst")}
    if set(getattr(S0, pre + "DERIV")) != steps:
        out.append(f"{pre}DERIV is keyed {sorted(getattr(S0, pre + 'DERIV'))}")
    named = {row[0] for row in B.PROOF_FILES.values()}
    dirs = {n.split("/")[0] for n in named} | {B.kind}
    files = {f"{d}/{f}" for d in dirs for f in os.listdir(os.path.join(B.root, d))
             if f.endswith(".json")}
    if files != named:
        out.append(f"{'/, '.join(sorted(dirs))}/ holds {sorted(files)}, "
                   f"{pre}PROOF_FILES names {sorted(named)}")
    return out


def s0_floor_problems():
    """Item 7 covers exactly S1, S2, S3 and S3-ring, every table is keyed
    by those four, and every problem file in stage0/ is one PROOF_FILES
    names, so a new file or a dropped row cannot pass unchecked."""
    want, out = {"S1", "S2", "S3", "S3-ring"}, []
    if set(S0.PROOF_FILES) != want:
        out.append(f"PROOF_FILES covers {sorted(S0.PROOF_FILES)}, expected {sorted(want)}")
    for table in ("STEPS", "EXPECTED_OBLIGATIONS", "FINAL_TRACKER", "ADMISSIONS",
                  "VERDICTS", "ANSWERS", "DERIV", "GOALS", "THEOREMS", "USED_ENTRIES"):
        if set(getattr(S0, table)) != want:
            out.append(f"{table} is keyed {sorted(getattr(S0, table))}")
    files = {f for f in os.listdir(STAGE0_DIR) if f.endswith(".json")}
    named = {row[0] for row in S0.PROOF_FILES.values()}
    if files != named:
        out.append(f"stage0/ holds {sorted(files)}, PROOF_FILES names {sorted(named)}")
    return out


# Two of the P1 seams run against the problem files, each in a child process
# through the same patches (ARCHITECTURE.md §7). The expected locations are
# derived from stage0/expected.py's rows by the rule each seam breaks: with
# ln's former gone, every `u > 0` that ln owes as a former disappears (the
# integrand's and F's x > 0 on [1, e_const], and the new goal's e_const > 0
# and 1 > 0); with d_ln emitting nothing, d_ln's x > 0 on (1, e_const) does.
# S1 and S2 hold no ln and must be unaffected.
S0_SEAMS = {
    "no_ln_former": {
        "kind": "mutate",
        "caught_by": [(p, sid, prop, dom) for p in ("S3", "S3-ring")
                      for sid, prop, dom in (("goal", "x > 0", "[1, e_const]"),
                                             ("s1", "x > 0", "[1, e_const]"),
                                             ("s1", "e_const > 0", "true"),
                                             ("s1", "1 > 0", "true"))]
                     + [("N", "S3"), ("N", "S3-ring")],
        "admissions": {"S1": 3, "S2": 3, "S3": 7, "S3-ring": 6}},
    "d_ln_emits_nothing": {
        "kind": "plant",
        "caught_by": [(p, "s1", what) for p in ("S3", "S3-ring")
                      for what in ("trace_emits", "deriv_emits")]
                     + [(p, "s1", "x > 0", "(1, e_const)") for p in ("S3", "S3-ring")]
                     + [("N", "S3"), ("N", "S3-ring")],
        "admissions": {"S1": 3, "S2": 3, "S3": 8, "S3-ring": 7}},
}


def s0_seam_child(name):
    """`--s0-seam NAME`: every S0 proof under one S0_SEAMS patch. Prints
    {"mismatches": [...], "admissions": {proof: N}} and exits 0, or 2 on a
    crash, as child() does."""
    if K is None or S0 is None:
        print(KERNEL_ERROR or STAGE0_ERROR, file=sys.stderr)
        return 2
    try:
        from unittest import mock
        kind = S0_SEAMS[name]["kind"]
        found, admissions = [], {}
        with (seam_patch if kind == "plant" else mutation_patch)(name, mock):
            for proof in S0.PROOF_FILES:
                run = s0_run(proof)
                found += [where for _, where, _ in run.found]
                admissions[proof] = run.n
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions}))
    return 0


def s0_seam_switched(name, case):
    """S0_SEAMS under DISCHARGE_SWITCH: every key either seam removes was
    discharged, so N no longer moves (DISCHARGE_S0_SEAMS): the N locations
    go, the list locations stay, and the admissions are expected.py's."""
    if not DISCHARGE_WIRED:
        return case
    table = S0.REG_S0_SEAMS if REGULARITY else S0.DISCHARGE_S0_SEAMS
    return dict(case, caught_by=[c for c in case["caught_by"] if c[0] != "N"],
                admissions=table[name]["admissions"])


def s0_seam_problems(name, case):
    case = s0_seam_switched(name, case)
    data, out = spawn("--s0-seam", name)
    if data is None:
        return out
    for loc in case["caught_by"]:
        if tuplify(loc) not in data["mismatches"]:
            out.append(f"not caught at {' / '.join(loc)}")
    if any(p in m[:2] for m in data["mismatches"] for p in ("S1", "S2")):
        out.append("S1 or S2 changed, and neither holds ln")
    if data["admissions"] != case["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {case['admissions']}")
    return out


def s1_checks(check, kind="stage1"):
    """Item 7's rows for a later set of problem files: stage 1's int_subst
    files (INT_SUBST_SWITCH), or the consolidation's QC1
    (CONSOLIDATION_SWITCH). The same checks through its book, with its own
    floor and its wrong answers (for stage 1, S2's refused forward
    substitution too)."""
    B, runs = book(kind=kind), {}
    what = {"stage1": ("Stage 1: the int_subst problem files (expected.py section 12)",
                       "section-12", "Stage 1 wrong answers and S2's forward "
                       "substitution"),
            "consolidation": ("The consolidation: QC1 (expected.py section 13)",
                              "section-13", "QC1's wrong answers")}[kind]
    print("\n" + what[0])
    check(f"{kind}/ holds exactly {B.pre}PROOF_FILES' files, and every "
          f"{what[1]} table is keyed by them", lambda: s1_floor_problems(B))
    for proof, where in B.PROOF_FILES.items():
        print(f"\n{proof} ({' '.join(where[:2])})")
        check(f"{proof}: the file's goal, declarations, steps and substitution are "
              "expected.py's", lambda p=proof: s0_file_problems(p, B))
        try:
            run = runs[proof] = s0_run(proof, B)
        except Exception as e:  # noqa: BLE001 -- a kernel crash mid-proof
            check(f"{proof} runs", lambda e=e: ["crash: " + crash_text(e)])
            continue
        check(f"{proof}: the goal is echoed as {B.pre}ECHO",
              lambda run=run: by_item(run, 6))
        check(f"{proof}: {len(B.STEPS[proof])} steps accepted, closes with ?A := "
              f"{B.ANSWERS[proof]}, N = {B.table('ADMISSIONS')[proof]}, "
              f"'{B.table('VERDICTS')[proof]}'", lambda run=run: by_item(run, 1))
        check(f"{proof}: every step's obligations (sources, status, tag, new, "
              "reason, certificate), deriv's trace, the final tracker, no tag none",
              lambda run=run: by_item(run, 2))
        check(f"{proof}: the loader's states are a direct drive's",
              lambda p=proof: s0_direct_problems(p, B))
        check(f"{proof}: the answer is the integral (math module)",
              lambda p=proof: s0_numeric_problems(p, B))
    print("\n" + what[2])
    for w in B.WRONG_ANSWERS:
        check(f"{w['id']}: {w['what']} -> {w['refusal']}",
              lambda w=w: s0_wrong_answer_problems(w, B)
              + (s2_sub_trace_problems(w) if "deriv_trace" in w else []))
    return runs


def s2_sub_trace_problems(w):
    """INT_SUBST_S0_REFUSALS' deriv_trace: the refused step emits nothing, so
    its trace is read from deriv itself, on the range the step gives it
    (the closed [lo, hi], E38)."""
    args = w["move"][1]
    iv = T.Interval(args["new_var"], T.parse_term(args["lo"], S0.SIG), True,
                    T.parse_term(args["hi"], S0.SIG), True)
    d = DV.deriv(T.parse_term(args["sub"], S0.SIG), args["new_var"], (iv,))
    got = [(e.rule, T.show(e.subterm), tuple(sorted(map(T.show, e.emits))))
           for e in d.trace]
    want = [(r, T.show(T.parse_term(t, S0.SIG)),
             tuple(sorted(T.show(T.parse_judgement(j, S0.SIG)) for j in em)))
            for r, t, em in w["deriv_trace"]]
    return [] if got == want else [f"deriv trace {got}, expected {want}"]


def s0_checks(suite):
    """Item 7's rows."""
    def check(label, fn):
        if S0 is None:
            suite.record(7, label, [f"not run: stage 0's data or the loader did "
                                    f"not import ({STAGE0_ERROR})"])
        else:
            suite.check(7, label, fn)

    check("PROOF_FILES is exactly S1, S2, S3 and S3-ring, and covers every file "
          "in stage0/", s0_floor_problems)
    check("NEW_ENTRIES are pinned in entries.py as stated, and every used entry "
          "exists", s0_entries_problems)
    check("the tagger's sign facts are ENTRIES' statements (e_gt_one for e_const)",
          s0_sign_fact_problems)
    check("the loader resolves a fact's handle, and refuses malformed files "
          "(ValueError) and an unbound handle", s0_loader_problems)
    runs = {}
    for proof in (S0.PROOF_FILES if S0 is not None else ()):
        print(f"\n{proof} ({' '.join(S0.PROOF_FILES[proof][:2])})")
        check(f"{proof}: the file's goal, declarations, steps and entries are "
              "expected.py's", lambda p=proof: s0_file_problems(p))
        try:
            run = runs[proof] = s0_run(proof)
        except Exception as e:  # noqa: BLE001 -- a kernel crash mid-proof
            suite.record(7, f"{proof} runs", ["crash: " + crash_text(e)])
            continue
        suite.record(7, f"{proof}: the goal is echoed as ECHO", by_item(run, 6))
        suite.record(7, f"{proof}: {len(S0.STEPS[proof])} steps accepted, closes with "
                     f"?A := {S0.ANSWERS[proof]}, N = {s0_table('ADMISSIONS')[proof]}, "
                     f"'{s0_table('VERDICTS')[proof]}'", by_item(run, 1))
        suite.record(7, f"{proof}: every step's obligations (sources, status, tag, "
                     "new), deriv's trace, the final tracker, no tag none",
                     by_item(run, 2))
        check(f"{proof}: the loader's states are a direct drive's",
              lambda p=proof: s0_direct_problems(p))
        check(f"{proof}: the answer is the integral (math module)",
              lambda p=proof: s0_numeric_problems(p))
    runs.update(s1_checks(check) if S0 is not None else {})
    if S0 is not None and CONSOLIDATED:
        runs.update(s1_checks(check, "consolidation"))
    if S0 is not None:
        print("\nStage 0 wrong answers")
        for w in S0.WRONG_ANSWERS:
            check(f"{w['id']}: {w['what']} -> {w['refusal']}, residual {w['residual']}",
                  lambda w=w: s0_wrong_answer_problems(w))
        print("\nStage 0 under two P1 seams (each in a child process)")
        for name, case in S0_SEAMS.items():
            check(f"{name} ({case['kind']}) on the problem files: caught at "
                  f"{len(case['caught_by'])} location(s), S1 and S2 untouched",
                  lambda n=name, c=case: s0_seam_problems(n, c))
    return runs


# ---------------------------------------------------------------- discharge (item D)
#
# discharge.py's trusted checkers, search.py's untrusted search and
# refute.py's untrusted decided-false check, called directly through
# test_discharge.py, one case per check, beside items 1-7, which assert
# them through kernel._emit.

def discharge_checks(suite):
    """Item D's rows."""
    if TD is None:
        suite.record("D", "discharge's checks", [
            f"not run: test_discharge.py did not import ({DISCHARGE_ERROR})"])
        return
    suite.check("D", "DISCHARGE_NEW_ENTRIES pinned (sqrt_zero immediately before "
                "sqrt_sq, cos_zero after exp_one, sqrt_nonneg after it, "
                "CONSOLIDATION_ENTRIES, atan_zero, trig_norm's seven, exp_pos, unit 00's seven, then G8's three: 42), and EXACT_VALUE_ENTRIES is "
                "ENTRIES' exact values", TD.entries_problems)
    for row in TD.expected_certificates():
        where, _, tag, spec = row
        suite.check("D", f"{' / '.join(where)}: the {spec['method']} certificate is "
                    f"accepted as {tag}, and the search proposes it",
                    lambda row=row: TD.expected_problems(row))
    for c in X.DISCHARGE_MUST_REJECT:
        why = TD.REJECT_REASONS.get(c["id"])
        suite.check("D", f"DISCHARGE_MUST_REJECT {c['id']}: rejected {why}; its truth, "
                    f"and {c['if_emitted'][0]} if emitted",
                    lambda c=c: TD.must_reject_problems(c))
    for c in X.DISCHARGE_CHECKER_ACCEPTS:
        suite.check("D", f"DISCHARGE_CHECKER_ACCEPTS {c['id']}: accepted as {c['tag']}",
                    lambda c=c: TD.checker_accept_problems(c))
    suite.check("D", "hyp's member for e # 0 needs a strict item: x >= 0, 0 <= x and "
                "x <= 0 give no x # 0", TD.hyp_signed_member_problems)
    for c in TD.SQRT_FACT_MUST_REJECT:
        suite.check("D", f"SQRT_FACT_MUST_REJECT {c['id']}: rejected "
                    f"{TD.REJECT_REASONS[c['id']]}; its truth, and {c['if_emitted'][0]} "
                    "if emitted", lambda c=c: TD.must_reject_problems(c))
    for c in TD.SQRT_FACT_CHECKER_ACCEPTS:
        suite.check("D", f"SQRT_FACT_CHECKER_ACCEPTS {c['id']}: accepted as {c['tag']}",
                    lambda c=c: TD.checker_accept_problems(c))
    if REGULARITY:  # section 17: the regularity checker called directly
        suite.check("D", "REG_SIDES_LISTED is the checker's own derivation of the "
                    "sides from the natural-domain table and C1_EXTRA",
                    TD.reg_sides_listed_problems)
        for c in TD.REG_MUST_REJECT:
            suite.check("D", f"REG_MUST_REJECT {c['id']}: rejected {c['rejects_because']}; "
                        f"{c['if_emitted'][0]} if emitted",
                        lambda c=c: TD.reg_must_reject_problems(c))
        for c in TD.REG_CHECKER_ACCEPTS:
            suite.check("D", f"REG_CHECKER_ACCEPTS {c['id']}: accepted as {c['tag']}",
                        lambda c=c: TD.checker_accept_problems(c))
        for c in X.REG_DECIDED_FALSE:
            suite.check("D", f"REG_DECIDED_FALSE {c['id']}: refused by E63's "
                        "'reg_undefined'", lambda c=c: TD.reg_decided_false_problems(c))
        # the regularity review (section 18)
        rows = TD.reg_side_key_rows()
        suite.check("D", f"REG_SIDE_KEY_RULE: every side of the {len(rows)} certificates "
                    "of REG_EXPECTED (both files), REG_CASE_CERTS and REG_CHECKER_ACCEPTS "
                    "is decided on exactly with_domain(prop, key.dom)",
                    lambda: [f"{' / '.join(r[0])}: {p}" for r in rows
                             for p in TD.reg_side_key_problems(r)])
        for c in TD.REG_REVIEW_MUST_REJECT:
            suite.check("D", f"REG_REVIEW_MUST_REJECT {c['id']}: rejected "
                        f"{c['rejects_because']}; {c['if_emitted'][0]} if emitted",
                        lambda c=c: TD.reg_must_reject_problems(c))
        for c in X.REG_REVIEW_DECIDED_FALSE:
            suite.check("D", f"REG_REVIEW_DECIDED_FALSE {c['id']}: refused by E63 through "
                        "its closed side, exact message",
                        lambda c=c: TD.reg_decided_false_problems(c))
    for table in ("SIGN_PRODUCT", "CONSOLIDATION"):  # E53, E54
        for c in getattr(TD, table + "_MUST_REJECT"):
            suite.check("D", f"{table}_MUST_REJECT {c['id']}: rejected "
                        f"{TD.REJECT_REASONS[c['id']]}; its truth, and "
                        f"{c['if_emitted'][0]} if emitted",
                        lambda c=c: TD.must_reject_problems(c))
        for c in getattr(TD, table + "_CHECKER_ACCEPTS"):
            suite.check("D", f"{table}_CHECKER_ACCEPTS {c['id']}: accepted as {c['tag']}",
                        lambda c=c: TD.checker_accept_problems(c))
    for where, spec in TD.decided_false_cases():
        suite.check("D", f"{where}: obligation-decided-false, '{spec[0]}' message",
                    lambda spec=spec: TD.decided_false_problems(spec))
    for row in TD.undecided_cases():
        suite.check("D", f"{row[0]}: {row[1][0]} @ {row[1][1]} admitted {row[1][4]}, "
                    f"{row[2]!r}", lambda row=row: TD.undecided_problems(row))
    suite.check("D", "DISCHARGE_DEFINEDNESS_CASES tan_zero_true: cos 0 # 0 reads 1 # 0 "
                "with cos_zero, discharged by norm_num", TD.tan_zero_problems)
    suite.check("D", f"DISCHARGE_PROPERTY_TEST (seed {TD.SEED}): every accept of the "
                f"{len(TD.CHECKERS)} checkers holds at sampled points, every "
                "refutation is false", discharge_property_problems)


def discharge_property_problems():
    results = TD.property_results()
    print(f"          counts (accepted/evaluated/skipped): "
          f"{TD.property_summary(results)}")
    return TD.property_problems(results)


# DISCHARGE_NEW_PLANTED_BUGS, each patched into a child process through a
# seam of discharge.py or search.py (ARCHITECTURE.md §7), as PLANTED_BUGS
# are. The child runs every proof in PROOFS under the patch, as a planted
# bug's child does, and the must-reject cases and, for a bug whose caught_by
# names PROPERTY, the property test's families it names; every caught_by
# location is required, and N where the data gives it.


def discharge_seam_patch(name, mock):
    """The child's patch for one DISCHARGE_NEW_PLANTED_BUGS key: the
    mutation's own text, through the seam that holds that rule."""
    import discharge as DC
    import search as SR

    def seam(module, attr, new):
        assert callable(getattr(module, attr, None)), \
            f"seam {module.__name__}.{attr} is missing"
        return mock.patch.object(module, attr, new)

    ends, witness = DC._ends, SR._witness

    def swapped(i, iv):  # ('dom', i, 'lo') from the hi end, and back
        v, out = T.Var(iv.var), {}
        if isinstance(iv.hi, T.Term):
            out[("dom", i, "lo")] = (v, iv.hi, not iv.hi_closed)
        if isinstance(iv.lo, T.Term):
            out[("dom", i, "hi")] = (iv.lo, v, not iv.lo_closed)
        return out

    patches = {
        "farkas_ignores_strictness": (DC, "_contradicts", lambda k, strict: k <= 0),
        "farkas_allows_negative_multiplier": (DC, "_multiplier_ok",
                                              lambda m: DC._rational(m)),
        "farkas_swaps_interval_ends": (DC, "_ends", swapped),
        "farkas_closed_as_open": (DC, "_ends", lambda i, iv: {
            lab: (x, y, True) for lab, (x, y, _) in ends(i, iv).items()}),
        "farkas_any_fact": (DC, "_is_fact", lambda entry, consts: (
            type(entry.statement) is T.Rel and entry.statement.op in DC.ORDERINGS)),
        "farkas_no_goal_needed": (DC, "_goal_used", lambda mults: True),
        "sign_skips_ring": (DC, "_sign_identity", lambda g, total: True),
        "sign_zero_constant_strict": (DC, "_constant_ok", lambda c0, strict: c0 >= 0),
        "sign_any_exponent": (DC, "_square_ok", lambda c, s, k: (
            DC._rational(c) and type(k) is int and k >= 1 and DC._plain(s))),
        "product_skips_parity": (DC, "_parity_ok", lambda c, rels: True),
        "product_skips_children": (DC, "_factors_hold", lambda dom, factors: ()),
        "cite_skips_hypotheses": (DC, "_hyps_hold", lambda dom, hyps, children: ()),
        "search_scales_wrongly": (SR, "_witness", lambda ms: witness(
            {lab: q / 2 if lab[0] == "fact" else q for lab, q in ms.items()})),
    }
    if name not in patches:
        raise KeyError(f"no seam for discharge planted bug {name!r}")
    return seam(*patches[name])


def discharge_child(name):
    """Under one DISCHARGE_NEW_PLANTED_BUGS patch (name None: the control),
    run every proof in PROOFS and print {"mismatches": [...], "admissions":
    {proof: N}}: the proofs' mismatches in caught_by's shapes, each
    must-reject case the checker accepts, and, for a bug whose caught_by
    names PROPERTY, each of those checkers the property test finds unsound,
    running those families only (item D's unpatched run of every family is
    the property test's own control). A crash exits 2."""
    if TD is None or K is None:
        print(DISCHARGE_ERROR or KERNEL_ERROR, file=sys.stderr)
        return 2
    try:
        if name is None:
            ctx, families = contextlib.nullcontext(), ()
        else:
            from unittest import mock
            ctx = discharge_seam_patch(name, mock)
            families = [c[1] for c in DISCHARGE_BUGS[name]["caught_by"]
                        if c[0] == "PROPERTY"]
        found, admissions, refusals = [], {}, {}
        with ctx:
            for p in PROOFS:
                run = run_proof(p, strict=False, out=lambda line: None)
                found += [list(where) for _, where, _ in run.found]
                refusals.update({"/".join(where): detail for _, where, detail
                                 in run.found if where[-1] == "refused"})
                admissions[p] = run.n
            found += TD.must_reject_accepted()
            if families:
                results = TD.property_results(families=families)
                found += [["PROPERTY", n] for n, st in results.items() if st.violations]
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions,
                      "refusals": refusals}))
    return 0


def discharge_plant_results():
    """Every DISCHARGE_NEW_PLANTED_BUGS child and the control, a few at a
    time: name -> spawn's (data, problems)."""
    from concurrent.futures import ThreadPoolExecutor
    names = [None, *X.DISCHARGE_NEW_PLANTED_BUGS]
    with ThreadPoolExecutor(max_workers=max(2, min(8, os.cpu_count() or 2))) as ex:
        futures = {n: ex.submit(spawn, *(("--discharge-control",) if n is None else
                                         ("--discharge-plant", n))) for n in names}
    return {n: f.result() for n, f in futures.items()}


def discharge_planted_problems(name, result):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    if name is None:
        out += [f"unpatched child found {m}" for m in sorted(found, key=str)]
        if data["admissions"] != ADMISSIONS:
            out.append(f"unpatched admissions {data['admissions']}")
        return out
    bug = DISCHARGE_BUGS[name]
    out += [f"not caught at {c}" for c in map(tuplify, bug["caught_by"])
            if c not in found]
    if "admissions" in bug and closed_admissions(data) != bug["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {bug['admissions']}")
    return out + refused_problems(data, bug) + sheet_n_problems(data, bug)


# ---------------------------------------------------------------- int_subst (item S)
#
# p1_expected's section 12 (INT_SUBST_RULE, E36-E49), asserted as
# INT_SUBST_SWITCH says: P1.1-sheet as items 1-2 assert PROOFS (it is not in
# PROOFS, E47), every INT_SUBST_ACCEPTS case with its continuation, every
# INT_SUBST_BAD_MOVES case by code, message and residual, and the planted
# bugs and re-traced seams in child processes (item 3). Stage 1's problem
# files are item 7's (s1_checks).


def subst_accept_problems(c, found=None, table="INT_SUBST_ACCEPTS"):
    """One INT_SUBST_ACCEPTS case (or INT_FLIP_ACCEPTS or E56_ACCEPTS one,
    `table`): installation's list, the move (goal after, deriv where given,
    its list with certificates and reasons), each `then` step likewise, and
    the report and theorem where given. A `then` step's own certificates
    join the case's. `found`, when given, collects each location in
    caught_by's shapes: the step's own list at (table, id, prop, dom,
    what)."""
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))
        if found is not None:
            found.append(list(where))

    # sum_second_occurrence's keys are P1.1-sheet's, key for key, and so are
    # their certificates; any other case states its own
    certs = case_certs(c) if "certificates" in c else (
        {**(case_certs({}) or {}), **proof_certs(SHEET, SUBST_TABLES)}
        if c["id"] == "sum_second_occurrence" else case_certs({}) or {})
    for step in c.get("then", ()):
        certs = {**certs, **(case_certs(step) or {})}
    reasons = case_reasons(c)
    goal_reasons = {key(p, d): r for (p, d), r in c.get("goal_reasons", {}).items()}
    st = install(c["goal"], (c["id"], "goal"))
    compare_emitted(miss, c["id"], "goal", c["goal_emits"], st.last.emitted,
                    frozenset(), certs=certs, reasons=goal_reasons)
    # a case moved in by E56_CHANGES (reverse_symbolic_old_range_reversed)
    # gives no deriv row, and its deriv is then not asserted
    first = {"move": c["move"], "goal_after": c["goal_after"], "emits": c["emits"]}
    for name in ("deriv", "occurrences"):
        if name in c:
            first[name] = c[name]
    steps = [first] + list(c.get("then", ()))
    for i, step in enumerate(steps):
        move, args = step["move"]
        where = (c["id"], move if i == 0 else f"then {i}")
        prev, st = st, take(st, move, args, {}, where)
        want = None if step["goal_after"] is None else goal(step["goal_after"])
        if st.goal != want:
            miss(1, where + ("goal_after",), f"got {show(st.goal)}")
        if "occurrences" in step and st.last.occurrences != step["occurrences"]:
            miss(1, where + ("occurrences",),
                 f"{st.last.occurrences}, expected {step['occurrences']}")
        if "deriv" in step:
            d = step["deriv"]
            for what, detail in deriv_problems(d["F"], st.last.trace, st.last.output, d):
                miss(2, where + (what,), detail)
        if i == 0:
            compare_emitted(miss, table, c["id"], step["emits"],
                            st.last.emitted, keys_of(prev), certs=certs,
                            reasons=reasons, with_dom=True)
        else:
            compare_emitted(miss, *where, step["emits"], st.last.emitted,
                            keys_of(prev), certs=certs, reasons=reasons)
    if "report" in c and K.report(st) != c["report"]:
        miss(1, (c["id"], "report"), f"{K.report(st)!r}, expected {c['report']!r}")
    if "theorem" in c and st.theorem != goal(c["theorem"]):
        miss(1, (c["id"], "theorem"), f"got {show(st.theorem)}")
    return out


def subst_sheet_numeric_problems(name):
    """INT_SUBST_NUMERIC against the theorem's right side and Simpson's rule
    on the sheet's goal, as numeric_problems does for PROOFS."""
    want, out = X.INT_SUBST_NUMERIC[name], []
    answer = value(term(X.INT_SUBST_ANSWERS[name]))
    if abs(answer - want) > 1e-12 * max(1.0, abs(want)):
        out.append(f"the answer is {answer!r}, INT_SUBST_NUMERIC says {want!r}")
    integral = value(goal(X.INT_SUBST_PROOFS[name]["goal"])[0].lhs)
    if abs(integral - want) > 1e-4:
        out.append(f"Simpson gives {integral!r}, INT_SUBST_NUMERIC says {want!r}")
    return out


def subst_checks(suite):
    """Item S's rows."""
    runs = {}
    for name in INT_SUBST_PROOFS:  # none since E52: P1.1-sheet is in PROOFS
        print(f"\n{name} (INT_SUBST_PROOFS, staged: not in PROOFS, E47)")
        try:
            run = runs[name] = run_proof(name, tb=SUBST_TABLES)
        except Exception as e:  # noqa: BLE001 -- a kernel crash mid-proof
            suite.record("S", f"{name} runs", ["crash: " + crash_text(e)])
            continue
        p = X.INT_SUBST_PROOFS[name]
        suite.record("S", f"{name}: the goal is echoed from the installed tree",
                     by_item(run, 6))
        suite.record("S", f"{name}: {len(p['steps'])} steps accepted, closes with ?A := "
                     f"{X.INT_SUBST_ANSWERS[name]}, N = {X.INT_SUBST_ADMISSIONS[name]}, "
                     f"'{X.INT_SUBST_VERDICTS[name]}'", by_item(run, 1))
        suite.record("S", f"{name}: every step's obligations (sources, status, tag, new, "
                     "reason, certificate), deriv's trace, the final tracker, no tag "
                     "none", by_item(run, 2))
        suite.check("S", f"{name}: the answer is the integral (math module)",
                    lambda n=name: subst_sheet_numeric_problems(n), needs_kernel=False)
    print("\nint_subst: accepted moves")
    for c in SUBST_ACCEPTS:
        suite.check("S", f"INT_SUBST_ACCEPTS {c['id']}"
                    + (f" -> {c['report']!r}" if "report" in c else ""),
                    lambda c=c: subst_accept_problems(c))
    print("\nint_subst: refused moves")
    for b in SUBST_BAD_MOVES:
        suite.check("S", f"INT_SUBST_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    return runs


# INT_SUBST_PLANTED_BUGS and INT_SUBST_SEAMS, each in a child process
# (`--int-subst NAME`) through the seams of ARCHITECTURE.md §7: the new
# bugs through kernel.py's int_subst functions (and discharge._sqrt_fact),
# the three re-traced seams through their existing patches. The child runs
# what int_subst reaches: P1.1-sheet, INT_SUBST_ACCEPTS and _BAD_MOVES, the
# stage-1 problem files and their wrong answers (locations prefixed 'S0',
# as the data writes them), SQRT_FACT_MUST_REJECT, and the property test's
# families a bug's caught_by names.

# INT_SUBST_PLANTED_BUGS and the review's REVIEW_PLANTED_BUGS, one set of
# child processes.
SUBST_BUGS = {**X.INT_SUBST_PLANTED_BUGS, **X.REVIEW_PLANTED_BUGS}
SUBST_SEAMS = dict(X.INT_SUBST_SEAMS)
if CONSOLIDATED:  # E56_CHANGES: one catch moves with its case, one seam re-traced
    _OLD = E56["REVIEW_PLANTED_BUGS int_subst_reverse_no_old_orient caught_by"]
    SUBST_BUGS["int_subst_reverse_no_old_orient"] = dict(
        SUBST_BUGS["int_subst_reverse_no_old_orient"],
        caught_by=[_OLD["new"] if tuplify(c) == _OLD["old"] else c
                   for c in SUBST_BUGS["int_subst_reverse_no_old_orient"]["caught_by"]])
    SUBST_SEAMS["pi_pos_not_in_constraint_set"] = _e56_planted(
        "pi_pos_not_in_constraint_set", SUBST_SEAMS["pi_pos_not_in_constraint_set"],
        "INT_SUBST_SEAMS pi_pos_not_in_constraint_set")
if REGULARITY:
    SUBST_BUGS = {n: _reg_retrace(n, b, "SUBST") for n, b in SUBST_BUGS.items()}
    SUBST_SEAMS = {n: _reg_retrace(n, b, "SUBST_SEAMS") for n, b in SUBST_SEAMS.items()}


def subst_seam_patch(name, mock):
    """The child's patch for one INT_SUBST_PLANTED_BUGS key: the mutation's
    own text, through the kernel function that holds the rule."""
    import discharge as DC
    import refute as RF
    orig = {n: getattr(K, n) for n in (
        "_select", "_new_orientation", "_forward_premises", "_new_integral")}

    def endpoint_unchecked(check, image, limit, end, source, minted, P, G, buf):
        K._emit(buf, T.with_domain(T.Rel("==", image, limit), P), source, G, (check, ()))

    def deriv_on_open(sub, x, D):
        iv = D[-1]
        return DV.deriv(sub, x, D[:-1] + (T.Interval(iv.var, iv.lo, False, iv.hi, False),))

    def c0_on_old(sub, F, D, it, P):
        old = K._range(it, P)[0]
        return [orig["_forward_premises"](sub, F, D, it, P)[0],
                (T.with_domain(T.Reg(it.body, 0), P + (old,)), K.S_SUBST_C0)]

    def literal_order(v, lo, hi):
        ql, qh = FD.rational_value(lo), FD.rational_value(hi)
        if ql is not None and qh is not None and qh < ql:
            return T.Interval(v, hi, True, lo, True)
        return T.Interval(v, lo, True, hi, True)

    def no_orientation(buf, v, lo, hi, P, G):
        return False, literal_order(v, lo, hi)

    def flips_undecided(buf, v, lo, hi, P, G):
        if FD.rational_value(lo) is not None and FD.rational_value(hi) is not None:
            return orig["_new_orientation"](buf, v, lo, hi, P, G)
        key = T.with_domain(T.Rel("<=", lo, hi), P)
        if K._settles(key):
            K._emit(buf, key, "orient", G)
            return False, T.Interval(v, lo, True, hi, True)
        return True, T.Interval(v, hi, True, lo, True)

    def sorted_limits(v, lo, hi, body, flip):
        ql, qh = FD.rational_value(lo), FD.rational_value(hi)
        if not flip and ql is not None and qh is not None and qh < ql:
            return T.Integral(v, hi, lo, body)
        return orig["_new_integral"](v, lo, hi, body, flip)

    def first_binding(g, var, k):
        for i in itertools.count():
            try:
                return orig["_select"](g, var, i)
            except T.Refused as r:
                if r.code == "int-subst-no-integral":
                    return orig["_select"](g, var, k)

    def reverse_unchecked(check, body, Fg, dg, f, minted, D, G, buf):
        K._emit(buf, T.with_domain(T.Rel("==", body, T.Mul(Fg, dg)), D),
                K.S_SUBST_INT, G, ("deriv+" + check, ()))

    def reverse_on_new_range(sub, Fg, D, f, v, lo, hi, P):
        return [(T.with_domain(T.Reg(sub, 1), D), K.S_SUBST_C1),
                (T.with_domain(T.Reg(f, 0), P + (literal_order(v, lo, hi),)),
                 K.S_SUBST_C0)]

    atom_fact = DC._atom_fact  # the sqrt label is ATOM_FACT_RULE's since E54

    def sqrt_strict(key, label):
        c = atom_fact(key, label)
        if c is None or label[1] != DC.SQRT_FACT:
            return c
        return (c[0], c[1], True)

    def sqrt_any_u(key, label):  # any u, once the key holds some sqrt atom
        if not (len(label) == 3 and label[1] == DC.SQRT_FACT):
            return atom_fact(key, label)
        if not DC._atom_arguments(key, "sqrt"):
            return None
        return (T.App("sqrt", label[2]), T.Num(0), False)

    def old_range_unoriented(buf, it, P, G):
        return K._range(it, P)[0]

    patches = {
        "f3_no_root_candidates": (RF, "roots", lambda key, v: []),
        "int_subst_no_sub_formers": (K, "_sub_formers",
                                     lambda buf, sub, Fg, D, G, anc: None),
        "int_subst_reverse_no_old_orient": (K, "_old_range", old_range_unoriented),
        "sqrt_fact_any_u": (DC, "_atom_fact", sqrt_any_u),
        "int_subst_skips_endpoint_check": (K, "_endpoint", endpoint_unchecked),
        "int_subst_drops_phi_prime": (K, "_new_integrand", lambda F, dphi: F),
        "int_subst_deriv_on_open": (K, "_subst_deriv", deriv_on_open),
        "int_subst_C0_on_original_integrand": (K, "_forward_premises", c0_on_old),
        "int_subst_no_orientation": (K, "_new_orientation", no_orientation),
        "int_subst_flips_without_decision": (K, "_new_orientation", flips_undecided),
        "int_subst_skips_freshness": (K, "_fresh", lambda goal, v: None),
        "int_subst_sorts_new_limits": (K, "_new_integral", sorted_limits),
        "int_subst_occurrence_ignored": (K, "_select", first_binding),
        "int_subst_under_D_unchecked": (K, "_subst_under_D", lambda anc, it, terms: None),
        "int_subst_reverse_skips_check": (K, "_reverse_check", reverse_unchecked),
        "int_subst_reverse_premise_on_new_range": (K, "_reverse_premises",
                                                   reverse_on_new_range),
        "sqrt_fact_strict": (DC, "_atom_fact", sqrt_strict),
    }
    if name not in patches:
        raise KeyError(f"no seam for int_subst planted bug {name!r}")
    module, attr, new = patches[name]
    assert callable(getattr(module, attr, None)), f"seam {module.__name__}.{attr} is missing"
    return mock.patch.object(module, attr, new)


def subst_child(name):
    """`--int-subst NAME`: under one INT_SUBST_PLANTED_BUGS or INT_SUBST_SEAMS
    patch (None: the control), print {"mismatches": [...], "admissions":
    {proof: N}, "final": {...}}. A crash exits 2."""
    if K is None or S0 is None or TD is None:
        print(KERNEL_ERROR or STAGE0_ERROR or DISCHARGE_ERROR, file=sys.stderr)
        return 2
    try:
        from unittest import mock
        bug = SUBST_BUGS.get(name) or SUBST_SEAMS.get(name) or {}
        if name is None:
            ctx = contextlib.nullcontext()
        elif name in SUBST_BUGS:
            ctx = subst_seam_patch(name, mock)
        elif name in X.DEFINEDNESS_MUTATIONS:
            ctx = mutation_patch(name, mock)
        else:
            ctx = seam_patch(name, mock)
        found, admissions, final = [], {}, {}
        B1 = book(True)
        with ctx:
            for p in SUBST_PROOFS:
                run = run_proof(p, strict=False, out=lambda line: None, tb=SUBST_TABLES)
                found += [list(where) for _, where, _ in run.found]
                admissions[p] = run.n
                final[p] = None if run.n is None else [
                    [T.show(o.key), o.status, o.tag[0], list(o.tag[1])]
                    for o in run.state.obligations()]
            for table, cases, fn in (
                    ("INT_SUBST_ACCEPTS", SUBST_ACCEPTS, None),
                    ("INT_SUBST_BAD_MOVES", SUBST_BAD_MOVES, bad_move_problems),
                    ("F3_ROOTS_CASES", X.F3_ROOTS_CASES, bad_move_problems),
                    ("DISCHARGE_BAD_MOVES_ADDED", DISCHARGE_BAD_MOVES_ADDED,
                     bad_move_problems)):
                for c in cases:
                    try:
                        problems = (fn(c) if fn else subst_accept_problems(c, found))
                    except Mismatch as m:
                        problems = [str(m)]
                    if problems:
                        found.append([table, c["id"]])
            for proof in B1.PROOF_FILES:
                run = s0_run(proof, B1)
                found += [["S0", *where] for _, where, _ in run.found]
            for w in B1.WRONG_ANSWERS:
                try:
                    problems = s0_wrong_answer_problems(w, B1)
                except Mismatch as m:
                    problems = [str(m)]
                if problems:
                    found.append(["S0", w["id"]])
            # each case in full: accepted, or rejected for another reason
            found += [["SQRT_FACT_MUST_REJECT", c["id"]] for c in TD.SQRT_FACT_MUST_REJECT
                      if TD.must_reject_problems(c)]
            families = [c[1] for c in bug.get("caught_by", ()) if c[0] == "PROPERTY"]
            if families:
                results = TD.property_results(families=families)
                found += [["PROPERTY", n] for n, st in results.items() if st.violations]
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions, "final": final}))
    return 0


def subst_child_results():
    """The control and every INT_SUBST_PLANTED_BUGS and INT_SUBST_SEAMS
    child, a few at a time: name -> spawn's (data, problems)."""
    from concurrent.futures import ThreadPoolExecutor
    names = [None, *SUBST_BUGS, *SUBST_SEAMS]
    with ThreadPoolExecutor(max_workers=max(2, min(8, os.cpu_count() or 2))) as ex:
        futures = {n: ex.submit(spawn, *(("--int-subst-control",) if n is None else
                                         ("--int-subst", n))) for n in names}
    return {n: f.result() for n, f in futures.items()}


# INT_SUBST_SEAMS locations the rules do not reach, each left failing with
# its evidence until the data changes (a data_change_request). The last one,
# pi_pos_not_in_constraint_set's, was answered by E56_CHANGES (E53's content
# split closes 0 <= pi/2 by cite pi_pos).
SUBST_DATA_CHANGE_REQUESTS = {}


def subst_planted_problems(name, result):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    if name is None:
        out += [f"unpatched child found {m}" for m in sorted(found, key=str)]
        if data["admissions"] != {p: ADMISSIONS[p] for p in SUBST_PROOFS}:
            out.append(f"unpatched admissions {data['admissions']}")
        return out
    bug = SUBST_BUGS.get(name) or SUBST_SEAMS[name]
    out += [f"not caught at {c}" for c in map(tuplify, bug["caught_by"])
            if c not in found]
    if out and name in SUBST_DATA_CHANGE_REQUESTS:
        out.append(SUBST_DATA_CHANGE_REQUESTS[name])
    if "admissions" in bug and closed_admissions(data) != bug["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {bug['admissions']}")
    for proof, rows in bug.get("retagged", {}).items():
        got = {r[0]: (r[1], (r[2], tuple(r[3]))) for r in data["final"].get(proof) or []}
        for p, d, status, tag in rows:
            if got.get(T.show(key(p, d))) != (status, tag):
                out.append(f"{proof}: {p} @ {d} is {got.get(T.show(key(p, d)))}, "
                           f"expected {(status, tag)}")
    return out


# ---------------------------------------------------------------- the consolidation (item C)
#
# p1_expected's sections 13 and 14 (CONSOLIDATION_SWITCH): int_flip (E51)
# accepted and refused as INT_FLIP_RULE states it, and E56's one
# orientation rule, reversed symbolic ranges proved end to end and the order
# refused when neither is proved, each case as the int_subst cases are
# asserted; E27's reading of E54's two equations. The non-strict sign
# product (E53) and the atom labels (E54) are item D's, through
# test_discharge.py; QC1 is item 7's; the planted bugs are item 3's.

FLIP_ACCEPTS = [reg_case("INT_FLIP_ACCEPTS", c) for c in X.INT_FLIP_ACCEPTS]
FLIP_BAD_MOVES = [reg_case("INT_FLIP_BAD_MOVES", b, {}) for b in X.INT_FLIP_BAD_MOVES]
E56_ACCEPTS = [reg_case("E56_ACCEPTS", c) for c in X.E56_ACCEPTS]
E56_BAD_MOVES = [reg_case("E56_BAD_MOVES", b, {}) for b in X.E56_BAD_MOVES]
# section 15 (the consolidation review, REVIEW2_SWITCH): E57's cases and
# E56_AMENDMENTS' (the enclosing range refused and decided, and the lazy
# install asserted by its time bound); under REG_SWITCH, E57's D case
# moves to REG_E57_ACCEPTS, the enclosing range is refused at
# installation, and the lazy install decides its order (E68)
E57_ACCEPTS = [reg_case("E57_ACCEPTS", c) for c in X.E57_ACCEPTS]
E57_BAD_MOVES = [b for b in X.E57_BAD_MOVES
                 if not (REGULARITY and b["id"] == "pyth_erases_D")]


def _review_bad(b):
    ch = X.REG_CASE_CHANGES["E56_REVIEW_CASES"].get(b["id"], {})
    if REGULARITY and "new" in ch:
        return dict(b, at="install", refusal=ch["new"][1],
                    message=(ch["new"][1], ch["new"][2]))
    return b


REVIEW_BAD = [_review_bad(b) for b in X.E56_REVIEW_CASES["bad_moves"]]
REVIEW_ACCEPTS = [reg_case("E56_REVIEW_CASES", c)
                  for c in X.E56_REVIEW_CASES["accepts"] if "move" in c]
REVIEW_LAZY = [reg_case("E56_REVIEW_CASES", c)
               for c in X.E56_REVIEW_CASES["accepts"] if "timing_bound" in c]
# section 17's own cases (REG_SWITCH)
REG_Q23 = [reg_case("REG_Q23_CASES", c, {}) for c in X.REG_Q23_CASES] if REGULARITY else []
REG_Q23_REFUSALS = list(X.REG_Q23_REFUSALS) if REGULARITY else []
REG_E57_ACCEPTS = [reg_case("REG_E57_ACCEPTS", c, {})
                   for c in X.REG_E57_ACCEPTS] if REGULARITY else []
REG_INSTALL_CASES = list(X.REG_INSTALL_CASES) if REGULARITY else []
REG_BAD_MOVES = list(X.REG_BAD_MOVES) if REGULARITY else []


def lazy_install_problems(c):
    """E56_AMENDMENTS' laziness: the goal installs emitting its goal_emits
    (nothing: no key uses the range, so no order is decided), within the
    case's timing_bound of CPU time (_cpu_timed). The time is printed."""
    K._ORDER_MEMO.clear()  # timed cold: no orientation answer is remembered
    r, secs = _cpu_timed(lambda: K.install(goal(c["goal"])), c["timing_bound"])
    print(f"          installed in {secs:.4f} s of CPU time (bound {c['timing_bound']} s)")
    if not isinstance(r, K.ProofState):
        return [f"not installed: {describe(r)}"]
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    compare_emitted(miss, c["id"], "goal", c["goal_emits"], r.last.emitted,
                    frozenset(), certs=case_certs(c))
    if secs > c["timing_bound"]:
        out.append(f"took {secs:.2f} s, more than {c['timing_bound']} s")
    return out


# section 16 (the second review, SECOND_REVIEW_SWITCH)
SECOND_BAD_MOVES, E58_ACCEPTS = X.SECOND_REVIEW_BAD_MOVES, X.E58_ACCEPTS
# Section-16 cases the rules do not reach, each left failing with its
# evidence until the data changes (a data_change_request).
SECOND_REVIEW_DATA_CHANGE_REQUESTS = {
    "int_subst_reverse_limit_holds_Int":
        "data_change_request: the move's hi, Int[y = 1 .. oo] 1, holds oo, and "
        "INT_SUBST_RULE step 1 refuses a term argument holding oo 'bad-args' "
        "('lo, hi and f are Terms holding no MVar and no oo'), before step 3 "
        "and SECOND_REVIEW_RULE's test, so the case cannot be refused "
        "Int-or-D-not-normalisable as written (nor was it orientation-"
        "undecided on 45132e5: it was bad-args). Proposed: hi := '1' (the "
        "selected Int's upper limit alone then holds the Int, and the move "
        "is refused Int-or-D-not-normalisable after step 3), or an Int or D "
        "with finite limits such as 'D[y](abs y)'",
}


def second_review_bad_move_problems(b):
    out = bad_move_problems(b)
    if out and b["id"] in SECOND_REVIEW_DATA_CHANGE_REQUESTS:
        out.append(SECOND_REVIEW_DATA_CHANGE_REQUESTS[b["id"]])
    return out


def e57_halves_problems():
    """E57's step 2a tests both halves, each alone: a tree in an inst value
    only, and in the target only, are each refused, and neither is refused
    without one. Under today's ENTRIES each half is redundant through the
    moves (step 3's ring_nf, or a target that holds the inst value), so
    kernel._no_trees_erased is called directly, on both kinds of left
    side, and a check that tests only one half fails here."""
    out = []
    tree, plain = term("Int[y = 1 .. oo] 1"), term("z")
    # a limit holding a tree: unstatable too; under REG_SWITCH a D node and
    # a statable Int pass step 2a (E66 (3)), their definedness owed
    d_tree = term("Int[y = 0 .. D[x](abs x)] 1") if REGULARITY else term("D[x](abs x)")
    passing = ([("a D in inst", {"u": term("D[x](abs x)")}, plain, False),
                ("a statable Int in the target", {"u": plain},
                 T.App("sin", term("Int[y = 0 .. 1] y")), False)] if REGULARITY else [])
    for lhs in (term("(sin u)^2 + (cos u)^2"), term("atan(u)")):
        for label, inst, at, refused in (
                ("an Int in inst only", {"u": tree}, plain, True),
                ("a tree-limited Int in inst only", {"u": d_tree}, plain, True),
                ("an Int in the target only", {"u": plain}, T.App("sin", tree), True),
                ("a tree-limited Int in the target only", {"u": plain},
                 T.App("sin", d_tree), True),
                ("neither", {"u": plain}, T.App("sin", plain), False), *passing):
            try:
                K._no_trees_erased(lhs, inst, at)
                code = None
            except T.Refused as r:
                code = r.code
            want = "Int-or-D-not-normalisable" if refused else None
            if code != want:
                out.append(f"{label}, left side {show(lhs)}: {code}, expected {want}")
    return out


def order_memo_depth_problems():
    """The orientation memo never keeps an answer a RecursionError decided:
    under a recursion limit too low for the search, _settles answers False
    for a key it proves at the normal limit, and the key is not memoised,
    so the next call, at the normal limit, proves it."""
    import inspect
    k = key("0 <= pi/7 + 1/11", "true")
    old, out, low = sys.getrecursionlimit(), [], None
    # the margin above the current depth at which the search itself runs
    # out of stack, found by lowering it until _settles answers False
    for margin in range(24, 4, -1):
        K._ORDER_MEMO.pop(k, None)
        sys.setrecursionlimit(len(inspect.stack()) + margin)
        try:
            low = K._settles(k)
        except RecursionError:  # the limit is below _settles' own frames
            low = None
        finally:
            sys.setrecursionlimit(old)
        if low is False:
            break
    if low is not False:
        out.append("no recursion limit made the search fail: the check is vacuous")
    if k in K._ORDER_MEMO:
        out.append("an answer decided by a RecursionError was memoised")
    if K._settles(k) is not True:
        out.append("at the normal limit the key is not proved")
    elif K._ORDER_MEMO.get(k) is not True:
        out.append("the stable answer was not memoised")
    return out


def install_case_problems(c):
    """A REG_INSTALL_CASES case: installation's list, with its certificates
    and reasons."""
    st = install(c["goal"], (c["id"], "goal"))
    out = []

    def miss(item, where, detail):
        out.append(fmt(where, detail))

    compare_emitted(miss, c["id"], "goal", c["goal_emits"], st.last.emitted,
                    frozenset(), certs=case_certs(c), reasons=case_reasons(c))
    return out


def reg_gap_problems():
    """Every pre-regularity Reg row of every switched case has its new
    status in the data (REG_CASE_CERTS or REG_CASE_ADMITTED)."""
    return [f"data_change_request: {p} @ {d} has neither a REG_CASE_CERTS nor a "
            f"REG_CASE_ADMITTED row" for p, d in dict.fromkeys(REG_GAPS)]


def deep_case_problems(c):
    """A REG_REVIEW_DEEP_CASES goal installs with no exception and no
    refusal, owing exactly its Int's former, discharged ('reg', ()), or,
    where the case allows it, admitted with a reason in
    REG_DEEP_ADMIT_REASONS (a derivation deeper than the stack). The status
    this machine gives is printed."""
    try:
        g = goal(c["goal"])
        r = K.install(g)
    except Exception as e:  # noqa: BLE001 -- E21: the crash being guarded against
        return ["crash: " + crash_text(e)]
    if not isinstance(r, K.ProofState):
        return [f"not installed: {describe(r)}"]
    out = []
    prop, dom, sources = c["emits_one"]
    obs = r.last.emitted
    print(f"          {c['id']}: " + "; ".join(f"{o.status} {o.tag} {o.reason}" for o in obs))
    if [o.key for o in obs] != [key(prop, dom)]:
        return [f"emitted {len(obs)} keys, expected exactly the Int's former"]
    ob = obs[0]
    if frozenset(ob.sources) != frozenset(sources):
        out.append(f"sources {sorted(ob.sources)}")
    ok = (ob.status == X.DISCHARGED and ob.tag == X.T_REG_OK) or (
        len(c["status"]) > 2 and ob.status == X.ADMITTED
        and ob.reason in X.REG_DEEP_ADMIT_REASONS)
    if not ok:
        out.append(f"status {ob.status} {ob.tag} {ob.reason}")
    if K.report(r) != "Open: " + T.show_goal(g):
        out.append(f"report {K.report(r)[:60]!r}")
    return out


def regularity_checks(suite):
    """Item R's rows (section 17's own cases)."""
    suite.check("R", "every Reg row the switched cases list has its new status in "
                "the data", reg_gap_problems)
    for c in REG_Q23:
        suite.check("R", f"REG_Q23_CASES {c['id']} -> {c['report']!r}",
                    lambda c=c: subst_accept_problems(c, table="REG_Q23_CASES"))
    for b in REG_Q23_REFUSALS:
        suite.check("R", f"REG_Q23_REFUSALS {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for c in REG_E57_ACCEPTS:
        suite.check("R", f"REG_E57_ACCEPTS {c['id']} -> {c['report']!r}",
                    lambda c=c: subst_accept_problems(c, table="REG_E57_ACCEPTS"))
    for c in REG_INSTALL_CASES:
        suite.check("R", f"REG_INSTALL_CASES {c['id']}: {c['goal']}",
                    lambda c=c: install_case_problems(c))
    for b in REG_BAD_MOVES:
        suite.check("R", f"REG_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for c in X.REG_REVIEW_DEEP_CASES:  # the regularity review's crash, fixed
        suite.check("R", f"REG_REVIEW_DEEP_CASES {c['id']}: installs, owing only its "
                    "Int's former, with no exception", lambda c=c: deep_case_problems(c))
    for c in REG_ACCEPTED_MOVES:
        suite.check("R", f"REG_BAD_MOVES_CHANGED {c['id']}: accepted"
                    + (f" -> {c['report']!r}" if "report" in c else ""),
                    lambda c=c: subst_accept_problems(c, table="REG_BAD_MOVES_CHANGED"))


def _parts_feed(st, move, args, handles):
    """One section-19 step through the loader's own path (terms parsed,
    handles resolved), as a problem file's step is fed."""
    import loader
    return loader.feed(st, {"move": move, "args": args}, handles, {})


def _parts_steps(name):
    """INT_PARTS_PROOFS' steps; the three that reuse PARTS1's swap its
    close value for their own theorem's rhs."""
    c = X.INT_PARTS_PROOFS[name]
    if isinstance(c["steps"], list):
        return c["steps"]
    value = c["theorem"].rsplit("== ", 1)[1]
    base = X.INT_PARTS_PROOFS["PARTS1"]["steps"]
    return base[:-1] + [("close", {"value": value, "check": "ring",
                                   "facts": []})]


def parts_proof_problems(name):
    """INT_PARTS_PROOFS: every step accepted, then the report and theorem."""
    c, out = X.INT_PARTS_PROOFS[name], []
    st, handles = K.install(goal(c["goal"])), {}
    for n, (move, args) in enumerate(_parts_steps(name)):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    if st.theorem != goal(c["theorem"]):
        out.append(f"theorem {T.show(st.theorem)}, expected {c['theorem']}")
    return out


def parts_bad_move_problems(b):
    """INT_PARTS_BAD_MOVES: refused with the code, the state unchanged,
    and a non-zero residual where the case says so. FACT is a handle
    minted by 'fact pi_pos' on the same state."""
    st, handles, args = K.install(goal(b["goal"])), {}, dict(b["args"])
    if args.get("facts") == ["FACT"]:
        st = _parts_feed(st, "fact", {"entry": "pi_pos", "inst": {},
                                      "bind": "h"}, handles)
        args["facts"] = [["handle", "h"]]
    before = (st.goal, st.obligations())
    try:
        r = _parts_feed(st, b["move"], args, handles)
    except Exception as e:  # noqa: BLE001 -- a crash is a finding
        return ["crash: " + crash_text(e)]
    if not isinstance(r, K.Refusal):
        return [f"accepted: {K.report(r)}"]
    out = [] if r.code == b["refusal"] else [f"refused {r.code}: {r.message}"]
    if b.get("residual") and (r.residual is None
                              or FD.ring_is_zero(r.residual)):
        out.append(f"residual {r.residual!r}, expected a non-zero term")
    if (st.goal, st.obligations()) != before:
        out.append("the state changed")
    return out


def parts_file_problems():
    import loader
    here = os.path.dirname(os.path.abspath(__file__))
    p = loader.load(os.path.join(here, "problems", "parts", "P1_PARTS.json"))
    results, _ = loader.replay(p)
    st = results[-1][1]
    if isinstance(st, K.Refusal):
        return [f"{results[-1][0]} refused {st.code}: {st.message}"]
    return [] if K.report(st) == "Proved." else [K.report(st)]


def parts_review_problems(c):
    """INT_PARTS_REVIEW_CASES (E83): every step accepted, and the report is
    not the case's not_report."""
    st, handles = K.install(goal(c["goal"])), {}
    for n, (move, args) in enumerate(c["steps"]):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    return [f"reports {c['not_report']!r}"] if K.report(st) == c["not_report"] \
        else []


def ftc_scope_problems():
    """E84: F at an occurrence naming a fresh variable is 'ftc-scope'."""
    st = K.install(goal("(Int[x = 0 .. 1] x) + (Int[x = 0 .. 1] x) == ?A"))
    r = _parts_feed(st, "ftc", {"F": "x^2/2 + q", "check": "ring",
                                "facts": [], "occurrence": 1}, {})
    return [] if isinstance(r, K.Refusal) and r.code == "ftc-scope" \
        else [f"got {describe(r)}"]


def deep_term_problems():
    """E85: a term past check_goal's recursion, built by hand, is refused
    'bad-args', not raised."""
    t = T.Var("x")
    for _ in range(3000):
        t = T.Add(t, T.Num(1))
    st = K.install(goal("x == ?A"))
    try:
        r = K.step(st, "close", {"value": t, "check": "ring", "facts": ()})
    except Exception as e:  # E21: an exception out of step() is a crash
        return [f"raised {type(e).__name__}"]
    return [] if isinstance(r, K.Refusal) and r.code == "bad-args" \
        else [f"got {describe(r)}"]


def parts_checks(suite):
    for name, c in X.INT_PARTS_PROOFS.items():
        suite.check("P", f"INT_PARTS_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda n=name: parts_proof_problems(n))
    for b in X.INT_PARTS_BAD_MOVES:
        suite.check("P", f"INT_PARTS_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: parts_bad_move_problems(b))
    suite.check("P", "problems/parts/P1_PARTS.json replays to 'Proved.' "
                "(readiness P1(1) by substitution, then parts)",
                parts_file_problems)
    for c in X.INT_PARTS_REVIEW_CASES:
        suite.check("P", f"INT_PARTS_REVIEW_CASES {c['id']}: not "
                    f"{c['not_report']!r} (E83)",
                    lambda c=c: parts_review_problems(c))
    suite.check("P", "ftc at an occurrence refuses a fresh name in F "
                "(E84, ftc-scope)", ftc_scope_problems)
    suite.check("P", "a hand-built term too deep to check is refused "
                "bad-args, not raised (E85)", deep_term_problems)
    suite.check("P", "int_parts' sources and codes are the spec's",
                lambda: [s for s in X.SOURCES_INT_PARTS
                         if s not in (K.S_PARTS_INT, K.S_PARTS_U, K.S_PARTS_V)])


def improper_proof_problems(name):
    c, out = X.INT_IMPROPER_PROOFS[name], []
    st, handles = K.install(goal(c["goal"])), {}
    for n, (move, args) in enumerate(c["steps"]):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    if st.theorem != goal(c["theorem"]):
        out.append(f"theorem {T.show(st.theorem)}, expected {c['theorem']}")
    return out


def limit_case_problems(t, s, want):
    """LIMIT_CASES through limits.lim, with the kernel's own sign guess
    (kernel._settles at the empty domain) and every side condition then
    emitted and required discharged, as int_improper emits them."""
    import limits as LM
    from terms import Num, Rel, with_domain

    def sign(c):
        for g, op in ((1, ">"), (-1, "<")):
            if K._settles(with_domain(Rel(op, c, Num(0)), ())):
                return g
        return None
    try:
        value, sides = LM.lim(term(t), "x", s, sign)
    except LM.NoLimit as e:
        return [] if want is None else [f"no limit ({e}), expected {want}"]
    if want is None:
        return [f"a limit {value}, expected none"]
    for side in sides:
        buf = {}
        try:
            K._emit(buf, with_domain(side, ()), "int_improper_limit", ())
        except T.Refused as r:
            return [f"side {T.show(side)} refused {r.code}"]
        if list(buf.values())[0].status != K.DISCHARGED:
            return [f"side {T.show(side)} not discharged"]
    if want in ("oo", "-oo"):
        return [] if value == {"oo": LM.POS, "-oo": LM.NEG}[want] else [
            f"{value}, expected {want}"]
    if value in (LM.POS, LM.NEG) or not FD.ring_equal(value, term(want)):
        return [f"{value if value in (LM.POS, LM.NEG) else T.show(value)}, "
                f"expected {want}"]
    return []


def sign_case_problems(g, want):
    """E81, E82: the key emitted alone is discharged exactly when `want`;
    a refused key counts as not discharged."""
    key, buf = T.parse_judgement(g), {}
    try:
        K._emit(buf, key, "former", key.dom)
    except T.Refused:
        return [] if not want else ["refused, expected discharged"]
    got = list(buf.values())[0].status == K.DISCHARGED
    return [] if got == want else [f"discharged is {got}, expected {want}"]


def sign_reject_problems(g, c):
    import discharge as DC
    import search as SE
    sub = lambda s: SE.propose(T.parse_judgement(s))  # noqa: E731
    parts = (c["num"], c["den"])
    cert = {"method": "sign node",
            "parts": tuple((r, sub(k)) for r, k in parts)}
    tag, why = DC.verdict(T.parse_judgement(g), cert)
    return [] if tag is None else [f"accepted: {tag}"]


def improper_file_problems(name, folder="improper"):
    import loader
    here = os.path.dirname(os.path.abspath(__file__))
    p = loader.load(os.path.join(here, "problems", folder, name + ".json"))
    results, _ = loader.replay(p)
    st = results[-1][1]
    if isinstance(st, K.Refusal):
        return [f"{results[-1][0]} refused {st.code}: {st.message}"]
    return [] if K.report(st) == "Proved." else [K.report(st)]


def improper_checks(suite):
    for name, c in X.INT_IMPROPER_PROOFS.items():
        suite.check("I", f"INT_IMPROPER_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda n=name: improper_proof_problems(n))
    for b in X.INT_IMPROPER_BAD_MOVES:
        suite.check("I", f"INT_IMPROPER_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: parts_bad_move_problems(b))
    for t, s, want in X.LIMIT_CASES:
        suite.check("I", f"LIMIT_CASES {t} as x -> {'oo' if s > 0 else '-oo'}: "
                    f"{want}", lambda t=t, s=s, w=want: limit_case_problems(t, s, w))
    for g, want in X.QUOTIENT_CASES + X.SIGN_NODE_CASES:
        suite.check("I", f"sign node (E81, E82): {g} -> "
                    f"{'discharged' if want else 'not discharged'}",
                    lambda g=g, w=want: sign_case_problems(g, w))
    for g, c, why in X.QUOTIENT_MUST_REJECT:
        suite.check("I", f"sign node must reject: {g} ({why})",
                    lambda g=g, c=c: sign_reject_problems(g, c))
    for c in X.INT_IMPROPER_REVIEW_CASES:
        suite.check("I", f"INT_IMPROPER_REVIEW_CASES {c['id']} -> "
                    f"{c['refusal']} ({c['why'].split(':')[0]})",
                    lambda c=c: trig_bad_move_problems(c))
    for name in ("P5", "P2"):
        suite.check("I", f"problems/improper/{name}.json replays to 'Proved.'",
                    lambda n=name: improper_file_problems(n))


def _trig_run(goal_text, steps):
    """Install and feed steps through the loader's argument path; the last
    state, or the first Refusal with its step index."""
    st = K.install(goal(goal_text))
    for n, (move, args) in enumerate(steps):
        r = _parts_feed(st, move, args, {})
        if isinstance(r, K.Refusal):
            return r, n
        st = r
    return st, None


def trig_proof_problems(name):
    """TRIG_NORM_PROOFS: accepted, the report and theorem, trig_norm's
    entries among the ftc_D cites (E88), and TRIG_TAN's obligation."""
    c = X.TRIG_NORM_PROOFS[name]
    st, n = _trig_run(c["goal"], c["steps"])
    if n is not None:
        return [f"step {n} refused {st.code}: {st.message}"]
    out = []
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    if st.theorem != goal(c["theorem"]):
        out.append(f"theorem {T.show(st.theorem)}, expected {c['theorem']}")
    tags = [o.tag for o in st.obligations() if "ftc_D" in o.sources]
    if not tags or set(tags[0][1]) != set(c["trig"]):
        out.append(f"ftc_D tags {tags}, expected cites {c['trig']}")
    if "trig_obligation" in c:
        got = [T.show(o.key) for o in st.obligations()
               if "trig_norm" in o.sources]
        if got != [c["trig_obligation"]]:
            out.append(f"trig_norm obligations {got}, expected "
                       f"[{c['trig_obligation']!r}]")
    return out


def trig_bad_move_problems(b):
    st = K.install(goal(b["goal"]))
    move, args = b["move"]
    r = _parts_feed(st, move, args, {})
    out = refusal_problems_of(r, b)
    if "residual" in b and isinstance(r, K.Refusal) and r.residual is not None \
            and not equal_by("ring", r.residual, term(b["residual"]))[0]:
        out.append(f"residual {T.show(r.residual)}, expected {b['residual']}")
    return out


def taylor_proof_problems(c):
    """TAYLOR_PROOFS: every step accepted through the loader's path, then
    the report, and the theorem is the goal itself (E96)."""
    st, handles = K.install(goal(c["goal"])), {}
    for n, (move, args) in enumerate(c["steps"]):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    out = []
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    if st.theorem != goal(c["goal"]):
        out.append(f"theorem {T.show(st.theorem)}, expected the goal")
    return out


def taylor_bound_problems(c):
    """TAYLOR_BOUND_CASES: the setup accepted, then the bound refused."""
    st, handles = K.install(goal(c["goal"])), {}
    for n, (move, args) in enumerate(c["steps"]):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"setup step {n} ({move}) refused {st.code}"]
    move, args = c["move"]
    r = _parts_feed(st, move, args, handles)
    out = refusal_problems_of(r, c)
    if c.get("residual") and isinstance(r, K.Refusal) and r.residual is None:
        out.append("no residual")
    return out


def taylor_install_problems(b):
    r = K.install(goal(b["goal"]))
    if b["refusal"] is None:
        return [] if isinstance(r, K.ProofState) else [f"got {describe(r)}"]
    return refusal_problems_of(r, b)


def reg_ck_problems(key_text, want):
    """REG_CK_CASES: the Reg emitted as a step emits it."""
    from terms import parse_judgement
    buf = {}
    k = parse_judgement(key_text)
    K._emit(buf, k, "former", k.dom)
    got = buf[k].status
    return [] if got == want else [f"{got}, expected {want}"]


def taylor_file_problems(name):
    return improper_file_problems(name, folder="taylor")


def taylor_checks(suite):
    for name, c in X.TAYLOR_PROOFS.items():
        suite.check("L", f"TAYLOR_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda c=c: taylor_proof_problems(c))
    for b in X.TAYLOR_BAD_MOVES:
        if b.get("install"):
            suite.check("L", f"TAYLOR_BAD_MOVES {b['id']} -> installs",
                        lambda b=b: taylor_install_problems(b))
            continue
        suite.check("L", f"TAYLOR_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: trig_bad_move_problems(
                        {k: v for k, v in b.items() if k != "residual"}))
    for c in X.TAYLOR_BOUND_CASES:
        suite.check("L", f"TAYLOR_BOUND_CASES {c['id']} -> {c['refusal']}",
                    lambda c=c: taylor_bound_problems(c))
    for k, want in X.REG_CK_CASES:
        suite.check("L", f"REG_CK_CASES {k} -> {want} (E100)",
                    lambda k=k, w=want: reg_ck_problems(k, w))
    suite.check("L", "taylor_lagrange's sources and codes are the spec's",
                lambda: [s for s in X.SOURCES_TAYLOR
                         if s not in (K.S_TAYLOR_ORDER, K.S_TAYLOR_F_C,
                                      K.S_TAYLOR_D_C0, K.S_TAYLOR_D,
                                      K.S_TAYLOR_MONO)])
    for name in ("P3_LOWER", "P3_UPPER"):
        suite.check("L", f"problems/taylor/{name}.json replays to 'Proved.' "
                    "(readiness P3 part 1)", lambda n=name: taylor_file_problems(n))


def unit00_proof_problems(c):
    """VERIFY_PROOFS: every step accepted through the loader's path, then
    the report; a goal verify closed has the goal itself as its theorem
    (E114), one close closed its instance."""
    st, handles = K.install(goal(c["goal"])), {}
    if isinstance(st, K.Refusal):
        return [f"install refused {st.code}: {st.message}"]
    for n, (move, args) in enumerate(c["steps"]):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    out = []
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    last = c["steps"][-1]
    if last[0] == "verify" and st.theorem != goal(c["goal"]):
        out.append(f"theorem {T.show(st.theorem)}, expected the goal")
    if last[0] == "close" and st.theorem != T.instantiate(
            goal(c["goal"]), term(last[1]["value"])):
        out.append(f"theorem {T.show(st.theorem)}, expected the instance")
    return out


def unit00_bad_move_problems(b):
    if b.get("install"):
        return refusal_problems_of(K.install(goal(b["goal"])), b)
    st = K.install(goal(b["goal"]))
    if isinstance(st, K.Refusal):
        return [f"install refused {st.code}: {st.message}"]
    move, args = b["move"]
    r = _parts_feed(st, move, args, {})
    out = refusal_problems_of(r, b)
    want = b.get("residual")
    if want and isinstance(r, K.Refusal):
        if r.residual is None:
            out.append("no residual")
        elif want is not True and not equal_by("ring", r.residual,
                                                term(want))[0]:
            out.append(f"residual {T.show(r.residual)}, expected {want}")
    return out


def unit00_deriv_problems(F, want):
    """UNIT00_DERIV: deriv's output as a tree, and its sides on ()."""
    out_text, sides = want
    d = DV.deriv(term(F), "x", ())
    out = []
    if d.output != term(out_text):
        out.append(f"output {T.show(d.output)}, expected {out_text}")
    got = tuple(k for k, _ in d.emissions)
    exp = tuple(T.parse_judgement(s, SIG) for s in sides)
    if got != exp:
        out.append(f"sides {[T.show(k) for k in got]}, expected {list(sides)}")
    return out


def unit00_checks(suite):
    for name, c in X.VERIFY_PROOFS.items():
        suite.check("U", f"VERIFY_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda c=c: unit00_proof_problems(c))
    for b in X.VERIFY_BAD_MOVES:
        suite.check("U", f"VERIFY_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: unit00_bad_move_problems(b))
    for F, want in X.UNIT00_DERIV.items():
        suite.check("U", f"UNIT00_DERIV D[x] {F} -> {want[0]} (E116)",
                    lambda F=F, w=want: unit00_deriv_problems(F, w))
    suite.check("U", "verify's codes are the spec's, and every one is met",
                lambda: [c for c in X.REFUSAL_CODES_UNIT00 if not any(
                    b["refusal"] == c for b in X.VERIFY_BAD_MOVES)])
    here = os.path.dirname(os.path.abspath(__file__))
    names = sorted(f[:-5] for f in os.listdir(os.path.join(
        here, "problems", "unit00")) if f.endswith(".json"))
    suite.check("U", "problems/unit00/ holds exactly E120's files",
                lambda: [] if names == sorted(X.UNIT00_PROBLEM_FILES)
                else [f"files {names}"])
    for name in X.UNIT00_PROBLEM_FILES:
        suite.check("U", f"problems/unit00/{name}.json replays to 'Proved.' "
                    "and states VERIFY_PROOFS' goal and steps",
                    lambda n=name: unit00_file_problems(n))


def unit00_file_problems(name):
    import json
    here = os.path.dirname(os.path.abspath(__file__))
    raw = json.load(open(os.path.join(here, "problems", "unit00",
                                      name + ".json")))
    c, out = X.VERIFY_PROOFS[name], []
    if raw["goal"] != c["goal"]:
        out.append("goal differs from VERIFY_PROOFS")
    if [(s["move"], s["args"]) for s in raw["reference_proof"]] != \
            [(m, a) for m, a in c["steps"]]:
        out.append("steps differ from VERIFY_PROOFS")
    return out + improper_file_problems(name, folder="unit00")


def g8_accept_problems(lhs, rhs, divisors):
    """G8_FIELD_ACCEPTS: field accepts with exactly these divisors, first
    seen (E131); ring refuses NotEqual (E132)."""
    out = []
    try:
        got = tuple(FD.field(term(lhs), term(rhs)).divisors)
        if got != tuple(term(d) for d in divisors):
            out.append(f"divisors {[T.show(d) for d in got]}, expected "
                       f"{list(divisors)}")
    except FD.NotEqual:
        out.append("field: NotEqual")
    return out


def g8_reject_problems(check, lhs, rhs):
    try:
        getattr(FD, check)(term(lhs), term(rhs))
    except FD.NotEqual:
        return []
    return [f"{check} accepted"]


def g8_checks(suite):
    for lhs, rhs, divs in X.G8_FIELD_ACCEPTS:
        suite.check("G", f"G8_FIELD_ACCEPTS field {lhs} == {rhs}, owing "
                    f"{', '.join(divs)} (E131)",
                    lambda a=(lhs, rhs, divs): g8_accept_problems(*a))
    for check, lhs, rhs in X.G8_REJECTS:
        suite.check("G", f"G8_REJECTS {check} {lhs} == {rhs} -> NotEqual "
                    "(E132, E135)", lambda a=(check, lhs, rhs):
                    g8_reject_problems(*a))
    for name, c in X.G8_PROOFS.items():
        suite.check("G", f"G8_PROOFS {name}: {c['goal']} -> {c['report']!r}",
                    lambda c=c: unit00_proof_problems(c))
    suite.check("G", "G8_ENTRIES pinned as stated (E133)", lambda: [
        n for n, e in X.G8_ENTRIES.items()
        if n not in EN.ENTRIES
        or EN.ENTRIES[n].statement != T.parse_judgement(e["statement"], SIG)
        or tuple(EN.ENTRIES[n].schema) != e["schema"]])


def strict_bad_move_problems(b):
    """STRICT_BAD_MOVES: the steps, then the move refused by code."""
    st, handles = K.install(goal(b["goal"])), {}
    if isinstance(st, K.Refusal):
        return [f"install refused {st.code}: {st.message}"]
    for move, args in b.get("steps", ()):
        st = _parts_feed(st, move, args, handles)
        if isinstance(st, K.Refusal):
            return [f"step {move} refused {st.code}: {st.message}"]
    move, args = b["move"]
    r = _parts_feed(st, move, args, handles)
    if not isinstance(r, K.Refusal):
        return ["accepted"]
    return [] if r.code == b["refusal"] else [f"refused {r.code}: {r.message}"]


def strict_checks(suite):
    for name, c in X.STRICT_PROOFS.items():
        suite.check("K", f"STRICT_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda c=c: unit00_proof_problems(c))
    for b in X.STRICT_BAD_MOVES:
        suite.check("K", f"STRICT_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: strict_bad_move_problems(b))
    suite.check("K", "taylor_lagrange's senses and bound's source are the "
                "spec's (E138, E139)", lambda: [] if (
                    set(K.TAYLOR_SENSES) == {"increasing", "decreasing",
                                             "strictly increasing",
                                             "strictly decreasing"}
                    and K.S_BOUND_SCALE in X.SOURCES_STRICT) else ["differ"])


def _clear_cert(key, spec):
    """A CLEAR_* certificate: the terms parsed, both children searched
    (a child the search cannot find is the norm_num leaf, which the
    checker then rejects)."""
    import discharge as DC
    import search as SR
    d, n, dr = term(spec["den"]), term(spec["num"]), spec["den_rel"]
    nonzero = isinstance(key, T.NonZero)
    if nonzero:
        strict = True
    else:
        strict = key.op in ("<", ">")
    nr = DC._clear_relation(dr, nonzero, strict)
    leaf = {"method": "norm_num"}
    dc = SR.propose(T.with_domain(T.Rel(dr, d, T.Num(0)), key.dom)) or leaf
    prop = T.NonZero(n) if nr == "# 0" else T.Rel(nr, n, T.Num(0))
    nc = SR.propose(T.with_domain(prop, key.dom)) or leaf
    return {"method": "clear", "den": d, "den_rel": dr, "den_cert": dc,
            "num": n, "num_cert": nc}


def clear_accept_problems(key_text, spec):
    import discharge as DC
    key = T.parse_judgement(key_text, SIG)
    tag, why = DC.verdict(key, _clear_cert(key, spec))
    out = [] if tag and tag[0] == "clear" else [f"rejected: {why}"]
    import search as SR
    if SR.propose(key) is None:
        out.append("the search proposes nothing")
    return out


def clear_reject_problems(key_text, spec, reason):
    import discharge as DC
    key = T.parse_judgement(key_text, SIG)
    tag, why = DC.verdict(key, _clear_cert(key, spec))
    if tag is not None:
        return ["accepted"]
    return [] if why.startswith(reason) else [f"rejected {why}, "
                                               f"expected {reason}"]


def clear_planted_problems(name, bug):
    """E145: with the seam mutated, some caught_by case is accepted."""
    import discharge as DC
    real = getattr(DC, bug["seam"])  # patched by hand: the parent never
    # imports unittest.mock (item 3's clean-afterwards check)
    if bug["seam"] == "_clear_relation":
        bad = lambda dr, nonzero, strict: real(">", nonzero, strict)  # noqa
    else:
        bad = lambda *a: True  # noqa: E731
    cases = {c[0]: c for c in X.CLEAR_MUST_REJECT}
    caught = []
    setattr(DC, bug["seam"], bad)
    try:
        for cid in bug["caught_by"]:
            _, key_text, spec, _ = cases[cid]
            key = T.parse_judgement(key_text, SIG)
            if DC.verdict(key, _clear_cert(key, spec))[0] is not None:
                caught.append(cid)
    finally:
        setattr(DC, bug["seam"], real)
    if getattr(DC, bug["seam"]) is not real:
        return ["the seam was not restored"]
    return [] if caught else [f"{name} went unnoticed"]


def clear_review_problems(key_text, method):
    import discharge as DC
    import search as SR
    key = T.parse_judgement(key_text, SIG)
    try:
        cert = SR.propose(key)
    except RecursionError:
        return ["RecursionError"]
    if cert is None or cert.get("method") != method:
        return [f"proposed {cert and cert.get('method')}"]
    tag = DC.check(key, cert)
    return [] if tag else ["rejected"]


def clear_checks(suite):
    for cid, key, spec in X.CLEAR_ACCEPTS:
        suite.check("Q", f"CLEAR_ACCEPTS {cid}: {key} (E142)",
                    lambda k=key, s=spec: clear_accept_problems(k, s))
    for cid, key, spec, why in X.CLEAR_MUST_REJECT:
        suite.check("Q", f"CLEAR_MUST_REJECT {cid} -> {why}",
                    lambda k=key, s=spec, w=why: clear_reject_problems(k, s, w))
    for name, bug in X.CLEAR_PLANTED_BUGS.items():
        suite.check("Q", f"CLEAR_PLANTED_BUGS {name} ({bug['seam']}) is "
                    "caught (E145)", lambda n=name, b=bug:
                    clear_planted_problems(n, b))
    for name, c in X.CLEAR_PROOFS.items():
        suite.check("Q", f"CLEAR_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda c=c: unit00_proof_problems(c))
    for k, method in X.CLEAR_REVIEW_KEYS:
        suite.check("Q", f"CLEAR_REVIEW_KEYS {k}: the search's {method} "
                    "certificate is accepted (E158)",
                    lambda k=k, m=method: clear_review_problems(k, m))


def _ode_gamma(data, sig):
    """ODE Γ data through the loader's own path (E155)."""
    import loader
    items = []
    for name, var, iv, j in data:
        d = {"name": name, "var": var, "in": iv}
        if j[0] == "law":
            d["law"] = j[1]
        else:
            d["reg"] = {"fn": j[1], "class": j[2]}
        items.append(d)
    return loader.assumptions(items, sig)


def _ode_install(c):
    return K.install(T.parse_goal(c["goal"], c["sig"]),
                     _ode_gamma(c["gamma"], c["sig"]))


def _ode_feed(st, move, args, handles, sig):
    import loader
    return loader.feed(st, {"move": move, "args": args}, handles, sig)


def ode_proof_problems(c):
    """ODE_PROOFS: install under Γ, every step accepted, the report, the
    theorem the goal itself (verify), Γ kept for the lineage (E147)."""
    st, handles = _ode_install(c), {}
    if isinstance(st, K.Refusal):
        return [f"install refused {st.code}: {st.message}"]
    gamma = _ode_gamma(c["gamma"], c["sig"])
    for n, (move, args) in enumerate(c["steps"]):
        st = _ode_feed(st, move, args, handles, c["sig"])
        if isinstance(st, K.Refusal):
            return [f"step {n} ({move}) refused {st.code}: {st.message}"]
    out = []
    if K.report(st) != c["report"]:
        out.append(f"report {K.report(st)!r}, expected {c['report']!r}")
    if st.theorem != T.parse_goal(c["goal"], c["sig"]):
        out.append(f"theorem {T.show(st.theorem)}, expected the goal")
    if K.assumptions(st) != gamma:
        out.append("assumptions(state) is not the installed Γ")
    return out


def ode_bad_move_problems(b):
    st = _ode_install(b)
    if isinstance(st, K.Refusal):
        return [f"install refused {st.code}: {st.message}"]
    r = _ode_feed(st, *b["move"], {}, b["sig"])
    if not isinstance(r, K.Refusal):
        return ["accepted"]
    return [] if r.code == b["refusal"] else [f"refused {r.code}: {r.message}"]


def ode_install_problems(gamma, sig, goal_text, want):
    r = K.install(T.parse_goal(goal_text, sig), _ode_gamma(gamma, sig))
    if not isinstance(r, K.Refusal):
        return ["installed"]
    return [] if r.code == want else [f"refused {r.code}: {r.message}"]


def ode_emission_problems():
    """E150, E152, E156: P1A_SEP's step emits containment, range and the
    law's divisor under their sources, and its handle's conclusion is
    E152's, at G."""
    c = X.ODE_PROOFS["P1A_SEP"]
    st = _ode_install(c)
    move, args = c["steps"][0]
    handles = {}
    st = _ode_feed(st, move, args, handles, c["sig"])
    if isinstance(st, K.Refusal):
        return [f"refused {st.code}"]
    srcs = set().union(*(ob.sources for ob in st.last.emitted))
    out = [f"no {s} emission" for s in (K.S_ODE_CONTAIN, K.S_ODE_RANGE,
                                         K.S_ODE_LAW, K.S_ODE_D)
           if s not in srcs]
    G = T.parse_goal(c["goal"], c["sig"])[0].dom
    want = T.with_domain(T.parse_judgement(
        "t == 0 + (-(m/b)*ln(m*g/b + v(t)) - -(m/b)*ln(m*g/b + v(0)))",
        c["sig"]), G)
    got = st.conclusion(handles["h"])
    if not equal_by("ring", T.Add(got.lhs, T.Neg(got.rhs)),
                    T.Add(want.lhs, T.Neg(want.rhs)))[0] or got.dom != G:
        out.append(f"conclusion {T.show(got)}")
    range_keys = [ob for ob in st.last.emitted
                  if K.S_ODE_RANGE in ob.sources]
    if not all(any(isinstance(i, T.Interval) and i.var == "s"
                   for i in ob.key.dom) for ob in range_keys):
        out.append("a range key is not at s in [t0, t1]")
    return out


def ode_forged_range_problems():
    """E159 (1): object.__new__ ranges with infinities misplaced or junk
    ends are refused bad-args, never read."""
    import loader
    c = X.ODE_PROOFS["P1A_SEP"]
    out = []
    for lo, hi in ((T.POS_INF, T.POS_INF), (T.NEG_INF, T.NEG_INF),
                   (T.POS_INF, T.NEG_INF), (None, T.POS_INF),
                   ("junk", T.POS_INF)):
        st = _ode_install(c)
        args = loader.step_args(c["steps"][0][1], {}, c["sig"])
        r = object.__new__(T.Interval)
        for k, v in (("var", "w"), ("lo", lo), ("lo_closed", False),
                     ("hi", hi), ("hi_closed", False)):
            object.__setattr__(r, k, v)
        args["range"] = r
        got = K.step(st, "sep_autonomous", args)
        if not (isinstance(got, K.Refusal) and got.code == "bad-args"):
            out.append(f"({lo!r}, {hi!r}): {getattr(got, 'code', 'accepted')}")
    return out


def ode_checks(suite):
    for name, c in X.ODE_PROOFS.items():
        suite.check("O", f"ODE_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda c=c: ode_proof_problems(c))
    for b in X.ODE_BAD_MOVES:
        suite.check("O", f"ODE_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: ode_bad_move_problems(b))
    for b in X.ODE_REVIEW_BAD_MOVES:
        suite.check("O", f"ODE_REVIEW_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: ode_bad_move_problems(b))
    suite.check("O", "a hand-built range w in (oo, oo) is refused bad-args "
                "(E159)", ode_forged_range_problems)
    for rid, gamma, sig, g, want in X.ODE_INSTALL_REFUSALS:
        suite.check("O", f"ODE_INSTALL_REFUSALS {rid} -> {want} (E148)",
                    lambda a=(gamma, sig, g, want): ode_install_problems(*a))
    suite.check("O", "P1A_SEP's emissions and handle (E150, E152, E156)",
                ode_emission_problems)
    suite.check("O", "the ODE moves and their args are the spec's (E149)",
                lambda: [] if (K._ODE_MOVES == X.ODE_MOVES and all(
                    set(K._ARGS[m]) == set(X.ODE_ARGS[m])
                    for m in X.ODE_MOVES)) else ["differ"])
    suite.check("O", "a goal installed without Γ has none (E147)",
                lambda: [] if K.assumptions(K.install(goal("x == x"))) == ()
                else ["Γ not empty"])
    suite.check("O", "a closed key holding a Call keeps its domain (E157)",
                lambda: [] if T.with_domain(
                    T.parse_judgement("v(0) >= 0", {"v": 1}),
                    (T.parse_judgement("v(0) >= 0", {"v": 1}),)).dom
                else ["dropped"])


def _trig_forgery(kind):
    """A replacement for trig_norm.propose, per TRIG_NORM_FORGERIES."""
    import trig_norm as TN
    real = TN.propose
    x = T.Var("x")

    def forged(lhs, rhs, facts=()):
        good = real(lhs, rhs, facts)
        if kind == "raises":
            raise ZeroDivisionError("planted")
        if kind == "not_list":
            return tuple(good)
        if kind == "empty":
            return []
        if kind == "too_many":
            return [good[0]] * 65
        if kind == "unknown_entry":
            return [("sin_triple", {"u": x})] + good
        if kind == "not_equation":
            return [("pi_pos", {})] + good
        if kind == "wrong_schema":
            return [("sin_add", {"u": x})] + good
        bad = {"mvar_inst": T.MVar("A"), "oo_inst": T.POS_INF,
               "int_inst": term("Int[t = 0 .. 1] t"), "foreign_var": T.Var("q"),
               "non_term": "x"}
        if kind in bad:
            return [("pyth_cos", {"u": bad[kind]})] + good[:-1]
        if kind == "false_pair":
            return good[:-1]  # without pyth_cos
        raise AssertionError(kind)
    return forged


def trig_forgery_problems(kind):
    """E88's fence: trig_wrong_F's own refusal whatever propose returns, and
    on the genuine move (TRIG_COS_SQ's ftc) the same fence refuses too, so
    a forged proposal never lends its instances to a true check."""
    import trig_norm as TN
    real = TN.propose
    TN.propose = _trig_forgery(kind)
    try:
        b = next(b for b in X.TRIG_NORM_BAD_MOVES if b["id"] == "trig_wrong_F")
        try:
            out = trig_bad_move_problems(b)
        except Exception as e:  # E21: nothing may raise out of step()
            return [f"raised {type(e).__name__}: {e}"]
        c = X.TRIG_NORM_PROOFS["TRIG_COS_SQ"]
        try:
            r, n = _trig_run(c["goal"], c["steps"][:1])
        except Exception as e:
            return out + [f"the genuine move raised {type(e).__name__}"]
        if n is None and kind != "not_list" and kind != "too_many":
            out.append("the genuine ftc was accepted on a forged proposal")
        return out
    finally:
        TN.propose = real


def field_order_problems(facts, lhs, rhs, want):
    import field as FD
    fs = [(term(a), term(b)) for a, b in facts]
    try:
        FD.field(term(lhs), term(rhs), fs)
        got = "equal"
    except FD.NotEqual:
        got = "not-equal"
    except T.Refused as r:
        got = r.code
    return [] if got == want else [f"got {got}"]


def e27_trig_problems(value, want):
    import schema as SC
    got = SC.evaluated_offence(term(value))
    name = got[2] if got is not None and got[0] == "a" else None
    return [] if name == want else [f"offence {got}, expected entry {want}"]


def qc1_w1_accepted_problems():
    """TRIG_NORM_SWITCH: QC1-W1's move accepted, pyth_cos among the ftc_D
    cites (supplied by trig_norm, E88)."""
    B = book(kind="consolidation")
    w = next(w for w in S0.CONSOLIDATION_WRONG_ANSWERS if w["id"] == "QC1-W1")
    problem, name = s0_file(w["state"][0], B)
    results, handles = LD.replay(problem, name, through=w["state"][1])
    st = results[-1][1]
    move, args = w["move"]
    r = LD.feed(st, {"move": move, "args": args}, handles, problem.sig)
    if not isinstance(r, K.ProofState):
        return [f"refused: {describe(r)}"]
    tags = [o.tag for o in r.obligations() if "ftc_D" in o.sources]
    return [] if tags and "pyth_cos" in tags[0][1] else [f"ftc_D tags {tags}"]


def trig_review_problems(c):
    """E94 and E95: the original refusal, nothing raised, and within the
    case's seconds where it gives them."""
    import time
    t0 = time.monotonic()
    try:
        out = trig_bad_move_problems(c)
    except Exception as e:  # E21
        return [f"raised {type(e).__name__}"]
    took = time.monotonic() - t0
    if "seconds" in c and took > c["seconds"]:
        out.append(f"took {took:.1f} s, over {c['seconds']} s")
    return out


def trig_checks(suite):
    for name, c in X.TRIG_NORM_PROOFS.items():
        suite.check("T", f"TRIG_NORM_PROOFS {name}: {c['goal']} -> "
                    f"{c['report']!r}", lambda n=name: trig_proof_problems(n))
    for b in X.TRIG_NORM_BAD_MOVES:
        suite.check("T", f"TRIG_NORM_BAD_MOVES {b['id']} -> {b['refusal']}, "
                    "field's own residual", lambda b=b: trig_bad_move_problems(b))
    for kind, what in X.TRIG_NORM_FORGERIES:
        suite.check("T", f"TRIG_NORM_FORGERIES {kind} ({what}): the original "
                    "refusal, nothing raised", lambda k=kind: trig_forgery_problems(k))
    for facts, lhs, rhs, want in X.FIELD_ORDER_CASES:
        suite.check("T", f"FIELD_ORDER_CASES (E86) {lhs} == {rhs} with "
                    f"{len(facts)} facts -> {want}",
                    lambda f=facts, a=lhs, b=rhs, w=want: field_order_problems(f, a, b, w))
    for value, want in X.E27_TRIG_CASES:
        suite.check("T", f"E27_TRIG_CASES (E89) {value}: counts {want}",
                    lambda v=value, w=want: e27_trig_problems(v, w))
    suite.check("T", "TRIG_NORM_ENTRIES pinned in entries.py (E87)",
                lambda: [n for n, e in X.TRIG_NORM_ENTRIES.items()
                         if EN.ENTRIES.get(n) is None
                         or EN.ENTRIES[n].statement != T.parse_judgement(e["statement"], SIG)
                         or tuple(EN.ENTRIES[n].schema) != e["schema"]])
    for c in X.TRIG_NORM_REVIEW_CASES:
        suite.check("T", f"TRIG_NORM_REVIEW_CASES {c['id']} -> {c['refusal']}"
                    f" ({c['why']})", lambda c=c: trig_review_problems(c))
    suite.check("T", "problems/trig/COS_SQ.json replays to 'Proved.'",
                lambda: improper_file_problems("COS_SQ", "trig"))
    if S0 is not None:
        suite.check("T", "TRIG_NORM_SWITCH: QC1-W1's ftc without pyth_cos is "
                    "accepted, pyth_cos cited", qc1_w1_accepted_problems)


def e57_principle_problems():
    """E57_PRINCIPLE checks every move: each of MOVES is named there."""
    return [f"{m} is not checked against E57's principle" for m in K.MOVES
            if m not in X.E57_PRINCIPLE]


def e27_pyth_problems():
    """ATOM_FACT_RULE's E27 (a): pyth counts at a subterm tree-equal to
    (sin b)^2 + (cos b)^2, which is 1 unevaluated; pyth_cos never counts, so
    a value holding (cos b)^2 is not refused for it; and neither is an
    exact value (each has a schema variable)."""
    out = []
    got = SC.evaluated_offence(term("2 + ((sin 1)^2 + (cos 1)^2)"))
    if got is None or (got[0], got[1], got[2]) != ("a", term("(sin 1)^2 + (cos 1)^2"),
                                                    "pyth"):
        out.append(f"(sin 1)^2 + (cos 1)^2: {got}, expected clause a at it, pyth")
    got = SC.evaluated_offence(term("(cos 1)^2"))
    if got is not None:
        out.append(f"(cos 1)^2: {got}, expected no offence (pyth_cos never counts)")
    exact = {n for n, e in EN.ENTRIES.items() if not e.schema and not e.hyps}
    out += [f"{n} is an exact value" for n in X.CONSOLIDATION_ENTRIES if n in exact]
    return out


def consolidation_entries_problems():
    """CONSOLIDATION_ENTRIES pinned in entries.py as stated, appended after
    sqrt_nonneg in their order (E54): statement, schema and hypotheses."""
    out, names = [], list(EN.ENTRIES)
    # IMPROPER_E27_CHANGES appends atan_zero after them (E80)
    want = list(X.CONSOLIDATION_ENTRIES) + list(
        X.IMPROPER_E27_CHANGES["ENTRIES_append"]) + list(
        X.TRIG_NORM_SWITCH["ENTRIES_append"]) + list(  # and trig_norm's (E87)
        X.TAYLOR_ENTRIES_APPEND) + list(  # and exp_pos (E103)
        X.UNIT00_ENTRIES_APPEND) + list(  # and unit 00's seven (E117)
        X.G8_ENTRIES_APPEND)  # and G8's three (E133)
    if "sqrt_nonneg" not in names or \
            names[names.index("sqrt_nonneg") + 1:] != want:
        out.append(f"not appended after sqrt_nonneg in order: {names}")
    for name, e in X.CONSOLIDATION_ENTRIES.items():
        got = EN.ENTRIES.get(name)
        if got is None:
            out.append(f"{name} is not in ENTRIES")
            continue
        if got.statement != T.parse_judgement(e["statement"], SIG) \
                or tuple(got.schema) != e["schema"] \
                or tuple(got.hyps) != tuple(T.parse_judgement(h, SIG) for h in e["hyps"]):
            out.append(f"{name}: {T.show(got.statement)} {got.schema}")
    return out


def consolidation_checks(suite):
    """Item C's rows."""
    suite.check("C", "CONSOLIDATION_ENTRIES are pinned after sqrt_nonneg, in order "
                "(E54)", consolidation_entries_problems)
    suite.check("C", "E27 (a) counts pyth at (sin b)^2 + (cos b)^2 and never "
                "pyth_cos; none of the six is an exact value", e27_pyth_problems)
    suite.check("C", f"int_flip is a move: MOVES is {len(K.MOVES)} long and names it",
                lambda: [] if K.MOVES[5] == X.INT_FLIP_MOVE and K.MOVES[6:] ==
                (X.INT_PARTS_MOVE, X.INT_IMPROPER_MOVE,  # sections 19, 20
                 X.TAYLOR_MOVE, X.BOUND_MOVE,  # section 25
                 X.VERIFY_MOVE,  # section 26
                 *X.ODE_MOVES)  # section 30
                else [f"MOVES is {K.MOVES}"])
    print("\nint_flip (E51): accepted moves")
    for c in FLIP_ACCEPTS:
        suite.check("C", f"INT_FLIP_ACCEPTS {c['id']}"
                    + (f" -> {c['report']!r}" if "report" in c else ""),
                    lambda c=c: subst_accept_problems(c, table="INT_FLIP_ACCEPTS"))
    print("\nint_flip (E51): refused moves")
    for b in FLIP_BAD_MOVES:
        suite.check("C", f"INT_FLIP_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    print("\nE56: reversed ranges everywhere")
    for c in E56_ACCEPTS:
        suite.check("C", f"E56_ACCEPTS {c['id']}"
                    + (f" -> {c['report']!r}" if "report" in c else ""),
                    lambda c=c: subst_accept_problems(c, table="E56_ACCEPTS"))
    for b in E56_BAD_MOVES:
        suite.check("C", f"E56_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    print("\nThe consolidation review (section 15): E57 and E56's amendments")
    suite.check("C", "E57_PRINCIPLE checks every move", e57_principle_problems)
    for b in E57_BAD_MOVES:
        suite.check("C", f"E57_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for c in E57_ACCEPTS:
        suite.check("C", f"E57_ACCEPTS {c['id']} -> {c['report']!r}",
                    lambda c=c: subst_accept_problems(c, table="E57_ACCEPTS"))
    for b in REVIEW_BAD:
        suite.check("C", f"E56_REVIEW_CASES {b['id']} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for c in REVIEW_ACCEPTS:
        suite.check("C", f"E56_REVIEW_CASES {c['id']}",
                    lambda c=c: subst_accept_problems(c, table="E56_REVIEW_CASES"))
    for c in REVIEW_LAZY:
        suite.check("C", f"E56_REVIEW_CASES {c['id']}: {c['goal']} installs emitting "
                    f"nothing, within {c['timing_bound']} s (E56_TIMING_BOUND)",
                    lambda c=c: lazy_install_problems(c))
    suite.check("C", "E57's step 2a, called directly: a tree in inst only, and in the "
                "target only, is each refused (both kinds of left side)",
                e57_halves_problems)
    suite.check("C", "the orientation memo keeps no answer a RecursionError decided",
                order_memo_depth_problems)
    print("\nThe second review (section 16): limits holding a tree, and 0^0 = 1")
    for b in SECOND_BAD_MOVES:
        suite.check("C", f"SECOND_REVIEW_BAD_MOVES {b['id']} -> {b['refusal']}",
                    lambda b=b: second_review_bad_move_problems(b))
    for c in E58_ACCEPTS:
        suite.check("C", f"E58_ACCEPTS {c['id']}: {c['goal']} closes with 1 -> "
                    f"{c['report']!r}",
                    lambda c=c: subst_accept_problems(c, table="E58_ACCEPTS"))


# CONSOLIDATION_PLANTED_BUGS and E56_PLANTED_BUGS, each in a child process
# (`--consolidation NAME`) through the seams of ARCHITECTURE.md §7: int_flip's
# rule functions, discharge's _relation_ok and _atom_fact, and kernel's
# _range_of. The child runs what their caught_by names: the int_flip and E56
# cases, BAD_MOVES' DISCHARGE_BAD_MOVES_CHANGED cases, the must-reject
# cases beyond DISCHARGE_MUST_REJECT (their verdicts), and the property
# test's families a bug's caught_by names.

CONSOLIDATION_BUGS = {n: _reg_retrace(n, b, "CONSOLIDATION") for n, b in {
    **X.CONSOLIDATION_PLANTED_BUGS, **X.E56_PLANTED_BUGS,
    **X.REVIEW2_PLANTED_BUGS}.items()}


def consolidation_seam_patch(name, mock):
    """The child's patch for one CONSOLIDATION_BUGS key: the mutation's own
    text, through the function that holds the rule."""
    import discharge as DC
    atom_fact, range_of, no_trees = DC._atom_fact, K._range_of, K._no_trees_erased

    def symbolic(lo, hi):
        """Neither end infinite, and not two rational literals: the ends E56
        orders by discharge."""
        return (all(isinstance(e, T.Term) for e in (lo, hi))
                and (FD.rational_value(lo) is None or FD.rational_value(hi) is None))

    def undecided(lo, hi):
        return T.Refused(K.ORIENTATION_UNDECIDED, f"the order of {T.show(lo)} and "
                         f"{T.show(hi)} is not decided; state it in the goal's domain")

    def one_order(v, lo, hi, dom):  # lo <= hi only (E4's old reading)
        if not symbolic(lo, hi):
            return range_of(v, lo, hi, dom)
        k = T.with_domain(T.Rel("<=", lo, hi), dom)
        if K._settles(k):
            return T.Interval(v, lo, True, hi, True), k
        raise undecided(lo, hi)

    def order_unproved(v, lo, hi, dom):  # [hi, lo] whenever lo <= hi is not proved
        if not symbolic(lo, hi):
            return range_of(v, lo, hi, dom)
        k = T.with_domain(T.Rel("<=", lo, hi), dom)
        if K._settles(k):
            return T.Interval(v, lo, True, hi, True), k
        return T.Interval(v, hi, True, lo, True), T.with_domain(T.Rel("<=", hi, lo), dom)

    def fact_strict(key, label):
        c = atom_fact(key, label)
        return None if c is None else (c[0], c[1], True)

    def any_entry(key, label):  # any ENTRIES ordering with a schema variable
        if not (type(label) is tuple and len(label) == 3 and label[1] in EN.ENTRIES):
            return None
        if label[1] in DC.ATOM_FACTS:
            return atom_fact(key, label)
        e = EN.ENTRIES[label[1]]
        st = e.statement
        if not (type(st) is T.Rel and st.op in DC.ORDERINGS and len(e.schema) == 1):
            return None
        (x, y), strict = DC._reading(DC._prop(T.subst(st, {e.schema[0]: label[2]})))
        return (x, y, strict)

    patches = {
        "int_flip_drops_negation": (K, "_flipped", lambda it: T.Integral(
            it.var, it.hi, it.lo, it.body)),
        "int_flip_under_D_unchecked": (K, "_flip_under_D", lambda anc, it: None),
        "product_nonstrict_factor_on_strict": (DC, "_relation_ok", lambda r, nonzero, strict: (
            r == "# 0" if nonzero else r in DC.ORDERINGS)),
        "cos_fact_strict": (DC, "_atom_fact", fact_strict),
        "atom_fact_any_entry": (DC, "_atom_fact", any_entry),
        "orientation_tries_one_order": (K, "_range_of", one_order),
        "orientation_order_unproved": (K, "_range_of", order_unproved),
        # REVIEW2_PLANTED_BUGS
        "rewrite_tree_branch_skips_E57": (K, "_no_trees_erased", lambda lhs, inst, at: (
            no_trees(lhs, inst, at) if isinstance(lhs, T.App) else None)),
        "enclosing_range_undecided": (K, "_decided", lambda buf, dom, anc, goal_dom: dom),
    }
    if name not in patches:
        raise KeyError(f"no seam for consolidation planted bug {name!r}")
    module, attr, new = patches[name]
    assert callable(getattr(module, attr, None)), f"seam {module.__name__}.{attr} is missing"
    return mock.patch.object(module, attr, new)


def consolidation_child(name):
    """`--consolidation NAME`: under one CONSOLIDATION_BUGS patch (None: the
    control), print {"mismatches": [...]}, each failing case as [table, id].
    A crash exits 2."""
    if K is None or TD is None:
        print(KERNEL_ERROR or DISCHARGE_ERROR, file=sys.stderr)
        return 2
    try:
        if name is None:
            ctx = contextlib.nullcontext()
        else:
            from unittest import mock
            ctx = consolidation_seam_patch(name, mock)
        bug = CONSOLIDATION_BUGS.get(name, {})
        found = []
        changed = [b for b in BAD_MOVES if b["id"] in X.DISCHARGE_BAD_MOVES_CHANGED]
        with ctx:
            for table, cases, fn in (
                    ("INT_FLIP_ACCEPTS", FLIP_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="INT_FLIP_ACCEPTS")),
                    ("INT_FLIP_BAD_MOVES", FLIP_BAD_MOVES, bad_move_problems),
                    ("E56_ACCEPTS", E56_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="E56_ACCEPTS")),
                    ("E56_BAD_MOVES", E56_BAD_MOVES, bad_move_problems),
                    ("DISCHARGE_BAD_MOVES_CHANGED", changed, bad_move_problems),
                    ("E57_BAD_MOVES", E57_BAD_MOVES, bad_move_problems),
                    ("E57_ACCEPTS", E57_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="E57_ACCEPTS")),
                    ("E56_REVIEW_CASES", REVIEW_BAD, bad_move_problems),
                    ("E56_REVIEW_CASES", REVIEW_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="E56_REVIEW_CASES"))):
                for c in cases:
                    try:
                        problems = fn(c)
                    except Mismatch as m:
                        problems = [str(m)]
                    if problems:
                        found.append([table, c["id"]])
            found += TD.more_must_reject_verdicts()
            families = [c[1] for c in bug.get("caught_by", ()) if c[0] == "PROPERTY"]
            if families:
                results = TD.property_results(families=families)
                found += [["PROPERTY", n] for n, st in results.items() if st.violations]
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found}))
    return 0


def consolidation_child_results():
    """The control and every CONSOLIDATION_BUGS child, a few at a time."""
    from concurrent.futures import ThreadPoolExecutor
    names = [None, *CONSOLIDATION_BUGS]
    with ThreadPoolExecutor(max_workers=max(2, min(8, os.cpu_count() or 2))) as ex:
        futures = {n: ex.submit(spawn, *(("--consolidation-control",) if n is None else
                                         ("--consolidation", n))) for n in names}
    return {n: f.result() for n, f in futures.items()}


def consolidation_planted_problems(name, result):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    if name is None:
        return out + [f"unpatched child found {m}" for m in sorted(found, key=str)]
    return out + [f"not caught at {c}" for c in map(tuplify, CONSOLIDATION_BUGS[name]["caught_by"])
                  if c not in found]


# ---------------------------------------------------------------- regularity planted bugs
#
# REG_PLANTED_BUGS, each in a child process (`--reg NAME`, the control
# `--reg-control`) through the seams of ARCHITECTURE.md §7: one function per
# REG_CHECK_RULE paragraph in discharge.py, the search's _reg_sides, E63's
# refute_reg, and the kernel's former functions. The child runs what their
# caught_by names: every proof in PROOFS (N and the step lists), the
# regularity checker's must-reject verdicts and decided-false keys,
# section 17's cases, E56_REVIEW_CASES, E57_BAD_MOVES, the switched
# BAD_MOVES and their accepted twins, and the property families named; and,
# for a bug whose data 'expect's it, whether REG_BAD_MOVES' cases are still
# refused with their 'as_well' messages.

REG_BUGS = {**X.REG_PLANTED_BUGS, **X.REG_REVIEW_PLANTED_BUGS} if REGULARITY else {}
# the REG_BAD_MOVES cases each 'expect' says are refused as_well
REG_AS_WELL = {"former_div_dropped": ("ftc_across_pole", "ftc_f_not_C0_at_an_end"),
               "ftc_no_F_formers": ("ftc_F_across_pole",)}


def reg_seam_patch(name, mock):
    """The child's patch for one REG_PLANTED_BUGS key: the mutation's own
    text, through the function that holds the rule."""
    import discharge as DC
    import domains as DM
    import refute as RF
    import search as SR
    rule, sides, holds_side = DC._reg_rule, DC._reg_sides, DC._reg_side_holds

    def charged_first(buf, term_, dom, goal_dom, anc=()):
        walk = list(K._positions(term_, dom, anc))
        K._tree_formers(buf, walk, goal_dom)
        K._e6_formers(buf, walk, goal_dom)

    def no_div(buf, walk, goal_dom):
        for _, s_, d, a in walk:
            if isinstance(s_, T.Div):
                continue
            for prop, divisor in K._owed(s_):
                K._emit_at(buf, prop, d, a, "former", goal_dom, divisor)

    def old_e57(lhs, inst, at):
        for t in (*inst.values(), at):
            if next(T.trees(t), None) is not None:
                raise T.Refused("Int-or-D-not-normalisable", "E57 as it stood")

    def all_atoms(self, t):
        return self.atom(("tree", t), t)

    c1 = mock.patch.object(DM, "C1_EXTRA", types.MappingProxyType({}))
    patches = {
        "reg_side_not_decided": [(DC, "_reg_side_holds", lambda prop, cert, dom: ())],
        # the skeptic's M3: each side decided on D + (prop,), assuming itself
        "reg_side_assumes_itself": [(DC, "_reg_side_holds", lambda prop, cert, dom:
                                     holds_side(prop, cert, tuple(dom) + (prop,)))],
        "reg_side_count_unchecked": [(DC, "_reg_side_count_ok", lambda g, r: True)],
        "reg_side_from_certificate": [(DC, "_reg_side_prop", lambda rebuilt, given: given)],
        "reg_rule_from_certificate": [(DC, "_reg_rule", lambda t, node: node["rule"])],
        "reg_children_not_walked": [(DC, "_reg_children", lambda *a: None)],
        "reg_c1_uses_c0_sides": [(DC, "_interior", lambda props: props), c1],
        "reg_no_c1_extra": [c1],
        "reg_div_no_side": [(DC, "_reg_sides", lambda t, r, k: () if r == "div"
                             else sides(t, r, k))],
        "reg_negative_power_as_power": [(DC, "_reg_rule", lambda t, node: "pow"
                                         if type(t) is T.Pow else rule(t, node))],
        "reg_rpow_no_side": [(DC, "_reg_sides", lambda t, r, k: () if r == "rpow"
                              else sides(t, r, k))],
        "reg_any_class": [(DC, "_reg_class_ok", lambda k: True)],
        "reg_tree_as_const": [(DC, "_reg_rule", lambda t, node: "const"
                               if type(t) in (T.Integral, T.Deriv) else rule(t, node))],
        "reg_extra_fields_ignored": [(DC, "_reg_fields", lambda x, names: hasattr(
            x, "keys") and set(names) <= set(x))],
        "reg_search_drops_side": [(SR, "_reg_sides", lambda s_: s_[:-1])],
        "reg_refute_off": [(RF, "refute_reg", lambda key_, owed: None)],
        "int_former_not_charged": [(K, "_int_former", lambda *a: None)],
        "d_former_not_charged": [(K, "_d_former", lambda *a: None)],
        "d_former_at_goal_domain": [(K, "_d_former", lambda buf, dx, dom, anc, goal_dom:
                                     K._emit_at(buf, T.Reg(dx.body, 1), goal_dom, (),
                                                "former", goal_dom))],
        "int_former_charged_first": [(K, "_charge_formers", charged_first)],
        "former_div_dropped": [(K, "_e6_formers", no_div)],
        "ftc_no_F_formers": [(K, "_ftc_F_formers", lambda buf, F, on_ab, G: None)],
        "e57_refuses_nothing": [(K, "_no_trees_erased", lambda lhs, inst, at: None)],
        "e57_refuses_statable": [(K, "_no_trees_erased", old_e57)],
        "improper_Int_as_atom": [(FD._Normaliser, "tree", all_atoms)],
    }
    if name not in patches:
        raise KeyError(f"no seam for regularity planted bug {name!r}")
    stack = contextlib.ExitStack()
    for p in patches[name]:
        if isinstance(p, tuple):
            module, attr, new = p
            assert callable(getattr(module, attr, None)), f"seam {attr} is missing"
            stack.enter_context(mock.patch.object(module, attr, new))
        else:
            stack.enter_context(p)
    return stack


def reg_child(name):
    """`--reg NAME`: under one REG_PLANTED_BUGS patch (None: the control),
    print {"mismatches": [...], "admissions": {proof: N}, "as_well":
    {id: problems}}. A crash exits 2."""
    if K is None or TD is None:
        print(KERNEL_ERROR or DISCHARGE_ERROR, file=sys.stderr)
        return 2
    try:
        if name is None:
            ctx = contextlib.nullcontext()
        else:
            from unittest import mock
            ctx = reg_seam_patch(name, mock)
        bug = REG_BUGS.get(name, {})
        found, admissions, as_well = [], {}, {}
        with ctx:
            for p in PROOFS:
                run = run_proof(p, strict=False, out=lambda line: None)
                found += [list(where) for _, where, _ in run.found]
                admissions[p] = run.n
            found += TD.reg_must_reject_verdicts()
            found += [["REG_DECIDED_FALSE", c["id"]] for c in X.REG_DECIDED_FALSE
                      if TD.reg_decided_false_problems(c)]
            for table, cases, fn in (
                    ("REG_Q23_CASES", REG_Q23,
                     lambda c: subst_accept_problems(c, table="REG_Q23_CASES")),
                    ("REG_Q23_REFUSALS", REG_Q23_REFUSALS, bad_move_problems),
                    ("REG_E57_ACCEPTS", REG_E57_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="REG_E57_ACCEPTS")),
                    ("REG_INSTALL_CASES", REG_INSTALL_CASES, install_case_problems),
                    ("REG_BAD_MOVES", REG_BAD_MOVES, bad_move_problems),
                    ("REG_BAD_MOVES_CHANGED", REG_ACCEPTED_MOVES,
                     lambda c: subst_accept_problems(c, table="REG_BAD_MOVES_CHANGED")),
                    ("E56_REVIEW_CASES", REVIEW_BAD, bad_move_problems),
                    ("E56_REVIEW_CASES", REVIEW_ACCEPTS,
                     lambda c: subst_accept_problems(c, table="E56_REVIEW_CASES")),
                    ("E57_BAD_MOVES", E57_BAD_MOVES, bad_move_problems),
                    ("BAD_MOVES", BAD_MOVES, bad_move_problems)):
                for c in cases:
                    try:
                        problems = fn(c)
                    except Mismatch as m:
                        problems = [str(m)]
                    if problems:
                        found.append([table, c["id"]])
            for b in REG_BAD_MOVES:
                if "as_well" in b:
                    try:
                        as_well[b["id"]] = bad_move_problems(dict(b, message=b["as_well"]))
                    except Mismatch as m:
                        as_well[b["id"]] = [str(m)]
            families = [c[1] for c in bug.get("caught_by", ()) if c[0] == "PROPERTY"]
            if families:
                results = TD.property_results(families=families)
                found += [["PROPERTY", n] for n, st in results.items() if st.violations]
    except Exception:  # noqa: BLE001 -- a crash, not a catch
        traceback.print_exc()
        return 2
    print(json.dumps({"mismatches": found, "admissions": admissions, "as_well": as_well}))
    return 0


def reg_child_results():
    from concurrent.futures import ThreadPoolExecutor
    names = [None, *REG_BUGS]
    with ThreadPoolExecutor(max_workers=max(2, min(8, os.cpu_count() or 2))) as ex:
        futures = {n: ex.submit(spawn, *(("--reg-control",) if n is None else
                                         ("--reg", n))) for n in names}
    return {n: f.result() for n, f in futures.items()}


def reg_planted_problems(name, result):
    data, out = result
    if data is None:
        return out
    found = data["mismatches"]
    if name is None:
        out += [f"unpatched child found {m}" for m in sorted(found, key=str)]
        if data["admissions"] != ADMISSIONS:
            out.append(f"unpatched admissions {data['admissions']}")
        return out
    bug = REG_BUGS[name]
    out += [f"not caught at {c}" for c in map(tuplify, bug["caught_by"]) if c not in found]
    if "admissions" in bug and closed_admissions(data) != bug["admissions"]:
        out.append(f"admissions {data['admissions']}, expected {bug['admissions']}")
    for cid in REG_AS_WELL.get(name, ()):  # 'expect': refused as_well
        if data["as_well"].get(cid):
            out.append(f"{cid} is not refused with its as_well message: "
                       f"{data['as_well'][cid]}")
    return out


# ---------------------------------------------------------------- main

# The review of the wired discharge (b99972e): inputs deeper than the stack,
# F3's definedness of the domain items, its point bound, and certificates
# the tracker keeps. Each must return a state or a clean Refusal, never an
# exception.
DEEP_SUM = "1/(" + " + ".join(["x"] * 500) + ") == ?A @ x in (2, 3)"
DEEP_CLOSE = ("y - y == ?A @ y > 0", "0*(1/(" + " + ".join(["y"] * 600) + "))")
# 2 + sin, not exp: exp_pos (E103) now decides a sum of exps positive, and
# nothing bounds sin, so the sum stays undecided and is never refuted
NINE_VARIABLES = "ln(" + " + ".join(f"(2 + sin x{i})" for i in range(1, 10)) + ") == ?A"


def _timed(thunk):
    import time
    t = time.perf_counter()
    try:
        r = thunk()
    except Exception as e:  # noqa: BLE001 -- the failure being guarded against
        r = e
    return r, time.perf_counter() - t


def _cpu_timed(thunk, bound):
    """(result, seconds) for thunk, the seconds being this process's CPU
    time (time.process_time), which other processes' load does not add to,
    unlike the wall clock. A run over `bound` is repeated once and the
    smaller time kept, so a scheduling hiccup cannot fail a bound that the
    code itself meets, while a regression (it costs its time on every run)
    still fails it."""
    import time
    best, r = None, None
    for _ in range(2):
        t = time.process_time()
        try:
            r = thunk()
        except Exception as e:  # noqa: BLE001 -- the failure being guarded against
            r = e
        secs = time.process_time() - t
        best = secs if best is None else min(best, secs)
        if best <= bound or isinstance(r, Exception):
            break
    return r, best


def deep_input_problems():
    """A sum of 500 x's in a divisor installs, a close whose value holds a
    600-term divisor is refused close-not-evaluated, and 1/(x - 1)^300
    installs: discharge's rewrite is iterative, the checker maps a
    RecursionError to a rejection, _emit's steps (4)-(6) treat one as no
    rewrite, certificate or refutation, and the search's factorisations
    nest at most tagger.FACTOR_DEPTH deep. 1/(x - 1)^150 installs within 3 s
    of CPU time (_cpu_timed; it took 4.5 s before the bound, and 5.7 s in
    the regression the review found)."""
    out = []
    r, _ = _timed(lambda: K.install(goal(DEEP_SUM)))
    if not isinstance(r, K.ProofState):
        out.append(f"500-term divisor: {describe(r)}")
    g, v = DEEP_CLOSE
    st = K.install(goal(g))
    r, _ = _timed(lambda: K.step(st, "close", {"value": term(v), "check": "ring",
                                               "facts": []}))
    if not (isinstance(r, K.Refusal) and r.code == "close-not-evaluated"):
        out.append(f"600-term close value: {describe(r)}")
    for n, limit in ((300, None), (150, 3.0)):
        r, secs = _cpu_timed(lambda n=n: K.install(goal(f"1/(x - 1)^{n} == ?A @ x in (2, 3)")),
                             limit if limit is not None else float("inf"))
        if not isinstance(r, (K.ProofState, K.Refusal)):
            out.append(f"1/(x - 1)^{n}: {describe(r)}")
        if limit is not None and secs > limit:
            out.append(f"1/(x - 1)^{n} took {secs:.1f} s, more than {limit} s")
    return out


def huge_input_problems():
    """The skeptic's inputs beyond the bounds, each a Refusal (or a state),
    never an exception, and quick: x := t^1000000000 at t = 3 (it ran over
    90 s) within 2 s; a residual whose constant is too long for str() gives
    a truncated message, the residual itself kept whole; and a programmatic
    substitution 600 nodes deep, in int_subst's sub and in ftc's F
    (terms.subst is iterative)."""
    out = []
    st = K.install(goal("Int[x = 0 .. 1] x == ?A"))
    args = {"var": "x", "sub": term("t^1000000000"), "new_var": "t",
            "lo": term("3"), "hi": term("1"), "check": "ring", "facts": []}
    r, secs = _timed(lambda: K.step(st, "int_subst", args))
    if not (isinstance(r, K.Refusal) and r.code == "power-too-large"):
        out.append(f"t^1000000000 at 3: {describe(r)}")
    if secs > 2.0:
        out.append(f"t^1000000000 at 3 took {secs:.1f} s, more than 2 s")
    # 3^4000 is within the bounds (2 * 4000 bits <= 8192); the product of
    # three has 5726 digits, which str() will not print, so the message
    # names the number instead
    st = K.install(goal("x == ?A @ x > 0"))
    r, _ = _timed(lambda: K.step(st, "close", {"value": term("3^4000*3^4000*3^4000"),
                                               "check": "ring", "facts": []}))
    if not (isinstance(r, K.Refusal) and r.code == "close-check-failed"
            and "too large to print" in r.message and r.residual is not None):
        out.append(f"a residual too long to print: {describe(r)}")
    deep = T.Var("t")
    for _ in range(600):
        deep = T.Add(deep, T.Num(1))
    st = K.install(goal("Int[x = 0 .. 1] x == ?A"))
    r, _ = _timed(lambda: K.step(st, "int_subst", {
        "var": "x", "sub": deep, "new_var": "t", "lo": term("0"), "hi": term("1"),
        "check": "ring", "facts": []}))
    if not isinstance(r, (K.ProofState, K.Refusal)):
        out.append(f"a 600-deep sub: {describe(r)}")
    F = T.Var("x")
    for _ in range(600):
        F = T.Add(F, T.Num(0))
    st = K.install(goal("Int[x = 0 .. 1] 2*x == ?A"))
    r, _ = _timed(lambda: K.step(st, "ftc", {"F": T.Mul(F, F), "check": "ring",
                                             "facts": []}))
    if not isinstance(r, K.ProofState):
        out.append(f"ftc with a 600-deep F: {describe(r)}")
    return out


def point_bound_problems():
    """COUNTERPOINT_CANDIDATES' 256-point bound: nine variables give 3^9
    candidate points, and the walk stops at 256, so installation completes
    quickly with ln's argument admitted, tagged none."""
    r, secs = _timed(lambda: K.install(goal(NINE_VARIABLES)))
    if not isinstance(r, K.ProofState):
        return [f"refused or raised: {describe(r)}"]
    # 8 s since E103: the sum is of 2 + sin, whose search per point costs
    # more than exp's did; 3^9 unbounded points would take about 20 minutes
    out = [] if secs <= 8.0 else [f"took {secs:.1f} s, more than 8 s"]
    admitted = [o for o in r.last.emitted if o.status == K.ADMITTED]
    if [(T.show(o.key), tag_of(o), o.reason) for o in admitted] != [
            (T.show(key(NINE_VARIABLES.split(" == ")[0][3:-1] + " > 0", "true")),
             X.T_NONE, X.REASON_NONE)]:
        out.append(f"admitted {[(T.show(o.key), o.tag, o.reason) for o in admitted]}")
    return out


def f3_definedness_problems():
    """COUNTERPOINT_CANDIDATES as amended: a point counts only where the
    domain items' formers are settled too. x > 0 on [0, 1] with a
    hypothesis whose real power owes x^2 > 0 is not refuted at x = 0, where
    that hypothesis is undefined. End to end, ln(x - 5) under such a
    hypothesis on [5, 6] is refused, and by the hypothesis's own former:
    (x - 5)^2 > 0, charged on the empty domain (it is the first
    hypothesis), is false at its root x = 5 (E50's candidate), which is the
    point where the hypothesis is undefined. Before E50 the goal installed
    with both keys admitted, tagged none; ln's x - 5 > 0 was never refuted
    at 5, and still is not."""
    import refute as RF
    out = []
    k = T.parse_judgement("x > 0 @ x in [0, 1], ((x^2)^(1/2))^2 + 1 > 0", SIG)
    r = RF.refute(k, K._owed)
    if r is not None:
        out.append(f"refuted: {r.message}")
    st = K.install(goal("ln(x - 5) == ?A @ (((x-5)^2)^(1/2))^2 + 1 > 0, x in [5, 6]"))
    return out + refusal_problems_of(st, {
        "refusal": X.OBLIGATION_DECIDED_FALSE,
        "message": X._point("(x - 5)^2 > 0", "(5 - 5)^2 > 0", x="5")})


def frozen_certificate_problems():
    """An obligation's certificate is deep-frozen: no write through what
    obligations() returns reaches the one the tracker keeps."""
    run = run_proof("P1.2", strict=False, out=lambda line: None)
    obs = [o for o in run.state.obligations() if o.certificate is not None]
    if not obs:
        return ["no obligation carries a certificate"]
    def snapshot(x):  # a plain copy, nested mappings and tuples included
        if isinstance(x, (dict, types.MappingProxyType)):
            return {k: snapshot(v) for k, v in x.items()}
        return tuple(map(snapshot, x)) if isinstance(x, tuple) else x

    out = []
    for o in obs:
        before = snapshot(o.certificate)
        attempts = [lambda c: c.__setitem__("method", "hyp"),
                    lambda c: c.__setitem__("extra", 1)]
        for field in ("multipliers", "inst"):
            if field in o.certificate:
                attempts.append(lambda c, f=field: c[f].__setitem__("x", 1))
        for field in ("squares", "factors", "hyps"):
            if field in o.certificate:
                attempts.append(lambda c, f=field: c[f].append(None))
        for attempt in attempts:
            try:
                attempt(o.certificate)
                out.append(f"{T.show(o.key)}: a write to its certificate succeeded")
            except (TypeError, AttributeError):
                pass
        if snapshot(o.certificate) != before:
            out.append(f"{T.show(o.key)}: its certificate changed")
    return out


def kernel_constant_problems():
    pairs = [("HANDLES_IN_FORCE", "HANDLES_IN_FORCE"), ("VERDICT", "VERDICT"),
             ("REASON_REG", "REASON_REG"), ("REASON_NONE", "REASON_NONE"),
             ("REASON_REJECTED", "REASON_REJECTED"), ("REASON_EMPTY", "REASON_EMPTY"),
             ("DECIDED_FALSE", "OBLIGATION_DECIDED_FALSE")]
    out = [f"{k} is {getattr(K, k, None)!r}, expected {getattr(X, x)!r}"
           for k, x in pairs if getattr(K, k, None) != getattr(X, x)]
    if hasattr(K, "ADMISSION_REASON"):
        out.append(f"ADMISSION_REASON {K.ADMISSION_REASON!r} is still defined")
    return out


def by_item(run, item):
    return [fmt(w, d) for i, w, d in run.found if i == item]


def main():
    suite = Suite()
    print("proof_of_life: readiness P1 against p1_expected.py (WHAT.md Done-when 1-6), "
          "and stage 0's problem files against stage0/expected.py (item 7)")
    print("protection in force (§15.3): "
          + (K.HANDLES_IN_FORCE if K is not None
             else "unknown (the kernel did not import)"))
    print("  fact slots take only the handle `fact` minted, by identity (E17); a "
          "proof state demands the kernel-private _TOKEN, which is enough because a "
          "finished state is only ever produced by step(), and §15.3's realistic "
          "threat, a buggy tactic building a result object, is refused; §16.3's API "
          "boundary, not built here, will replace in-process states with ids")
    suite.check(1, "the kernel imports, its HANDLES_IN_FORCE, VERDICT, admission "
                "reasons and decided-false code are p1_expected's, and 'discharge "
                "not built' is retired", kernel_constant_problems)
    suite.check(1, "the §6.8 entries are pinned as NAMED_ENTRIES states them",
                entries_problems)

    runs = {}
    for name, p in PROOFS.items():
        route = [r for r, n in ROUTE.items() if n == name]
        print(f"\n{name}{' (fallback)' if p['fallback'] else ''}"
              + (f" (ROUTE['{route[0]}'])" if route else ""))
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
                     f"?A := {ANSWERS[name]}, N = {ADMISSIONS[name]}, "
                     f"'{VERDICTS[name]}'", by_item(run, 1))
        suite.record(2, f"{name}: every step's obligations (sources, status, tag, "
                     "new), deriv's trace, the final tracker, no tag none",
                     by_item(run, 2))
        suite.check(1, f"{name}: the answer is the integral (math module)",
                    lambda name=name: numeric_problems(name), needs_kernel=False)

    if CONSOLIDATED and K is not None:
        suite.check(1, "ROUTE['P1.1'] is P1.1-sheet (E52), and each ROUTE entry is a "
                    "PROOFS proof that closes with its problem's answer",
                    lambda: route_problems(runs))

    print("\nMatching, occurrences and deriv")
    for m in MATCH_ACCEPTS:
        suite.check(2, f"MATCH_ACCEPTS {m['id']}", lambda m=m: match_problems(m))
    for c in DEFINEDNESS_CASES:
        want = c["refusal"] + " at install" if "refusal" in c else repr(c["report"])
        suite.check(2, f"DEFINEDNESS_CASES {c['id']}: {c['goal']} -> {want}",
                    lambda c=c: definedness_problems(c))
    for which in ("all", "one"):
        c = OCCURRENCE_CASE[which]
        want = (c["refusal"] if "refusal" in c else
                f"{c['occurrences']} occurrence(s)")
        suite.check(2, f"OCCURRENCE_CASE {which}: {want}",
                    lambda w=which: occurrence_problems(w))
    for c in UNDECIDED:
        suite.check(2, f"DISCHARGE_UNDECIDED {c['id']}: admitted, tagged none",
                    lambda c=c: undecided_problems(c))
    suite.check(2, "OCCURRENCE_CASE one with occurrence 1 rewrites the second Int",
                occurrence_k_problems)
    suite.check(2, "F3 counts a point only where the domain items are defined "
                "(COUNTERPOINT_CANDIDATES, amended), and E50's root refutes the "
                "undefined hypothesis's own former", f3_definedness_problems)

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
    for b in BAD_MOVES:
        suite.check(5, f"{b['id']}{' (added)' if b.get('added') else ''} -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))
    for b in SUITE_BAD_MOVES:
        suite.check(5, f"{b['id']} (suite) -> {b['refusal']}",
                    lambda b=b: bad_move_problems(b))

    print("\nEvaluated answers (E27)")
    suite.check(5, f"E27's clause, subterm and entry for its {len(e27_cases())} "
                "refusals, by schema.evaluated_offence on the value",
                e27_clause_problems)
    order = [b for b in BAD_MOVES if b["id"].startswith("e27_") and "e27" not in b]
    if not order:
        suite.record(5, "E27's order in close", ["no ordering case in BAD_MOVES"])
    for b in order:
        suite.check(5, f"{b['id']} (added): wrong and unevaluated -> {b['refusal']} "
                    "with residual lhs - value, before E27", lambda b=b: e27_order_problems(b))
    for c in EVALUATED_ACCEPTS:
        suite.check(5, f"EVALUATED_ACCEPTS {c['id']} ({c['kind']}): {c['value']} "
                    "closes by refl", lambda c=c: evaluated_accept_problems(c))
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
    suite.check(5, f"a close value of {DEEP_NEGS} nested Negs is refused, not crashed, "
                "by E27 (b4) and by E23 (close-schema-not-closed)",
                deep_neg_close_problems)
    suite.check(5, f"REWRITE_RULE 9(a)'s subterm clause, directly: {len(OPEN_IN_CASES)} "
                "hypotheses", open_in_problems)
    suite.check(5, "inputs deeper than the stack (a 500-term divisor, a 600-term close "
                "value, 1/(x - 1)^300) give a state or a Refusal, never an exception; "
                "1/(x - 1)^150 installs within 3 s", deep_input_problems)
    suite.check(5, "inputs beyond the bounds give a Refusal, never an exception: "
                "t^1000000000 at 3 within 2 s, a residual too long to print, and a "
                "600-deep sub and F (terms.subst iterative)", huge_input_problems)
    suite.check(5, "F3 walks at most 256 points: nine variables install within 8 s, "
                "ln's argument admitted", point_bound_problems)
    suite.check(5, "a certificate the tracker keeps cannot be written through "
                "obligations()", frozen_certificate_problems)

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

    print("\nProblem files: stage 0's S1-S3 through the loader (item 7)")
    s0_runs = s0_checks(suite) if K is not None else {}

    print("\nDischarge's parts, called directly (item D)")
    discharge_checks(suite)

    print("\nint_subst (item S; p1_expected section 12)")
    s_runs = subst_checks(suite) if K is not None else {}

    print("\nThe consolidation (item C; p1_expected sections 13-14)")
    if K is not None and CONSOLIDATED:
        consolidation_checks(suite)

    print("\nRegularity (item R; p1_expected section 17)")
    if K is not None and REGULARITY:
        regularity_checks(suite)

    print("\nint_parts and ftc at an occurrence (item P; p1_expected section 19)")
    if K is not None:
        parts_checks(suite)

    print("\nint_improper, limits and the sign node (item I; p1_expected section 20)")
    if K is not None:
        improper_checks(suite)

    print("\ntrig_norm (item T; p1_expected section 22)")
    if K is not None:
        trig_checks(suite)

    print("\nTaylor with the Lagrange remainder (item L; p1_expected section 25)")
    if K is not None:
        taylor_checks(suite)

    print("\nverify and unit 00 (item U; p1_expected section 26)")
    if K is not None:
        unit00_checks(suite)

    print("\nfield's atom arguments (item G; p1_expected section 27)")
    if K is not None:
        g8_checks(suite)

    print("\nstrict Taylor bounds and bound's scale (item K; p1_expected "
          "section 28)")
    if K is not None:
        strict_checks(suite)

    print("\nclearing a denominator (item Q; p1_expected section 29)")
    if K is not None:
        clear_checks(suite)

    print("\nassumptions and the ODE rules (item O; p1_expected section 30)")
    if K is not None:
        ode_checks(suite)

    print("\nPlanted bugs (each in a child process)")
    suite.check(3, "control: the child, unpatched, finds nothing", control_problems)
    for name, bug in PLANTED_BUGS.items():
        suite.check(3, f"{name}: caught at {len(bug['caught_by'])} location(s)",
                    lambda n=name, b=bug: planted_problems(n, b))
    print("\nDefinedness mutations (E26; each in a child process)")
    results = mutation_results() if K is not None else {}
    for name, m in DEFINEDNESS_MUTATIONS.items():
        suite.check(3, f"{name}: {m['mutation']}; caught at {len(m['caught_by'])} "
                    "location(s)", lambda n=name, m=m: mutation_problems(m, results[n], n))
    print("\nDischarge planted bugs (each in a child process)")
    dresults = discharge_plant_results() if TD is not None else {}
    suite.check(3, "discharge control: the child, unpatched, finds nothing in the "
                "proofs or the must-reject cases",
                lambda: discharge_planted_problems(None, dresults[None]))
    for name, bug in DISCHARGE_BUGS.items():
        suite.check(3, f"{name}: {bug['mutation']}; caught at "
                    f"{len(bug['caught_by'])} location(s)",
                    lambda n=name: discharge_planted_problems(n, dresults[n]))
    print("\nint_subst planted bugs and re-traced seams (each in a child process)")
    sresults = subst_child_results() if K is not None and S0 is not None else {}
    suite.check(3, "int_subst control: the child, unpatched, finds nothing",
                lambda: subst_planted_problems(None, sresults[None]))
    for name, bug in {**SUBST_BUGS, **SUBST_SEAMS}.items():
        suite.check(3, f"{name}: {bug.get('mutation', 're-traced on int_subst')}; "
                    f"caught at {len(bug['caught_by'])} location(s)",
                    lambda n=name: subst_planted_problems(n, sresults[n]))
    if CONSOLIDATED:
        print("\nConsolidation planted bugs (sections 13-14; each in a child process)")
        cresults = consolidation_child_results() if K is not None and TD is not None else {}
        suite.check(3, "consolidation control: the child, unpatched, finds nothing",
                    lambda: consolidation_planted_problems(None, cresults[None]))
        for name, bug in CONSOLIDATION_BUGS.items():
            suite.check(3, f"{name}: {bug['mutation']}; caught at "
                        f"{len(bug['caught_by'])} location(s)",
                        lambda n=name: consolidation_planted_problems(n, cresults[n]))
    if REGULARITY:
        print("\nRegularity planted bugs (section 17; each in a child process)")
        rresults = reg_child_results() if K is not None and TD is not None else {}
        suite.check(3, "regularity control: the child, unpatched, finds nothing",
                    lambda: reg_planted_problems(None, rresults[None]))
        for name, bug in REG_BUGS.items():
            suite.check(3, f"{name}: {bug['mutation']}; caught at "
                        f"{len(bug['caught_by'])} location(s)",
                        lambda n=name: reg_planted_problems(n, rresults[n]))
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
    for name in [*PROOFS, *INT_SUBST_PROOFS,
                 *(S0.PROOF_FILES if S0 is not None else ()),
                 *(S0.INT_SUBST_PROOF_FILES if S0 is not None else ()),
                 *(S0.CONSOLIDATION_PROOF_FILES if S0 is not None and CONSOLIDATED
                   else ())]:
        run = runs.get(name) or s_runs.get(name) or s0_runs.get(name)
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
    if sys.argv[1:2] == ["--s0-seam"] and len(sys.argv) == 3:
        sys.exit(s0_seam_child(sys.argv[2]))
    if sys.argv[1:2] == ["--discharge-plant"] and len(sys.argv) == 3:
        sys.exit(discharge_child(sys.argv[2]))
    if sys.argv[1:] == ["--discharge-control"]:
        sys.exit(discharge_child(None))
    if sys.argv[1:2] == ["--int-subst"] and len(sys.argv) == 3:
        sys.exit(subst_child(sys.argv[2]))
    if sys.argv[1:] == ["--int-subst-control"]:
        sys.exit(subst_child(None))
    if sys.argv[1:2] == ["--reg"] and len(sys.argv) == 3:
        sys.exit(reg_child(sys.argv[2]))
    if sys.argv[1:] == ["--reg-control"]:
        sys.exit(reg_child(None))
    if sys.argv[1:2] == ["--consolidation"] and len(sys.argv) == 3:
        sys.exit(consolidation_child(sys.argv[2]))
    if sys.argv[1:] == ["--consolidation-control"]:
        sys.exit(consolidation_child(None))
    sys.exit(main())
