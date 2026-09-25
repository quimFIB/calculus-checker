"""Discharge's parts called directly: the trusted checkers (discharge.py),
the untrusted search (search.py) and the untrusted decided-false check
(refute.py), against p1_expected's section 11 and
problems/stage0/expected.py's. Nothing here goes through kernel.step;
proof_of_life.py's items 1-7 assert discharge through it, wired into
kernel._emit (DISCHARGE_SWITCH (2)), and this file tests the parts apart,
where a must-reject certificate or a random key can be handed to them.

Run: python3 -m unittest -v test_discharge (in kernel/), or python3
test_discharge.py. proof_of_life.py also calls the `*_problems` functions
below one case at a time, and its discharge planted-bug children call
`property_results` and `must_reject_accepted` under each seam patch.

What is checked:

- every certificate the spec gives (DISCHARGE_EXPECTED for P1 and stage 0,
  DISCHARGE_MATCH_ACCEPTS, DISCHARGE_OCCURRENCE_CASE, the certificates of
  DISCHARGE_DEFINEDNESS_CASES and DISCHARGE_BAD_MOVES_ADDED) is accepted
  with exactly its tag, and the search's own certificate for that key is
  the same one, compared as DISCHARGE_RULE says;
- every DISCHARGE_MUST_REJECT certificate is rejected for its stated reason
  (REJECT_REASONS maps each case's prose to the checker's reason code), its
  'truth' holds, and its 'if_emitted' outcome is what DISCHARGE_RULE's order
  gives (`outcome`); every DISCHARGE_CHECKER_ACCEPTS neighbour is accepted;
- every decided-false message the spec states for a key, filled from
  DECIDED_FALSE_MESSAGES, and every DISCHARGE_UNDECIDED key's admission;
- the pinned entries (DISCHARGE_NEW_ENTRIES at their positions, and
  EXACT_VALUE_ENTRIES as ENTRIES' exact values);
- SQRT_FACT_MUST_REJECT and SQRT_FACT_CHECKER_ACCEPTS, E49's sqrt_nonneg
  label, whose Farkas family in the property test holds sqrt of a linear
  polynomial, sampled where it is a rational square;
- DISCHARGE_PROPERTY_TEST: every accept of every checker holds at sampled
  rational points of its domain by this file's own exact evaluation, and
  every refutation is false where it says, by an independent reading.
"""

import copy
import importlib.util
import itertools
import math
import random
import sys
import unittest
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import discharge as DC  # noqa: E402
import field as FD  # noqa: E402
import kernel as K  # noqa: E402
import p1_expected as X  # noqa: E402
import poly as P  # noqa: E402
import refute as RF  # noqa: E402
import residual  # noqa: E402
import search as SR  # noqa: E402
import tagger as TG  # noqa: E402
import terms as T  # noqa: E402
from entries import ENTRIES  # noqa: E402


def _load_stage0():
    path = HERE / "problems" / "stage0" / "expected.py"
    spec = importlib.util.spec_from_file_location("stage0_expected_d", path)
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    return data


S0 = _load_stage0()
GOAL = X.GOAL

# DISCHARGE_UNDECIDED and DISCHARGE_BAD_MOVES_ADDED as F3_ROOTS_CHANGES
# re-traces them once F3 tries rational roots (E50, REVIEW_SWITCH): the
# unbounded-range key is now refused at its root x = 5, and the
# false-but-undecided example is the irrational pole.
_ROOTS = X.F3_ROOTS_CHANGES
DISCHARGE_UNDECIDED = [c for c in X.DISCHARGE_UNDECIDED
                       if c["id"] not in _ROOTS["DISCHARGE_UNDECIDED_remove"]] \
    + list(X.F3_ROOTS_UNDECIDED)
DISCHARGE_BAD_MOVES_ADDED = list(X.DISCHARGE_BAD_MOVES_ADDED) \
    + list(_ROOTS["DISCHARGE_BAD_MOVES_ADDED_add"])
# E56_CHANGES (CONSOLIDATION_SWITCH): decided_false_reversed_range installs
# now, and rewrite_under_D_through_Int is refused 'orientation-undecided'
# before its orientation key is emitted, so neither states a decided-false
# key any more; E56_BAD_MOVES decided_false_closed_negation is F2's example.
DISCHARGE_BAD_MOVES_ADDED = [c for c in DISCHARGE_BAD_MOVES_ADDED
                             if c["id"] != "decided_false_reversed_range"]
DISCHARGE_BAD_MOVES_CHANGED = {i: c for i, c in X.DISCHARGE_BAD_MOVES_CHANGED.items()
                               if i != "rewrite_under_D_through_Int"}


# ---------------------------------------------------------------- data to calls

def term(s):
    return T.parse_term(s, X.SIG)


def judgement(s):
    return T.parse_judgement(s, X.SIG)


def key(prop, dom):
    return judgement(X.judgement_string(prop, dom))


def cert_of(c):
    """A spec certificate (rationals and terms as strings) in the checker's
    form (Fractions and Terms), recursively."""
    m = c["method"]
    if m == "farkas":  # E49's sqrt label carries its argument as a string
        return {**c, "multipliers": {
            (lab[:2] + (term(lab[2]),) if _sqrt_label(lab) else lab): Fraction(q)
            for lab, q in c["multipliers"].items()}}
    if m == "sign":
        return {**c, "const": Fraction(c["const"]),
                "squares": tuple((Fraction(a), term(s), k)
                                 for a, s, k in c["squares"])}
    if m == "sign product":
        return {**c, "content": Fraction(c["content"]),
                "factors": tuple((term(f), r, cert_of(cc))
                                 for f, r, cc in c["factors"])}
    if m == "cite":
        return {**c, "inst": {v: term(s) for v, s in c["inst"].items()},
                "hyps": tuple((judgement(p), cert_of(cc))
                              for p, cc in c["hyps"])}
    if m == "reg" and isinstance(c.get("tree"), dict):
        return {**c, "tree": _reg_node_of(c["tree"])}
    return dict(c)


def _reg_node_of(n):
    """A regularity certificate node (REG_CERTIFICATE) in the checker's
    form: each side's proposition parsed, its certificate converted. A node
    that is not REG_CERTIFICATE's shape passes through, for the checker to
    reject."""
    if not (isinstance(n, dict) and set(n) == {"rule", "args", "side"}):
        return n
    return {"rule": n["rule"], "args": tuple(_reg_node_of(a) for a in n["args"]),
            "side": tuple((judgement(p), cert_of(cc)) for p, cc in n["side"])}


def show_tag(tag):
    return None if tag is None else (tag[0], tuple(tag[1]))


# ---------------------------------------------------------------- comparing certificates

def _same_nf(a, b, up_to_sign=False):
    p, q = FD.ring_polys([a, b])[0]
    return p == q or (up_to_sign and p == P.neg(q))


def _sqrt_label(lab):
    """E49's ('fact', 'sqrt_nonneg', u), as against ('dom', i, 'lo') and the
    two-part fact labels."""
    return len(lab) == 3 and lab[0] == "fact"


def _same_multipliers(got, want):
    """Farkas multipliers equal, E49's sqrt labels compared by the ring
    normal form of their argument (SQRT_FACT_RULE), every other label
    exactly."""
    plain = [{lab: q for lab, q in ms.items() if not _sqrt_label(lab)}
             for ms in (got, want)]
    if plain[0] != plain[1]:
        return False
    left = [(lab, q) for lab, q in got.items() if _sqrt_label(lab)]
    for lab, q in ((lab, q) for lab, q in want.items() if _sqrt_label(lab)):
        hit = next((g for g in left if g[0][:2] == lab[:2] and g[1] == q
                    and _same_nf(g[0][2], lab[2])), None)
        if hit is None:
            return False
        left.remove(hit)
    return not left


def cert_differences(got, want, where="certificate"):
    """[] when `got` is `want` as DISCHARGE_RULE compares them: Farkas
    multipliers exactly, scaled so that ('goal',) has 1; a sign
    certificate's c0 exactly and its squares as a multiset of (ci, ki, ring
    normal form of si up to sign); a product's content exactly and its
    factors as a multiset of (ring normal form of fj, rj), each certificate
    recursively; a cite's entry, instantiation and children; hyp and the
    leaf as they are."""
    if got is None:
        return [f"{where}: none"]
    if got.get("method") != want["method"] or set(got) != set(want):
        return [f"{where}: {got.get('method')} {sorted(got)}, expected "
                f"{want['method']} {sorted(want)}"]
    m, out = want["method"], []
    if "sense" in want and got["sense"] != want["sense"]:
        out.append(f"{where}: sense {got['sense']!r}, expected {want['sense']!r}")
    if m == "farkas":
        def scaled(ms):
            g = ms.get(GOAL)
            return {lab: q / g for lab, q in ms.items()} if g else ms
        if not _same_multipliers(scaled(got["multipliers"]),
                                 scaled(want["multipliers"])):
            out.append(f"{where}: multipliers {got['multipliers']}, expected "
                       f"{want['multipliers']}")
    elif m == "sign":
        if got["const"] != want["const"]:
            out.append(f"{where}: const {got['const']}, expected {want['const']}")
        left = list(got["squares"])
        for c, s, k in want["squares"]:
            hit = next((g for g in left if g[0] == c and g[2] == k
                        and _same_nf(g[1], s, up_to_sign=True)), None)
            if hit is None:
                out.append(f"{where}: no square {c}*({T.show(s)})^{k}")
            else:
                left.remove(hit)
        out += [f"{where}: extra square {c}*({T.show(s)})^{k}" for c, s, k in left]
    elif m == "sign product":
        if got["content"] != want["content"]:
            out.append(f"{where}: content {got['content']}, expected "
                       f"{want['content']}")
        left = list(got["factors"])
        for f, r, c in want["factors"]:
            hit = next((g for g in left if g[1] == r and _same_nf(g[0], f)
                        and not cert_differences(g[2], c)), None)
            if hit is None:
                out.append(f"{where}: no factor {T.show(f)} {r} with its "
                           f"certificate")
            else:
                left.remove(hit)
        out += [f"{where}: extra factor {T.show(f)} {r}" for f, r, _ in left]
    elif m == "reg":
        out += _reg_differences(got["tree"], want["tree"], f"{where}/tree")
    elif m == "cite":
        if got["entry"] != want["entry"] or got["inst"] != want["inst"]:
            out.append(f"{where}: {got['entry']} {got['inst']}, expected "
                       f"{want['entry']} {want['inst']}")
        if len(got["hyps"]) != len(want["hyps"]):
            out.append(f"{where}: {len(got['hyps'])} hypotheses")
        for i, ((gp, gc), (wp, wc)) in enumerate(zip(got["hyps"], want["hyps"])):
            if gp != wp:
                out.append(f"{where}: hypothesis {T.show(gp)}, expected {T.show(wp)}")
            out += cert_differences(gc, wc, f"{where}/hyp {i}")
    elif got != want:
        out.append(f"{where}: {got}, expected {want}")
    return out


def _reg_differences(got, want, where):
    """Two regularity derivations compared node by node: the rule, the
    side propositions as trees, each side's certificate as
    cert_differences compares it, and the children in order."""
    if not (hasattr(got, "keys") and set(got) == {"rule", "args", "side"}):
        return [f"{where}: {got!r} is not a node"]
    out = []
    if got["rule"] != want["rule"]:
        return [f"{where}: rule {got['rule']!r}, expected {want['rule']!r}"]
    if len(got["side"]) != len(want["side"]):
        out.append(f"{where} {want['rule']}: {len(got['side'])} sides, expected "
                   f"{len(want['side'])}")
    for i, ((gp, gc), (wp, wc)) in enumerate(zip(got["side"], want["side"])):
        if gp != wp:
            out.append(f"{where} {want['rule']}: side {T.show(gp)}, expected {T.show(wp)}")
        out += cert_differences(gc, wc, f"{where} {want['rule']}/side {i}")
    if len(got["args"]) != len(want["args"]):
        return out + [f"{where} {want['rule']}: {len(got['args'])} children, expected "
                      f"{len(want['args'])}"]
    for i, (g, w) in enumerate(zip(got["args"], want["args"])):
        out += _reg_differences(g, w, f"{where}.{i}")
    return out


# ---------------------------------------------------------------- the expected certificates

def _tags(emits):
    return {(ob[0], ob[1]): ob[4] for ob in emits}


def expected_certificates():
    """(where, key, tag, spec certificate) for every certificate the two
    data files give."""
    rows = []
    for name, data in (("DISCHARGE_EXPECTED", X), ("stage0 DISCHARGE_EXPECTED", S0)):
        for proof, table in data.DISCHARGE_EXPECTED.items():
            for (p, d), (tag, c) in table.items():
                rows.append(((name, proof, p, d), key(p, d), tag, c))
    for case, table in X.DISCHARGE_MATCH_ACCEPTS.items():
        for (p, d), (tag, c) in table.items():
            rows.append((("DISCHARGE_MATCH_ACCEPTS", case, p, d), key(p, d), tag, c))
    oc = X.DISCHARGE_OCCURRENCE_CASE
    for part, emits, certs in (("goal", oc["goal_emits"], oc["goal_certificates"]),
                               ("one", oc["one"]["emits"], oc["one"]["certificates"])):
        tags = _tags(emits)
        for (p, d), c in certs.items():
            rows.append((("DISCHARGE_OCCURRENCE_CASE", part, p, d), key(p, d),
                         tags[(p, d)], c))
    cases = [(f"DISCHARGE_DEFINEDNESS_CASES {i}", c)
             for i, c in X.DISCHARGE_DEFINEDNESS_CASES.items()]
    cases += [(f"DISCHARGE_BAD_MOVES_ADDED {c['id']}", c)
              for c in DISCHARGE_BAD_MOVES_ADDED]
    for where, c in cases:
        tags = _tags(c.get("goal_emits", ()))
        for (p, d), cc in c.get("certificates", {}).items():
            rows.append(((where, p, d), key(p, d), tags[(p, d)], cc))
    # the consolidation (sections 13-14, stage 0's section 13): QC1's, the
    # new certificates of cos_theta_canonical (CONSOLIDATION_CHANGES), and
    # those of INT_FLIP_ACCEPTS and E56_ACCEPTS, tagged as their lists tag
    for proof, table in S0.CONSOLIDATION_EXPECTED.items():
        for (p, d), (tag, c) in table.items():
            rows.append((("stage0 CONSOLIDATION_EXPECTED", proof, p, d), key(p, d),
                         tag, c))
    # regularity (section 17): every Reg key's certificate, both files
    for name, data in (("REG_EXPECTED", X), ("stage0 REG_EXPECTED", S0)):
        for proof, table in data.REG_EXPECTED.items():
            for (p, d), (tag, c) in table.items():
                rows.append(((name, proof, p, d), key(p, d), tag, c))
    for (p, d), (tag, c) in X.REG_CASE_CERTS.items():
        rows.append((("REG_CASE_CERTS", p, d), key(p, d), tag, c))
    ch = X.CONSOLIDATION_CHANGES["INT_SUBST_ACCEPTS cos_theta_canonical"]
    tags = _tags(list(ch["goal_emits"]) + [ch["emits_change"]])
    for (p, d), c in ch["certificates_add"].items():
        rows.append((("CONSOLIDATION_CHANGES cos_theta_canonical", p, d), key(p, d),
                     tags[(p, d)], c))
    for table, cases in (("INT_FLIP_ACCEPTS", X.INT_FLIP_ACCEPTS),
                         ("E56_ACCEPTS", X.E56_ACCEPTS)):
        for c in cases:
            steps = [c] + list(c.get("then", ()))
            tags = _tags([ob for st in steps for name in ("goal_emits", "emits")
                          for ob in st.get(name, ())])
            for st in steps:
                for (p, d), cc in st.get("certificates", {}).items():
                    rows.append(((f"{table} {c['id']}", p, d), key(p, d),
                                 tags[(p, d)], cc))
    return rows


def expected_problems(row):
    """The checker accepts the spec's certificate with exactly its tag, and
    the search proposes the same certificate, which the checker accepts."""
    _, k, tag, spec = row
    out = []
    got, why = DC.verdict(k, cert_of(spec))
    if show_tag(got) != tag:
        out.append(f"the spec's certificate: {show_tag(got) or why}, expected {tag}")
    mine = SR.propose(k)
    out += cert_differences(mine, cert_of(spec), "the search's certificate")
    if mine is not None and show_tag(DC.check(k, mine)) != tag:
        out.append(f"the search's certificate: {DC.verdict(k, mine)}, expected {tag}")
    return out


# ---------------------------------------------------------------- must-reject, must-accept

# Each case's 'rejects_because', as the checker's reason code (discharge.
# REASONS). A child's rejection carries the child's own reason.
REJECT_REASONS = {
    "farkas_negative_multiplier": "multiplier-not-positive",
    "farkas_nonstrict_pair": "zero-without-strict",
    "farkas_constant_not_contradiction": "positive-constant",
    "farkas_not_constant": "not-constant",
    "farkas_label_not_in_set": "unknown-label",
    "farkas_fact_not_in_set": "unknown-label",
    "farkas_non_fact_entry": "unknown-label",
    "farkas_schema_entry_as_fact": "unknown-label",
    "farkas_infinite_end": "unknown-label",
    "farkas_nonzero_item": "unknown-label",
    "farkas_nonzero_without_sense": "bad-sense",
    "farkas_goal_unused": "goal-unused",
    "sign_false_quadratic": "constant-too-small",
    "sign_false_quadratic_forged": "identity-fails",
    "sign_forged_square": "identity-fails",
    "sign_odd_power": "bad-square",
    "sign_negative_coefficient": "bad-square",
    "sign_zero_constant_strict": "constant-too-small",
    "product_forged_factorisation": "identity-fails",
    # CONSOLIDATION_CHANGES (E53): the target is allowed, and the child
    # x > 0 @ [-1, 1] fails
    "product_nonstrict_target": "child-rejected/positive-constant",
    "product_parity": "parity",
    "product_child_at_closed_end": "child-rejected/zero-without-strict",
    "cite_pi_pos_for_e_const": "conclusion-does-not-imply",
    "cite_wrong_instance": "conclusion-does-not-imply",
    "cite_hypothesis_unproved": "child-rejected/zero-without-strict",
    "cite_hypothesis_missing": "hypothesis-count",
    "cite_not_syntactic": "conclusion-does-not-imply",
    "cite_equation_entry": "entry-not-ordering",
    "hyp_not_member": "not-member",
    "hyp_chain_broken": "chain-broken",
    "hyp_interval_item": "not-hypothesis-item",
    "norm_num_leaf_not_literal": "not-literal-true",
    # SQRT_FACT_MUST_REJECT (E49), with the review's
    # REVIEW_SQRT_FACT_MUST_REJECT
    "sqrt_fact_nonstrict_pair": "zero-without-strict",
    "sqrt_fact_absent_atom": "unknown-label",
    "sqrt_fact_label_for_absent_atom": "unknown-label",
    # SIGN_PRODUCT_MUST_REJECT (E53) and CONSOLIDATION_MUST_REJECT (E54)
    "product_nonstrict_factor_changes_sign": "child-rejected/positive-constant",
    "product_nonstrict_parity": "parity",
    "product_nonstrict_factor_under_strict_target": "bad-relation",
    "cos_fact_nonstrict_pair": "zero-without-strict",
    "sin_fact_not_a_label": "unknown-label",
}


def _sqrt_case(c):
    """A SQRT_FACT_* case in DISCHARGE_MUST_REJECT's shape ('cert')."""
    return {**c, "cert": c["certificate"]}


SQRT_FACT_MUST_REJECT = [_sqrt_case(c) for c in X.SQRT_FACT_MUST_REJECT
                         + X.REVIEW_SQRT_FACT_MUST_REJECT]
SQRT_FACT_CHECKER_ACCEPTS = [_sqrt_case(c) for c in X.SQRT_FACT_CHECKER_ACCEPTS]
# The consolidation's (sections 13c-13d), in the same shape: E53's
# non-strict sign product and E54's atom labels and cites.
SIGN_PRODUCT_MUST_REJECT = [_sqrt_case(c) for c in X.SIGN_PRODUCT_MUST_REJECT]
SIGN_PRODUCT_CHECKER_ACCEPTS = [_sqrt_case(c) for c in X.SIGN_PRODUCT_CHECKER_ACCEPTS]
CONSOLIDATION_MUST_REJECT = [_sqrt_case(c) for c in X.CONSOLIDATION_MUST_REJECT]
CONSOLIDATION_CHECKER_ACCEPTS = [_sqrt_case(c) for c in X.CONSOLIDATION_CHECKER_ACCEPTS]
# Every must-reject case beyond DISCHARGE_MUST_REJECT, by table name, for
# the planted-bug children (consolidation_accepted).
MORE_MUST_REJECT = {"SQRT_FACT_MUST_REJECT": SQRT_FACT_MUST_REJECT,
                    "SIGN_PRODUCT_MUST_REJECT": SIGN_PRODUCT_MUST_REJECT,
                    "CONSOLIDATION_MUST_REJECT": CONSOLIDATION_MUST_REJECT}


def sqrt_fact_accepted():
    """The SQRT_FACT_MUST_REJECT ids whose certificate the checker accepts
    (none, unless a seam is patched)."""
    return [c["id"] for c in SQRT_FACT_MUST_REJECT
            if DC.check(key(*c["key"]), cert_of(c["cert"])) is not None]


def outcome(k):
    """DISCHARGE_RULE's order at emission, steps (3)-(7), for a key that is
    not ftc's premise, read from the rule apart from kernel._emit, which
    implements it; a Reg by REG_DISCHARGE_ORDER (E60). ('discharged', tag,
    certificate), ('refused', code, message) or ('admitted', tag, reason).
    Γ is the key's non-Interval items, as a goal's own domain would give
    them."""
    gamma = tuple(i for i in k.dom if type(i) is not T.Interval)
    if type(k) is T.Reg:
        cert = SR.propose(k)
        tag = DC.check(k, cert) if cert is not None else None
        if tag is not None:
            return ("discharged", show_tag(tag), cert)
        r = RF.refute_reg(k, K._owed)
        if r is not None:
            return ("refused", X.OBLIGATION_DECIDED_FALSE, r.message)
        tag = show_tag(TG.tag(k, gamma))
        return ("admitted", tag, X.REASON_NONE if tag == X.T_NONE else X.REASON_REJECTED)
    try:
        said = FD.norm_num(k)
    except T.Refused as r:
        return ("refused", r.code, r.message)
    if said is not None:
        return (("discharged", ("norm_num", ()), None) if said else
                ("refused", "obligation-refuted", ""))
    new, used = DC.exact_values(k)
    said = FD.norm_num(new)
    if new != k and said is not None:
        if said:
            return ("discharged", ("norm_num", used), None)
        return ("refused", X.OBLIGATION_DECIDED_FALSE, RF.exact_false(k).message)
    cert = SR.propose(k)
    tag = DC.check(k, cert) if cert is not None else None
    if tag is not None:
        return ("discharged", show_tag(tag), cert)
    r = RF.refute(k, K._owed)
    if r is not None:
        return ("refused", X.OBLIGATION_DECIDED_FALSE, r.message)
    gamma = tuple(i for i in k.dom if type(i) is not T.Interval)
    tag = show_tag(TG.tag(k, gamma))
    reason = (X.REASON_EMPTY if SR.domain_empty(k) else
              X.REASON_NONE if tag == X.T_NONE else X.REASON_REJECTED)
    return ("admitted", tag, reason)


def expected_message(spec):
    """A DISCHARGE_* refusal (template key, parts) filled per
    DECIDED_FALSE_MESSAGES, every key and term printed by terms.show after
    parsing."""
    how, parts = spec
    if how in X.DECIDED_FALSE_MESSAGES_REG:  # E63: the side's own message inside
        return X.DECIDED_FALSE_MESSAGES_REG[how].format(
            key=T.show(judgement(parts["key"])), cond=T.show(judgement(parts["cond"])),
            inner=expected_message(parts["inner"]))
    fill = {"key": T.show(judgement(parts["key"]))}
    if "point" in parts:
        fill["point"] = ", ".join(f"{v} = {T.show(T.lit(Fraction(q)))}"
                                  for v, q in sorted(parts["point"].items()))
    for name in ("reading", "rewritten", "negation"):
        if name in parts:
            fill[name] = T.show(judgement(parts[name]))
    if "entries" in parts:
        fill["entries"] = ", ".join(parts["entries"])
    if "tag" in parts:
        fill["tag"] = ", ".join((parts["tag"][0],) + tuple(parts["tag"][1]))
    return X.DECIDED_FALSE_MESSAGES[how].format(**fill)


def must_reject_problems(case):
    out = []
    k, cert = key(*case["key"]), cert_of(case["cert"])
    got, why = DC.verdict(k, cert)
    if got is not None:
        return [f"accepted with {got}"]
    reason = REJECT_REASONS[case["id"]]
    if why != reason:
        out.append(f"rejected {why!r}, expected {reason!r} "
                   f"({case['rejects_because']})")
    if case["truth"][0] == "false":
        env = {v: Fraction(q) for v, q in case["truth"][1].items()}
        inside, held = judge_at(k, env)
        if not inside or held:
            out.append(f"truth: at {case['truth'][1]} in the domain {inside}, "
                       f"holds {held}")
    want, got = case["if_emitted"], outcome(k)
    if want[0] == "refused":
        if got[:2] != ("refused", X.OBLIGATION_DECIDED_FALSE) or \
                got[2] != expected_message(want[1]):
            out.append(f"if emitted: {got[:3]}, expected {expected_message(want[1])!r}")
    elif want[0] == "discharged":
        if got[:2] != ("discharged", want[1]):
            out.append(f"if emitted: {got[:2]}, expected {want}")
    elif got != tuple(want):
        out.append(f"if emitted: {got}, expected {want}")
    return out


def hyp_signed_member_problems():
    """hyp's member for e # 0 needs a strict item (e > 0, e < 0, 0 < e,
    0 > e): x >= 0 and 0 <= x do not give x # 0, which is false at x = 0.
    The strict items do."""
    out = []
    for dom, accepted in (("x >= 0", False), ("0 <= x", False), ("x <= 0", False),
                          ("x > 0", True), ("0 > x", True)):
        got, why = DC.verdict(key("x # 0", dom), {"method": "hyp", "member": 0})
        if (got is not None) != accepted:
            out.append(f"x # 0 @ {dom}: {got or why}, expected "
                       f"{'accepted' if accepted else 'rejected'}")
        elif not accepted and why != "not-member":
            out.append(f"x # 0 @ {dom}: rejected {why!r}, expected 'not-member'")
    return out


def checker_accept_problems(case):
    got, why = DC.verdict(key(*case["key"]), cert_of(case["cert"]))
    return [] if show_tag(got) == case["tag"] else [f"{show_tag(got) or why}, "
                                                    f"expected {case['tag']}"]


# ---------------------------------------------------------------- regularity (section 17)
#
# The regularity checker called directly (item D, REG_SWITCH commit 1):
# REG_MUST_REJECT rejected for its REG_REASONS name ('child-rejected' by
# prefix, the child's own reason after it), its point inside the domain,
# and its outcome if emitted; REG_CHECKER_ACCEPTS accepted with its tag;
# REG_DECIDED_FALSE refused with its message; every certificate REG_EXPECTED
# (both files) and REG_CASE_CERTS give accepted with its tag and proposed by
# the search node by node (expected_certificates); REG_SIDES_LISTED against
# the checker's own derivation of the sides; and the property test's 'reg'
# family.

def _reg_case(c):
    return {**c, "cert": c["cert"]}


REG_MUST_REJECT = [_reg_case(c) for c in X.REG_MUST_REJECT]
# the regularity review's (section 18): side certificates naming the item one
# past the Reg's domain, which only a checker that appends the side accepts
REG_REVIEW_MUST_REJECT = [_reg_case(c) for c in X.REG_REVIEW_MUST_REJECT]
REG_CHECKER_ACCEPTS = [_reg_case(c) for c in X.REG_CHECKER_ACCEPTS]


def reg_must_reject_problems(case):
    """One REG_MUST_REJECT case: rejected for its reason, its false point
    inside the key's domain, and the kernel's outcome if emitted."""
    out = []
    k, cert = key(*case["key"]), cert_of(case["cert"])
    got, why = DC.verdict(k, cert)
    if got is not None:
        return [f"accepted with {got}"]
    reason = case["rejects_because"]
    if not (why == reason or reason == "child-rejected" and why.startswith(reason + "/")):
        out.append(f"rejected {why!r}, expected {reason!r}")
    if case["truth"][0] == "false":
        env = {v: Fraction(q) for v, q in case["truth"][1].items()}
        try:
            if not in_domain(k.dom, env):
                out.append(f"truth: {case['truth'][1]} is not in the domain")
        except Skip:
            pass
    out += reg_outcome_problems(k, case["if_emitted"])
    return out


def reg_outcome_problems(k, want):
    got = outcome(k)
    if want[0] == "refused":
        msg = expected_message(want[1])
        if got[:2] != ("refused", X.OBLIGATION_DECIDED_FALSE) or got[2] != msg:
            return [f"if emitted: {got[:3]}, expected {msg!r}"]
    elif want[0] == "discharged":
        if got[:2] != ("discharged", want[1]):
            return [f"if emitted: {got[:2]}, expected {want}"]
    elif got != tuple(want):
        return [f"if emitted: {got}, expected {want}"]
    return []


def reg_decided_false_problems(case):
    """A REG_DECIDED_FALSE key emitted alone: refused by E63 with its
    message."""
    return reg_outcome_problems(key(*case["key"]), case["if_emitted"])


def reg_must_reject_verdicts():
    """[table, id] for each REG_MUST_REJECT and REG_REVIEW_MUST_REJECT case
    the checker accepts, or rejects for another reason (the planted-bug
    children's view)."""
    out = []
    for table, cases in (("REG_MUST_REJECT", REG_MUST_REJECT),
                         ("REG_REVIEW_MUST_REJECT", REG_REVIEW_MUST_REJECT)):
        for c in cases:
            got, why = DC.verdict(key(*c["key"]), cert_of(c["cert"]))
            reason = c["rejects_because"]
            if got is not None or not (why == reason or reason == "child-rejected"
                                       and why.startswith(reason + "/")):
                out.append([table, c["id"]])
    return out


def reg_side_key_rows():
    """(where, key, spec certificate) for every certificate REG_SIDE_KEY_RULE
    names: REG_EXPECTED (both files), REG_CASE_CERTS and REG_CHECKER_ACCEPTS."""
    rows = []
    for name, data in (("REG_EXPECTED", X), ("stage0 REG_EXPECTED", S0)):
        for proof, table in data.REG_EXPECTED.items():
            rows += [((name, proof, p, d), key(p, d), c) for (p, d), (_, c) in table.items()]
    rows += [(("REG_CASE_CERTS", p, d), key(p, d), c)
             for (p, d), (_, c) in X.REG_CASE_CERTS.items()]
    rows += [(("REG_CHECKER_ACCEPTS", c["id"]), key(*c["key"]), c["cert"])
             for c in X.REG_CHECKER_ACCEPTS]
    return rows


def reg_side_key_problems(row):
    """REG_SIDE_KEY_RULE: every side the certificate carries is decided on
    exactly with_domain(prop, key.dom). The checker is watched deciding it:
    each call of discharge.verdict made with one of the tree's side
    certificates records the key it was made on. The module attribute is
    restored whatever happens."""
    _, k, spec = row
    cert = cert_of(spec)
    sides, todo = [], [cert["tree"]]
    while todo:
        n = todo.pop()
        sides += list(n["side"])
        todo.extend(n["args"])
    seen, orig = [], DC.verdict

    def spy(k2, c):
        if any(c is sc for _, sc in sides):
            seen.append((c, k2))
        return orig(k2, c)
    DC.verdict = spy
    try:
        tag, why = orig(k, cert)
    finally:
        DC.verdict = orig
    if tag is None:
        return [f"not accepted: {why}"]
    out = []
    for prop, sc in sides:
        want = T.with_domain(prop, k.dom)
        got = [k2 for c, k2 in seen if c is sc]
        if not got:
            out.append(f"side {T.show(prop)} was never decided")
        elif any(g != want for g in got):
            out.append(f"side {T.show(prop)} decided on {[T.show(g) for g in got]}, "
                       f"expected {T.show(want)}")
    return out


def reg_sides_listed_problems():
    """REG_SIDES_LISTED, the sides spelled out once for review, against the
    checker's own derivation from the natural-domain table and C1_EXTRA."""
    out, u = [], T.Var("u")
    for fn, (c0, c1) in X.REG_SIDES_LISTED.items():
        t = T.App(fn, u)
        for k, want in ((0, c0), (1, c1)):
            got = tuple(DC._reg_sides(t, DC._reg_rule(t, None), k))
            if got != tuple(judgement(w) for w in want):
                out.append(f"{fn} at C^{k}: {[T.show(g) for g in got]}, expected {list(want)}")
    return out


def more_must_reject_failures(tables=None):
    """[table, id] for each case of MORE_MUST_REJECT (or of the named
    tables) that fails in full: accepted, or rejected for another reason,
    or its truth or if-emitted outcome other than the data's."""
    return [[t, c["id"]] for t, cases in MORE_MUST_REJECT.items()
            if tables is None or t in tables
            for c in cases if must_reject_problems(c)]


def more_must_reject_verdicts():
    """[table, id] for each MORE_MUST_REJECT case whose certificate the
    checker accepts, or rejects for another reason than REJECT_REASONS
    gives: the verdict alone, apart from the truth and the if-emitted
    outcome, which the search's own certificates decide."""
    out = []
    for t, cases in MORE_MUST_REJECT.items():
        for c in cases:
            got, why = DC.verdict(key(*c["key"]), cert_of(c["cert"]))
            if got is not None or why != REJECT_REASONS[c["id"]]:
                out.append([t, c["id"]])
    return out


def must_reject_accepted():
    """[table, id] for each DISCHARGE_MUST_REJECT case whose certificate the
    checker accepts (none, unless a seam is patched)."""
    return [["DISCHARGE_MUST_REJECT", c["id"]] for c in X.DISCHARGE_MUST_REJECT
            if DC.check(key(*c["key"]), cert_of(c["cert"])) is not None]


# ---------------------------------------------------------------- decided false, undecided

def decided_false_cases():
    """(where, spec message) for every decided-false refusal section 11
    states with its key."""
    rows = []
    dc = X.DISCHARGE_DEFINEDNESS_CASES
    rows += [(f"DISCHARGE_DEFINEDNESS_CASES {i}", c["message"])
             for i, c in dc.items() if "message" in c]
    rows.append(("DISCHARGE_OCCURRENCE_CASE all",
                 X.DISCHARGE_OCCURRENCE_CASE["all"]["message"]))
    rows += [(f"DISCHARGE_BAD_MOVES_CHANGED {i}", c["message"])
             for i, c in DISCHARGE_BAD_MOVES_CHANGED.items()]
    rows += [(f"E56_BAD_MOVES {c['id']}", c["message"]) for c in X.E56_BAD_MOVES
             if c["refusal"] == X.OBLIGATION_DECIDED_FALSE]
    rows += [(f"DISCHARGE_BAD_MOVES_ADDED {c['id']}", c["message"])
             for c in DISCHARGE_BAD_MOVES_ADDED if "message" in c]
    rows += [(f"F3_ROOTS_CASES {c['id']}", c["message"]) for c in X.F3_ROOTS_CASES
             if c["move"][0] == "install"]
    for name, bug in X.DISCHARGE_PLANTED_BUGS.items():
        for proof, (sid, msg) in bug.get("refused", {}).items():
            rows.append((f"DISCHARGE_PLANTED_BUGS {name} {proof} {sid}", msg))
    return rows


def decided_false_problems(spec):
    k = judgement(spec[1]["key"])
    got = outcome(k)
    want = expected_message(spec)
    if got[:2] != ("refused", X.OBLIGATION_DECIDED_FALSE) or got[2] != want:
        return [f"{got[:3]}, expected {want!r}"]
    return []


def undecided_cases():
    rows = []
    for c in DISCHARGE_UNDECIDED:
        for ob in c["goal_emits"]:
            rows.append((c["id"], ob, c["reasons"].get((ob[0], ob[1]))))
    for c in DISCHARGE_BAD_MOVES_ADDED:
        for ob in c.get("goal_emits", ()):
            if ob[3] == X.ADMITTED:
                rows.append((c["id"], ob, c.get("reasons", {}).get((ob[0], ob[1]))))
    return rows


def undecided_problems(row):
    _, ob, reason = row
    got = outcome(key(ob[0], ob[1]))
    return [] if got == ("admitted", ob[4], reason) else [
        f"{got}, expected admitted {ob[4]} {reason!r}"]


def tan_zero_problems():
    """DISCHARGE_DEFINEDNESS_CASES tan_zero_true: cos 0 # 0 is decided by
    step (4), the exact value then norm_num, with no certificate."""
    out = []
    for ob in X.DISCHARGE_DEFINEDNESS_CASES["tan_zero_true"]["goal_emits"]:
        got = outcome(key(ob[0], ob[1]))
        if got != ("discharged", ob[4], None):
            out.append(f"{ob[0]}: {got}, expected discharged {ob[4]}")
    return out


# ---------------------------------------------------------------- the entries

def entries_problems():
    """DISCHARGE_NEW_ENTRIES pinned at their positions (sqrt_zero
    immediately before sqrt_sq, cos_zero after exp_one), SQRT_NONNEG_ENTRY
    after cos_zero, CONSOLIDATION_ENTRIES' six after it (E54), each
    statement, schema and hypotheses as pinned, and EXACT_VALUE_ENTRIES as
    ENTRIES' equations with no schema variable and no hypothesis (none of
    the six is one)."""
    out, names = [], list(ENTRIES)
    for name, e in X.DISCHARGE_NEW_ENTRIES.items():
        got = ENTRIES.get(name)
        if got is None:
            out.append(f"{name} is not in ENTRIES")
            continue
        if got.statement != judgement(e["statement"]) or tuple(got.schema) != e["schema"]:
            out.append(f"{name}: {T.show(got.statement)} {got.schema}")
        if (got.statement.lhs, got.statement.rhs) != (term(e["lhs"]), term(e["rhs"])):
            out.append(f"{name}: sides")
        if tuple(got.hyps) != tuple(judgement(h) for h in e["hyps"]):
            out.append(f"{name}: hyps")
    if "sqrt_zero" in names and names.index("sqrt_zero") + 1 != names.index("sqrt_sq"):
        out.append(f"sqrt_zero is not immediately before sqrt_sq: {names}")
    # cos_zero was appended last (DISCHARGE_NEW_ENTRIES), sqrt_nonneg after
    # it (SQRT_NONNEG_ENTRY, E49), and CONSOLIDATION_ENTRIES after that, in
    # their order (E54): ENTRIES goes from 16 to 17 to 23
    # and atan_zero after them (IMPROPER_E27_CHANGES, E80): 24
    tail = ["cos_zero", "sqrt_nonneg", *X.CONSOLIDATION_ENTRIES,
            *X.IMPROPER_E27_CHANGES["ENTRIES_append"],
            *X.TRIG_NORM_SWITCH["ENTRIES_append"],  # E87: 31
            *X.TAYLOR_ENTRIES_APPEND]  # E103: 32
    if names[-len(tail):] != tail:
        out.append(f"cos_zero, sqrt_nonneg and CONSOLIDATION_ENTRIES are not "
                   f"last, in that order: {names}")
    if len(names) != 32:
        out.append(f"ENTRIES has {len(names)} entries, expected 32")
    for name, e in {**X.SQRT_NONNEG_ENTRY, **X.CONSOLIDATION_ENTRIES}.items():
        got = ENTRIES.get(name)
        if got is None or got.statement != judgement(e["statement"]) \
                or tuple(got.schema) != e["schema"] \
                or tuple(got.hyps) != tuple(judgement(h) for h in e["hyps"]):
            out.append(f"{name}: {got and T.show(got.statement)}")
    exact = {n for n, _ in DC._exact_entries()}
    want = set(X.EXACT_VALUE_ENTRIES) | set(
        X.IMPROPER_E27_CHANGES["EXACT_VALUE_ENTRIES_add"]) | set(
        X.TRIG_NORM_SWITCH["EXACT_VALUE_ENTRIES_add"])
    if exact != want:
        out.append(f"exact values {sorted(exact)}, expected "
                   f"{sorted(want)}")
    return out


# ---------------------------------------------------------------- exact evaluation (the test's own)

class Skip(Exception):
    """Undefined at this point, or not exactly evaluable here."""


def _root(q):
    if q < 0:
        raise Skip
    n, d = math.isqrt(q.numerator), math.isqrt(q.denominator)
    if n * n != q.numerator or d * d != q.denominator:
        raise Skip
    return Fraction(n, d)


# The builtins at the points where this evaluator knows them exactly: the
# exact values' own points, and the zeros of the odd functions.
_EXACT_APPS = {("sin", 0): 0, ("cos", 0): 1, ("exp", 0): 1, ("ln", 1): 0,
               ("atan", 0): 0, ("tan", 0): 0}


def ev(t, env):
    """t's exact value at env (names to Fractions), with Fractions only; it
    shares no code with field.py or the kernel."""
    k = type(t)
    if k is T.Num:
        return Fraction(t.n)
    if k in (T.Var, T.Const):
        if t.name not in env:
            raise Skip
        return env[t.name]
    if k is T.Neg:
        return -ev(t.a, env)
    if k is T.Add:
        return ev(t.a, env) + ev(t.b, env)
    if k is T.Mul:
        return ev(t.a, env) * ev(t.b, env)
    if k is T.Div:
        d = ev(t.b, env)
        if d == 0:
            raise Skip
        return ev(t.a, env) / d
    if k is T.Pow:
        b = ev(t.base, env)
        if b == 0 and t.n < 0:
            raise Skip
        return b ** t.n
    if k is T.App:
        q = ev(t.arg, env)
        if t.fn == "sqrt":
            return _root(q)
        if t.fn == "ln" and q <= 0:
            raise Skip
        if (t.fn, q) in _EXACT_APPS:
            return Fraction(_EXACT_APPS[(t.fn, q)])
    raise Skip


_OPS = {">": lambda d: d > 0, ">=": lambda d: d >= 0, "<": lambda d: d < 0,
        "<=": lambda d: d <= 0, "==": lambda d: d == 0}


def holds(j, env):
    if type(j) is T.NonZero:
        return ev(j.e, env) != 0
    return _OPS[j.op](ev(j.lhs, env) - ev(j.rhs, env))


def in_domain(dom, env):
    for item in dom:
        if type(item) is T.Interval:
            v = env[item.var]
            if isinstance(item.lo, T.Term):
                lo = ev(item.lo, env)
                if v < lo or (v == lo and not item.lo_closed):
                    return False
            if isinstance(item.hi, T.Term):
                hi = ev(item.hi, env)
                if v > hi or (v == hi and not item.hi_closed):
                    return False
        elif not holds(item, env):
            return False
    return True


# A second, independent reading for refutations and for the spec's truth
# points: the math module, with the real pi and e, at a 1e-9 margin.
_MATH = {"sin": math.sin, "cos": math.cos, "tan": math.tan, "exp": math.exp,
         "ln": math.log, "sqrt": math.sqrt, "atan": math.atan,
         "asin": math.asin, "acos": math.acos, "abs": abs, "sinh": math.sinh,
         "cosh": math.cosh, "tanh": math.tanh, "asinh": math.asinh,
         "acosh": math.acosh, "atanh": math.atanh}
MARGIN = 1e-9


def fev(t, env):
    k = type(t)
    try:
        if k is T.Num:
            return float(t.n)
        if k is T.Const:
            return {"pi": math.pi, "e_const": math.e}[t.name]
        if k is T.Var:
            return float(env[t.name])
        if k is T.Neg:
            return -fev(t.a, env)
        if k is T.Add:
            return fev(t.a, env) + fev(t.b, env)
        if k is T.Mul:
            return fev(t.a, env) * fev(t.b, env)
        if k is T.Div:
            return fev(t.a, env) / fev(t.b, env)
        if k is T.Pow:
            return fev(t.base, env) ** t.n
        if k is T.App:
            r = _MATH[t.fn](fev(t.arg, env))
            if t.fn == "exp" and r == 0.0:  # underflow: exp is never 0 (E103)
                raise Skip
            return r
    except (ValueError, ZeroDivisionError, KeyError, OverflowError):
        raise Skip from None
    raise Skip


def float_holds(j, env):
    """j's truth at env in floats; an equality within MARGIN of the
    boundary reads as the boundary itself. A strict or # 0 judgement whose
    difference is nonzero but within MARGIN is not decided by floats (Skip):
    exp(-24) > 0 is true, and reading it as the boundary would call it
    false (p1_expected E103, which made exp's positivity citable)."""
    d = fev(j.e, env) if type(j) is T.NonZero else fev(j.lhs, env) - fev(j.rhs, env)
    if abs(d) <= MARGIN:
        if d != 0 and (type(j) is T.NonZero or j.op in ("<", ">")):
            raise Skip
        d = 0.0
    return d != 0 if type(j) is T.NonZero else _OPS[j.op](d)


def judge_at(k, env):
    """(in the domain, proposition holds) at env, the real pi and e: exact
    when the terms allow it, else the math module's reading."""
    prop = replace(k, dom=())
    try:
        return in_domain(k.dom, env), holds(prop, env)
    except Skip:
        pass
    ok = True
    for item in k.dom:
        if type(item) is T.Interval:
            v = float(env[item.var])
            for end, closed, below in ((item.lo, item.lo_closed, True),
                                       (item.hi, item.hi_closed, False)):
                if isinstance(end, T.Term):
                    e = fev(end, env)
                    d = (v - e) if below else (e - v)
                    ok &= d > MARGIN or (closed and abs(d) <= MARGIN)
        else:
            ok &= float_holds(item, env)
    return ok, float_holds(prop, env)


# ---------------------------------------------------------------- the property test

SEED = 20260924
PER_CERT = 20      # points sampled per accepted certificate
MIN_ACCEPTED, MIN_POINTS, MIN_REFUTED = 50, 1000, 50
CHECKERS = ("reg", "farkas", "hyp", "sign", "sign product", "sign node", "cite",
            "norm_num", "dispatcher")
XV, YV = T.Var("x"), T.Var("y")


def _q(rng, n=6, d=4):
    return Fraction(rng.randint(-n, n), rng.randint(1, d))


def _inside(rng, lo, hi):
    """A rational strictly inside (lo, hi), denominator up to 12 in the
    step."""
    d = rng.randint(1, 12)
    return lo + (hi - lo) * Fraction(rng.randint(1, 2 * d - 1), 2 * d)


def _constants(rng):
    """pi > 0 and e_const > 1 as random rationals: the Farkas, sign and
    product checkers know nothing of either beyond pi_pos and e_gt_one."""
    return {"pi": Fraction(rng.randint(1, 96), rng.randint(1, 12)),
            "e_const": 1 + Fraction(rng.randint(1, 60), rng.randint(1, 12))}


def points(rng, k, n, targets=()):
    """Up to n points of k's domain: each variable at a closed end of its
    Interval with probability 1/4 per end, else strictly inside it (a window
    of 5 past an infinite end, [-4, 4] for a variable with no Interval);
    with targets, half the time one of them."""
    ivs = {it.var: it for it in k.dom if type(it) is T.Interval}
    names = sorted(T.fv(k))
    out, tries = [], 0
    while len(out) < n and tries < 8 * n:
        tries += 1
        env = _constants(rng)
        if targets and rng.random() < 0.5:
            env.update(rng.choice(targets))
        try:
            for v in names:
                if v not in env:
                    env[v] = _coordinate(rng, ivs.get(v), env)
            if in_domain(k.dom, env):
                out.append(env)
        except Skip:
            continue
    return out


def _coordinate(rng, iv, env):
    if iv is None:
        return _inside(rng, Fraction(-4), Fraction(4))
    lo = ev(iv.lo, env) if isinstance(iv.lo, T.Term) else None
    hi = ev(iv.hi, env) if isinstance(iv.hi, T.Term) else None
    if lo is not None and iv.lo_closed and rng.random() < 0.25:
        return lo
    if hi is not None and iv.hi_closed and rng.random() < 0.25:
        return hi
    lo = hi - 5 if lo is None else lo
    hi = lo + 5 if hi is None else hi
    return _inside(rng, lo, hi) if lo < hi else lo


class Stats:
    def __init__(self):
        self.accepted = self.evaluated = self.skipped = 0
        self.violations = []


def _record(stats, k, cert, rng, targets=()):
    stats.accepted += 1
    prop = replace(k, dom=())
    for env in points(rng, k, PER_CERT, targets):
        try:
            ok = holds(prop, env)
        except Skip:
            stats.skipped += 1
            continue
        stats.evaluated += 1
        if not ok:
            stats.violations.append(f"{T.show(k)} accepted with {cert!r} is "
                                    f"false at {env}")
            return


def _lit_sum(pairs):
    """The term sum of c * t over (c, t) pairs, t None for a constant."""
    out = None
    for c, t in pairs:
        if c == 0:
            continue
        u = T.lit(c) if t is None else (t if c == 1 else T.Mul(T.lit(c), t))
        out = u if out is None else T.Add(out, u)
    return T.Num(0) if out is None else out


def _rel(rng, g, strict):
    """The proposition g > 0 (or >= 0) written one of four ways."""
    op = ">" if strict else ">="
    r = rng.random()
    if r < 0.5:
        return T.Rel(op, g, T.Num(0))
    if r < 0.75:
        return T.Rel("<" if strict else "<=", T.Num(0), g)
    return T.Rel("<" if strict else "<=", T.Neg(g), T.Num(0))


def _interval(rng, var="x", const=None):
    """A random Interval on var with rational ends lo < hi, each open or
    closed, one end infinite with probability 1/8; with a constant, the
    upper end may be hi times it. Returns it and its rational ends (None
    for an infinite one)."""
    lo, hi = _q(rng), _q(rng)
    while lo == hi:
        hi = _q(rng)
    lo, hi = min(lo, hi), max(lo, hi)
    lt, ht = T.lit(lo), T.lit(hi)
    if const and hi > 0 and rng.random() < 0.5:
        ht = T.Mul(T.lit(hi), T.Const(const))
    lc, hc = rng.random() < 0.5, rng.random() < 0.5
    if rng.random() < 1 / 8:
        if rng.random() < 0.5:
            return T.Interval(var, T.NEG_INF, False, ht, hc), (None, hi)
        return T.Interval(var, lt, lc, T.POS_INF, False), (lo, None)
    return T.Interval(var, lt, lc, ht, hc), (lo, hi)


def _gamma(rng, names, n):
    items = []
    for _ in range(n):
        v = T.Var(rng.choice(names))
        c = T.lit(_q(rng, 3, 2))
        op = rng.choice(("<", "<=", ">", ">="))
        items.append(T.Rel(op, v, c) if rng.random() < 0.7 else T.Rel(op, c, v))
    return tuple(items)


def _key(prop, dom):
    return T.with_domain(prop, dom)


# -- (c) Farkas: every sign pattern the checker's own constraint set allows

def _solve(rows, rhs):
    """A solution of rows * lam = rhs over the rationals, free unknowns set
    to 1, or None."""
    n = len(rows[0]) if rows else 0
    m = [list(r) + [b] for r, b in zip(rows, rhs)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        m[r] = [x / m[r][c] for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    if any(all(x == 0 for x in row[:-1]) and row[-1] != 0 for row in m):
        return None
    lam = [Fraction(1)] * n
    for i, c in enumerate(piv):
        lam[c] = m[i][-1] - sum(m[i][j] * lam[j] for j in range(n)
                                if j != c and j not in piv)
    return lam


def farkas_candidates(k):
    """Certificates solving the combination exactly over each subset of the
    checker's own constraint set (discharge._constraint_set), multipliers of
    either sign: an accept can only come from a sound combination, and a
    mutated set or rule shows as an accepted false key."""
    out = []
    for sense in ((">", "<") if type(k) is T.NonZero else (None,)):
        try:
            cs = DC._constraint_set(k, sense)
            labels = list(cs)
            polys = FD.ring_polys([t for lab in labels for t in cs[lab][:2]])[0]
        except (DC._Reject, T.Refused):
            continue
        h = {lab: P.sub(polys[2 * i], polys[2 * i + 1]) for i, lab in enumerate(labels)}
        others = [lab for lab in labels if lab != GOAL]
        for n in range(len(others) + 1):
            for sub in itertools.combinations(others, n):
                mons = sorted({m for lab in (GOAL, *sub) for m in h[lab]
                               if m != P.ONE_MONO})
                rows = [[h[lab].get(m, 0) for lab in sub] for m in mons]
                lam = _solve(rows, [-h[GOAL].get(m, 0) for m in mons]) if sub else (
                    [] if not mons else None)
                if lam is None:
                    continue
                mults = {GOAL: Fraction(1), **{lab: q for lab, q in zip(sub, lam) if q}}
                out.append({"method": "farkas", "sense": sense, "multipliers": mults})
    return out


# -- (b) one field mutated

def mutate(rng, cert):
    """The certificate with one field changed at random, or None."""
    c = copy.deepcopy(cert)
    m = c["method"]
    if m == "farkas":
        ms = c["multipliers"]
        lab = rng.choice(list(ms))
        r = rng.random()
        if r < 0.3:
            ms[lab] = -ms[lab]
        elif r < 0.5:
            ms[lab] = ms[lab] * rng.choice((2, Fraction(1, 2), 3))
        elif r < 0.7 and lab[0] == "dom":
            del ms[lab]
            ms[("dom", lab[1], {"lo": "hi", "hi": "lo", "rel": "lo"}[lab[2]])] = Fraction(1)
        elif r < 0.85:
            del ms[lab]
            if not ms:
                return None
        else:
            c["sense"] = {">": "<", "<": ">", None: ">"}[c["sense"]]
    elif m == "hyp":
        if "member" in c:
            c["member"] += rng.choice((-1, 1))
        else:
            ch = list(c["chain"])
            rng.shuffle(ch)
            c["chain"] = tuple(ch[: rng.randint(1, len(ch))])
    elif m == "sign":
        r = rng.random()
        if r < 0.3 or not c["squares"]:
            c["const"] = c["const"] + rng.choice((-1, 1, Fraction(-1, 2)))
        else:
            sq = list(c["squares"])
            i = rng.randrange(len(sq))
            a, s, kk = sq[i]
            sq[i] = ((-a, s, kk) if r < 0.55 else (a, s, kk + 1) if r < 0.75
                     else (a, T.Add(s, T.lit(rng.choice((1, -1)))), kk))
            c["squares"] = tuple(sq)
    elif m == "sign product":
        fs = list(c["factors"])
        r = rng.random()
        if r < 0.35 and fs:
            i = rng.randrange(len(fs))
            f, rel, cc = fs[i]
            # the sign flipped, or (E53) the strictness toggled
            flip = ({">": "<", "<": ">", ">=": "<=", "<=": ">=", "# 0": "# 0"}
                    if rng.random() < 0.6 else
                    {">": ">=", ">=": ">", "<": "<=", "<=": "<", "# 0": "# 0"})
            fs[i] = (f, flip[rel], cc)
        elif r < 0.6:
            c["content"] = -c["content"]
        elif r < 0.8 and fs:
            i = rng.randrange(len(fs))
            f, rel, cc = fs[i]
            fs[i] = (T.Add(f, T.lit(rng.choice((1, -1)))), rel, cc)
        elif fs:
            i = rng.randrange(len(fs))
            f, rel, cc = fs[i]
            child = mutate(rng, cc)
            if child is None:
                return None
            fs[i] = (f, rel, child)
        c["factors"] = tuple(fs)
    elif m == "sign node":
        ps = list(c["parts"])
        r = rng.random()
        if not ps or r < 0.15:
            ps = [(rng.choice(tuple(DC.SIGN_SETS)), {"method": "norm_num"})]
        elif r < 0.6:
            i = rng.randrange(len(ps))
            rl, cc = ps[i]
            # the sign flipped, or the strictness toggled
            flip = ({">": "<", "<": ">", ">=": "<=", "<=": ">=", "# 0": "# 0"}
                    if rng.random() < 0.6 else
                    {">": ">=", ">=": ">", "<": "<=", "<=": "<", "# 0": ">"})
            ps[i] = (flip[rl], cc)
        elif r < 0.75:
            ps.pop(rng.randrange(len(ps)))
        else:
            i = rng.randrange(len(ps))
            rl, cc = ps[i]
            child = mutate(rng, cc)
            if child is None:
                return None
            ps[i] = (rl, child)
        c["parts"] = tuple(ps)
    elif m == "cite":
        r = rng.random()
        if r < 0.3 and c["inst"]:
            v = rng.choice(list(c["inst"]))
            c["inst"][v] = T.Add(c["inst"][v], T.Num(1))
        elif r < 0.5:
            c["entry"] = rng.choice(list(ENTRIES))
        elif r < 0.7:
            c["hyps"] = ()
        elif c["hyps"]:
            p, cc = c["hyps"][0]
            child = mutate(rng, cc)
            if child is None:
                return None
            c["hyps"] = ((p, child),) + c["hyps"][1:]
        else:
            return None
    else:
        return None
    return c


# -- the families of keys, one per checker

def _farkas_key(rng):
    """A key over one Interval and Γ relations: half built true, as a
    positive combination of the domain's own constraints plus slack; half
    random, of degree up to 3."""
    names = ["x"] if rng.random() < 0.6 else ["x", "y"]
    const = rng.choice(("pi", "e_const")) if rng.random() < 1 / 8 else None
    iv, _ = _interval(rng, "x", const)
    dom = _gamma(rng, names, rng.randint(0, 2)) + (iv,)
    if rng.random() < 0.5:
        # The domain's own constraints, read from a key on this domain.
        own = DC._constraint_set(_key(T.Rel(">", XV, T.Num(0)), dom), None)
        parts = [(Fraction(rng.randint(1, 3), rng.randint(1, 2)), T.Add(x, T.Neg(y)))
                 for lab, (x, y, _) in own.items()
                 if lab != GOAL and rng.random() < 0.6]
        slack = Fraction(rng.randint(0, 2), rng.randint(1, 3))
        g = _lit_sum(parts + [(slack, None)])
        if const and rng.random() < 0.5:
            g = T.Add(g, T.Mul(T.lit(Fraction(rng.randint(1, 2))), T.Const(const)))
        strict = rng.random() < 0.5
    else:
        mons = [(_q(rng), XV), (_q(rng), None)]
        if "y" in names:
            mons.append((_q(rng), YV))
        if rng.random() < 0.25:
            mons.append((_q(rng), T.Pow(XV, rng.randint(2, 3))))
        g, strict = _lit_sum(mons), rng.random() < 0.5
    prop = T.NonZero(g) if rng.random() < 0.2 else _rel(rng, g, strict)
    return _key(prop, dom), ()


def _sqrt_key(rng):
    """E49's family: c0 + c1*sqrt(p) REL 0 for a linear p over an Interval,
    with the points where p is a rational square as targets, p's root among
    them, so that sqrt p is evaluated exactly (others are skipped and
    counted)."""
    iv, (lo, hi) = _interval(rng)
    a, b, p = _linear(rng, lo, hi, root_at_end=rng.random() < 0.5)
    g = _lit_sum([(Fraction(rng.randint(-2, 3), rng.randint(1, 2)), None),
                  (Fraction(rng.choice((1, 2, -1)), rng.randint(1, 2)),
                   T.App("sqrt", p))])
    strict = rng.random() < 0.5
    prop = T.NonZero(g) if rng.random() < 0.25 else _rel(rng, g, strict)
    targets = [{"x": (Fraction(n, d) ** 2 - b) / a}
               for n, d in ((rng.randint(0, 12), rng.randint(1, 6)) for _ in range(8))]
    # p's root always among them: there sqrt p = 0, where a label read as
    # strict (sqrt p > 0) is false
    return _key(prop, (iv,)), targets + [{"x": -b / a}]


def _cos_key(rng):
    """ATOM_FACT_RULE's cos family (E54): c0 + c1*cos(p) REL 0 for a linear
    p over an Interval, near the bounds 1 - cos p >= 0 and cos p + 1 >= 0,
    with the root of p as the target, where cos p = cos 0 = 1 is exact
    (cos_zero); every other point is skipped and counted."""
    iv, (lo, hi) = _interval(rng)
    a, b, p = _linear(rng, lo, hi, root_at_end=rng.random() < 0.5)
    c1 = Fraction(rng.choice((1, -1, 2, -2, Fraction(1, 2))))
    c0 = abs(c1) * Fraction(rng.choice((-2, -1, -1, 0, 1, 1, 2)), rng.choice((1, 1, 2)))
    g = _lit_sum([(c0, None), (c1, T.App("cos", p))])
    strict = rng.random() < 0.5
    prop = T.NonZero(g) if rng.random() < 0.2 else _rel(rng, g, strict)
    return _key(prop, (iv,)), [{"x": -b / a}]


def _root_key(rng):
    """A false univariate key with a rational root strictly inside its
    range (E50): (x - r) * (a x + b) # 0, or x - r # 0, over an Interval
    around r whose ends and midpoint are not r."""
    r = Fraction(rng.randint(-20, 20), rng.randint(2, 7))
    lo = r - Fraction(rng.randint(1, 5), rng.randint(1, 3))
    hi = r + Fraction(rng.randint(1, 5), rng.randint(1, 3))
    f = T.Add(XV, T.Neg(T.lit(r)))
    if rng.random() < 0.5:
        f = T.Mul(f, T.Add(T.Mul(T.lit(Fraction(rng.randint(1, 3))), XV),
                           T.lit(Fraction(rng.randint(-5, 5)))))
    iv = T.Interval("x", T.lit(lo), rng.random() < 0.5, T.lit(hi), rng.random() < 0.5)
    return _key(T.NonZero(f), (iv,))


def _hyp_key(rng):
    """Γ relations sharing constants, so that chains exist, and a
    proposition that is an item, a # 0 of one, a chain's ends, or a random
    ordering among the same terms."""
    c = [T.lit(_q(rng, 3, 1)) for _ in range(2)]
    pool = [XV, YV, T.Num(0)] + c
    items = []
    for _ in range(rng.randint(1, 3)):
        a, b = rng.sample(pool, 2)
        items.append(T.Rel(rng.choice(("<", "<=", ">", ">=")), a, b))
    iv, _ = _interval(rng)
    dom = tuple(items) + ((iv,) if rng.random() < 0.5 else ())
    r = rng.random()
    if r < 0.3:
        prop = rng.choice(items)
    elif r < 0.45:
        prop = T.NonZero(rng.choice(pool))
    else:
        a, b = rng.sample(pool, 2)
        prop = T.Rel(rng.choice(("<", "<=", ">", ">=")), a, b)
    return _key(prop, dom), ()


def _hyp_random(rng, k):
    n = len(k.dom)
    if not n:
        return []
    return [{"method": "hyp", "member": rng.randrange(n)},
            {"method": "hyp", "chain": tuple(rng.randrange(n)
                                             for _ in range(rng.randint(1, 3)))}]


def _linear(rng, lo, hi, root_at_end=False):
    """a*x + b with its root at an end of [lo, hi], or anywhere."""
    a = Fraction(rng.choice((1, -1, 2, -2, Fraction(1, 2))))
    r = rng.choice([e for e in (lo, hi) if e is not None] or [Fraction(0)]) \
        if root_at_end else _q(rng)
    return a, -a * r, T.Add(T.Mul(T.lit(a), XV), T.lit(-a * r)) if r else T.Mul(T.lit(a), XV)


def _sign_key(rng):
    """A key built from a sign certificate c0 + sum c*s^k, written as that
    sum or as its expanded ring normal form, with c0 sometimes negative."""
    iv, (lo, hi) = _interval(rng)
    squares = []
    for _ in range(rng.randint(1, 2)):
        _, _, s = _linear(rng, lo, hi, root_at_end=rng.random() < 0.5)
        squares.append((Fraction(rng.randint(1, 3), rng.randint(1, 2)), s,
                        rng.choice((2, 2, 4))))
    if rng.random() < 0.25:  # a term no sign certificate may hold
        c, s, kk = squares[0]
        squares[0] = (-c, s, kk) if rng.random() < 0.5 else (c, s, rng.choice((1, 3)))
    c0 = rng.choice((Fraction(0), Fraction(0), Fraction(rng.randint(1, 3), 2),
                     Fraction(-rng.randint(1, 3), 4)))
    total = T.lit(c0)
    for c, s, kk in squares:
        total = T.Add(total, T.Mul(T.lit(c), T.Pow(s, kk)))
    if rng.random() < 0.5:
        (p,), atoms = FD.ring_polys([total])
        total = residual.poly_term(p, atoms)
    strict = rng.random() < 0.5
    nonzero = rng.random() < 0.2
    prop = T.NonZero(total) if nonzero else T.Rel(">" if strict else ">=", total, T.Num(0))
    cert = {"method": "sign", "sense": ">" if nonzero else None, "const": c0,
            "squares": tuple(squares)}
    return _key(prop, (iv,)), (cert,)


def _product_key(rng):
    """A key built from a product c * f1 * ... * fn of linear factors whose
    roots lie outside the Interval or at an end, with each factor's sign
    taken at the Interval's middle and its certificate from the search. A
    factor whose root is a closed end is 0 there, so its relation is
    non-strict, and the key is then non-strict (E53), except one time in
    four, when the key is strict and false at that end, which only a
    checker that allows a non-strict factor under a strict target accepts;
    a non-strict key's strict factors are sometimes written non-strict."""
    lo, hi = _q(rng), _q(rng)
    while lo == hi:
        hi = _q(rng)
    lo, hi = min(lo, hi), max(lo, hi)
    lc, hc = rng.random() < 0.5, rng.random() < 0.5
    iv = T.Interval("x", T.lit(lo), lc, T.lit(hi), hc)
    dom, mid = (iv,), (lo + hi) / 2
    factors, sign, zero_at_end = [], 1, False
    for _ in range(rng.randint(1, 3)):
        a = Fraction(rng.choice((1, -1, 2)))
        r = rng.choice((lo, hi, lo - rng.randint(1, 3), hi + rng.randint(1, 3)))
        f = T.Add(T.Mul(T.lit(a), XV), T.lit(-a * r))
        s = 1 if a * (mid - r) > 0 else -1
        sign *= s
        zero = (r == lo and lc) or (r == hi and hc)
        zero_at_end |= zero
        factors.append((f, s, zero))
    c = Fraction(rng.choice((1, -1, 2, Fraction(-1, 3))))
    total = T.lit(c)
    for f, _, _ in factors:
        total = T.Mul(total, f)
    if rng.random() < 0.3:
        (p,), atoms = FD.ring_polys([total])
        total = residual.poly_term(p, atoms)
    r = rng.random()
    if r < 0.3:
        prop, sense, content, rels = T.NonZero(total), "#", c, ["# 0"] * len(factors)
    else:
        # The key states total's true sign, except one time in four, when
        # its certificate's parity is then wrong while every child holds.
        positive = ((c > 0) == (sign > 0)) != (rng.random() < 0.25)
        strict = not zero_at_end if rng.random() < 0.75 else zero_at_end
        if not zero_at_end and rng.random() < 0.3:
            strict = False
        op = (">" if positive else "<") if strict else (">=" if positive else "<=")
        prop = T.Rel(op, total, T.Num(0))
        sense, content = None, c if positive else -c
        rels = [(">" if s > 0 else "<") + ("=" if zero or (not strict and rng.random() < 0.3)
                                          else "")
                for _, s, zero in factors]
    cfs = []
    for (f, _, _), rel in zip(factors, rels):
        child = T.NonZero(f) if rel == "# 0" else T.Rel(rel, f, T.Num(0))
        cc = SR.propose(_key(child, dom))
        if cc is None:
            cc = {"method": "farkas", "sense": ">" if rel == "# 0" else None,
                  "multipliers": {GOAL: Fraction(1), ("dom", 0, "lo"): Fraction(1)}}
        cfs.append((f, rel, cc))
    cert = {"method": "sign product", "sense": sense, "content": content,
            "factors": tuple(cfs)}
    return _key(prop, dom), (cert,)


def _node_key(rng):
    """A key g r 0 over one of E82's node shapes, built from linear factors
    whose roots lie outside the Interval or at an end: a quotient f1/f2
    (f2's root never a closed end), a negated quotient, a sum of two like-
    signed factors, a square plus a constant, or an even power alone (no
    parts). Each part's relation is its factor's sign at the Interval's
    middle, non-strict where it is 0 at a closed end, with its certificate
    from the search. One key in four states the wrong sign, which only a
    checker that skips E82's parity accepts."""
    lo, hi = _q(rng), _q(rng)
    while lo == hi:
        hi = _q(rng)
    lo, hi = min(lo, hi), max(lo, hi)
    lc, hc = rng.random() < 0.5, rng.random() < 0.5
    dom, mid = (T.Interval("x", T.lit(lo), lc, T.lit(hi), hc),), (lo + hi) / 2

    def factor(may_vanish=True):
        a = Fraction(rng.choice((1, -1, 2)))
        ends = (lo, hi) if may_vanish else ()
        r = rng.choice(ends + (lo - rng.randint(1, 3), hi + rng.randint(1, 3)))
        f = T.Add(T.Mul(T.lit(a), XV), T.lit(-a * r))
        zero = (r == lo and lc) or (r == hi and hc)
        return f, (1 if a * (mid - r) > 0 else -1), zero

    def rel(s, zero):
        return (">" if s > 0 else "<") + ("=" if zero else "")

    shape = rng.choice(("div", "neg", "add", "sq", "pow"))
    if shape in ("div", "neg"):
        (f1, s1, z1), (f2, s2, _) = factor(), factor(may_vanish=False)
        g, kids = T.Div(f1, f2), [(f1, rel(s1, z1)), (f2, rel(s2, False))]
        sign, zero = s1 * s2, z1
        if shape == "neg":
            g, kids, sign = T.Neg(g), [(g, rel(sign, zero))], -sign
    elif shape == "add":
        (f1, s1, z1), (f2, s2, z2) = factor(), factor()
        if s1 != s2:
            f2, s2 = T.Neg(f2), s1
        g, kids = T.Add(f1, f2), [(f1, rel(s1, z1)), (f2, rel(s2, z2))]
        sign, zero = s1, z1 and z2
    elif shape == "sq":
        (f1, s1, z1), c = factor(), Fraction(rng.choice((1, 2, Fraction(1, 3))))
        sq = T.Pow(f1, 2)
        g, kids = T.Add(sq, T.lit(c)), [(sq, ">="), (T.lit(c), ">")]
        sign, zero = 1, False
    else:
        f1, _, _ = factor()
        g, kids, sign, zero = T.Pow(f1, 2), [], 1, True
    if rng.random() < 0.25:
        sign = -sign  # the wrong sign: the parts still hold
    r = rng.random()
    if r < 0.2 and not zero:
        prop = T.NonZero(g)
    else:
        strict = not zero if rng.random() < 0.75 else zero
        prop = T.Rel((">" if sign > 0 else "<") + ("" if strict else "="),
                     g, T.Num(0))
    parts = []
    for f, rl in kids:
        cc = SR.propose(_key(T.Rel(rl, f, T.Num(0)), dom))
        if cc is None:
            cc = {"method": "norm_num"}
        parts.append((rl, cc))
    cert = {"method": "sign node", "parts": tuple(parts)}
    return _key(prop, dom), (cert,)


def _cite_key(rng):
    """sqrt(p) # 0, > 0 or >= 0 for a linear p, cited by sqrt_pos with its
    hypothesis p > 0 by the search; or a sign fact's own constant. The
    targets are points where p is a rational square, so that sqrt p is
    exact."""
    if rng.random() < 0.25:
        name = rng.choice(("pi_pos", "e_gt_one"))
        const = T.Const("pi" if name == "pi_pos" else "e_const")
        props = ([T.NonZero(const), T.Rel(">", const, T.Num(0)),
                  T.Rel(">=", const, T.Num(0)), T.Rel("<=", T.Num(0), const)]
                 if name == "pi_pos" else [T.Rel(">", const, T.Num(1))])
        prop = rng.choice(props)
        cert = {"method": "cite", "entry": name, "inst": {}, "hyps": ()}
        return _key(prop, ()), (cert,), ()
    iv, (lo, hi) = _interval(rng)
    a, b, p = _linear(rng, lo, hi, root_at_end=rng.random() < 0.3)
    s = T.App("sqrt", p)
    prop = rng.choice((T.NonZero(s), T.Rel(">", s, T.Num(0)), T.Rel(">=", s, T.Num(0)),
                       T.Rel("<=", T.Num(0), s), T.Rel("<", T.Num(0), s)))
    dom = (iv,)
    hyp = T.Rel(">", p, T.Num(0))
    child = SR.propose(_key(hyp, dom)) or {
        "method": "farkas", "sense": None,
        "multipliers": {GOAL: Fraction(1), ("dom", 0, "lo"): Fraction(1)}}
    cert = {"method": "cite", "entry": "sqrt_pos", "inst": {"a": p},
            "hyps": ((hyp, child),)}
    targets = [{"x": (Fraction(n, d) ** 2 - b) / a}
               for n, d in ((rng.randint(0, 12), rng.randint(1, 6)) for _ in range(8))]
    return _key(prop, dom), (cert,), targets


def _literal_key(rng):
    def lit_term():
        a, b = T.lit(_q(rng, 9, 4)), T.lit(_q(rng, 9, 4))
        return rng.choice((a, T.Add(a, b), T.Mul(a, b), T.Pow(a, rng.randint(0, 3)),
                           T.Div(a, b) if FD.rational_value(b) else a))
    if rng.random() < 0.25:
        return _key(T.NonZero(lit_term()), ())
    return _key(T.Rel(rng.choice(("<", "<=", ">", ">=")), lit_term(), lit_term()), ())


_EXACT_TERMS = (
    lambda g: T.Add(g, T.App("sin", T.Add(XV, T.Neg(XV)))),
    lambda g: T.Mul(g, T.App("cos", T.Num(0))),
    lambda g: T.Add(g, T.App("ln", T.Num(1))),
    lambda g: T.Mul(T.App("exp", T.Mul(T.Num(0), XV)), g),
    lambda g: T.Add(T.App("sqrt", T.Num(0)), g),
)


def _dispatcher_key(rng):
    """A Farkas key with exact values at rational points written into its
    proposition, which only the dispatcher's rewrite (E31) removes."""
    k, _ = _farkas_key(rng)
    prop = replace(k, dom=())
    inject = rng.choice(_EXACT_TERMS)
    if type(prop) is T.NonZero:
        prop = T.NonZero(inject(prop.e))
    else:
        prop = replace(prop, lhs=inject(prop.lhs))
    return _key(prop, k.dom), ()


# -- the 'reg' family (REG_PROPERTY_TEST)

_REG_BUILTINS = ("ln", "sqrt", "tan", "asin", "acos", "acosh", "atanh", "sin",
                 "cos", "atan", "exp", "abs", "sinh", "cosh", "tanh", "asinh")


def _reg_term(rng, depth):
    """A random term over x from REG_RULES' node kinds: literals, x, neg,
    add, mul, div, pow with n in -2..3, and the sixteen builtins."""
    if depth <= 0 or rng.random() < 0.3:
        return XV if rng.random() < 0.6 else T.lit(_q(rng, 4, 2))
    r = rng.random()
    if r < 0.1:
        return T.Neg(_reg_term(rng, depth - 1))
    if r < 0.3:
        return T.Add(_reg_term(rng, depth - 1), _reg_term(rng, depth - 1))
    if r < 0.45:
        return T.Mul(_reg_term(rng, depth - 1), _reg_term(rng, depth - 1))
    if r < 0.55:
        return T.Div(_reg_term(rng, depth - 1), _reg_term(rng, depth - 1))
    if r < 0.65:
        return T.Pow(_reg_term(rng, depth - 1), rng.choice((-2, -1, 0, 1, 2, 3)))
    return T.App(rng.choice(_REG_BUILTINS), _reg_term(rng, depth - 1))


def _reg_key(rng):
    lo, hi = _q(rng), _q(rng)
    while lo == hi:
        hi = _q(rng)
    lo, hi = min(lo, hi), max(lo, hi)
    iv = T.Interval("x", T.lit(lo), rng.random() < 0.5, T.lit(hi), rng.random() < 0.5)
    return T.Reg(_reg_term(rng, rng.randint(1, 4)), rng.choice((0, 1)), (iv,)), (lo, hi, iv)


def _reg_tree_sides(tree):
    out, todo = [], [tree]
    while todo:
        n = todo.pop()
        out += [p for p, _ in n["side"]]
        todo.extend(reversed(n["args"]))
    return out


def _reg_points(rng, lo, hi, iv):
    """The interval's rational points: its closed ends, its midpoint and 16
    more inside, and a point a margin inside each open end."""
    pts = [(lo + hi) / 2] + [_inside(rng, lo, hi) for _ in range(16)]
    pts += [e for e, closed in ((lo, iv.lo_closed), (hi, iv.hi_closed)) if closed]
    eps = Fraction(1, 10 ** 6) * (hi - lo)
    pts += [lo + eps, hi - eps]
    return pts


def _side_holds(prop, env):
    try:
        return holds(prop, env)
    except Skip:
        pass
    try:
        return float_holds(prop, env)
    except Skip:
        return True  # not evaluable at this point by either reading


def _reg_mutants(rng, cert, dom):
    """The accepted certificate's three mutations REG_PROPERTY_TEST names, and
    a side certificate replaced by the norm_num leaf where the side is not
    closed: each must be rejected."""
    out = []
    nodes, todo = [], [cert["tree"]]
    while todo:
        n = todo.pop()
        nodes.append(n)
        todo.extend(n["args"])

    def rebuilt(target, fn):
        def walk(n):
            if n is target:
                return fn(n)
            return {**n, "args": tuple(walk(a) for a in n["args"])}
        return {"method": "reg", "tree": walk(cert["tree"])}
    with_sides = [n for n in nodes if n["side"]]
    if with_sides:
        n = rng.choice(with_sides)
        out.append(rebuilt(n, lambda m: {**m, "side": m["side"][:-1]}))
        strict = [i for i, (p, _) in enumerate(n["side"])
                  if type(p) is T.Rel and p.op in (">", "<")]
        if strict:
            i = rng.choice(strict)
            p, c = n["side"][i]
            weak = T.Rel(p.op + "=", p.lhs, p.rhs)
            out.append(rebuilt(n, lambda m: {**m, "side": m["side"][:i] + ((weak, c),)
                                                   + m["side"][i + 1:]}))
        open_sides = [i for i, (p, _) in enumerate(n["side"])  # the leaf fails there
                      if DC.check(T.with_domain(p, dom), {"method": "norm_num"}) is None]
        if open_sides:
            i = rng.choice(open_sides)
            p, _ = n["side"][i]
            out.append(rebuilt(n, lambda m: {**m, "side": m["side"][:i]
                                                   + ((p, {"method": "norm_num"}),)
                                                   + m["side"][i + 1:]}))
    kids = [n for n in nodes if n is not cert["tree"]]
    if kids:
        n = rng.choice(kids)
        other = "cos" if n["rule"] != "cos" else "sin"
        out.append(rebuilt(n, lambda m: {**m, "rule": other}))
    return out


def property_results(seed=SEED, families=None):
    """Run DISCHARGE_PROPERTY_TEST: {checker: Stats}, plus 'refutation'.
    Each family of keys draws from its own stream, seeded from `seed` and
    its name, so a run of some families (a planted-bug child's) samples
    them exactly as the full run does. The refutations are checked on the
    full run only."""
    stats = {name: Stats() for name in CHECKERS + ("refutation",)}
    refute_keys = []

    def trial(rng, name, k, extra=(), targets=(), random_certs=()):
        certs = list(extra)
        mine = SR.propose(k)
        if mine is not None:
            certs.append(mine)
        base = [c for c in certs if c is not None]
        certs += [mutate(rng, c) for c in base for _ in range(2)]
        certs += list(random_certs)
        accepted = False
        for cert in certs:
            if cert is not None and DC.check(k, cert) is not None:
                accepted = True
                _record(stats[name if name == "dispatcher" else cert["method"]],
                        k, cert, rng, targets)
        if not accepted:
            refute_keys.append(k)

    def farkas(rng):
        for _ in range(200):
            k, _ = _farkas_key(rng)
            trial(rng, "farkas", k, random_certs=farkas_candidates(k)[:10])
        for _ in range(80):  # E49's sqrt label (SQRT_FACT_RULE)
            k, targets = _sqrt_key(rng)
            trial(rng, "farkas", k, targets=targets,
                  random_certs=farkas_candidates(k)[:10])
        for _ in range(80):  # E54's cos labels (ATOM_FACT_RULE)
            k, targets = _cos_key(rng)
            trial(rng, "farkas", k, targets=targets,
                  random_certs=farkas_candidates(k)[:10])

    def hyp(rng):
        for _ in range(250):
            k, _ = _hyp_key(rng)
            trial(rng, "hyp", k, random_certs=_hyp_random(rng, k))

    def sign(rng):
        for _ in range(150):
            k, certs = _sign_key(rng)
            trial(rng, "sign", k, certs)

    def product(rng):
        for _ in range(120):
            k, certs = _product_key(rng)
            trial(rng, "sign product", k, certs)

    def node(rng):
        for _ in range(150):
            k, certs = _node_key(rng)
            trial(rng, "sign node", k, certs)

    def cite(rng):
        for _ in range(150):
            k, certs, targets = _cite_key(rng)
            trial(rng, "cite", k, certs, targets)

    def leaf(rng):
        s = stats["norm_num"]
        for _ in range(1200):
            k = _literal_key(rng)
            if DC.check(k, {"method": "norm_num"}) is None:
                continue
            s.accepted += 1
            try:
                ok = holds(k, {})
            except Skip:
                s.skipped += 1
                continue
            s.evaluated += 1
            if not ok:
                s.violations.append(f"{T.show(k)} accepted by the leaf is false")

    def dispatcher(rng):
        for _ in range(120):
            k, _ = _dispatcher_key(rng)
            trial(rng, "dispatcher", k,
                  random_certs=farkas_candidates(DC.exact_values(k)[0])[:6])

    def reg(rng):  # REG_PROPERTY_TEST
        st = stats["reg"]
        for _ in range(2000):
            k, (lo, hi, iv) = _reg_key(rng)
            cert = SR.propose(k)
            if cert is None or DC.check(k, cert) is None:
                continue
            st.accepted += 1
            sides = _reg_tree_sides(cert["tree"])
            for q in _reg_points(rng, lo, hi, iv):
                env = {"x": q}
                st.evaluated += 1
                bad = [p for p in sides if not _side_holds(p, env)]
                if bad:
                    st.violations.append(f"{T.show(k)} accepted, and its side "
                                         f"{T.show(bad[0])} fails at x = {q}")
                    break
            for m in _reg_mutants(rng, cert, k.dom):
                if DC.check(k, m) is not None:
                    st.violations.append(f"{T.show(k)}: a mutated certificate is "
                                         f"accepted: {m!r}")
                    break

    runs = {"reg": reg, "farkas": farkas, "hyp": hyp, "sign": sign,
            "sign product": product, "sign node": node, "cite": cite, "norm_num": leaf,
            "dispatcher": dispatcher}
    for name, run in runs.items():
        if families is None or name in families:
            run(random.Random(f"{seed}/{name}"))
    if families is not None:
        return stats
    rng, s = random.Random(f"{seed}/refutation"), stats["refutation"]
    for _ in range(40):  # E50: univariate # 0 keys with a rational root inside
        refute_keys.append(_root_key(rng))
    for k in refute_keys[::2] + refute_keys[-40:]:
        r = RF.decided_false(k, K._owed)
        if r is None:
            continue
        s.accepted += 1
        problem = refutation_problem(k, r, rng)
        if problem:
            s.violations.append(problem)
    return stats


def refutation_problem(k, r, rng=None):
    """An F3 point must lie in the domain with the proposition false there,
    by this file's evaluation; an F1 or F2 refusal of a closed key must be
    false by the math module's reading. F1 of a key with a free variable
    (the exact values made it literal, so its variables cancelled) must be
    false at every sampled point of its domain."""
    try:
        if r.point is not None:
            inside, held = judge_at(k, dict(r.point))
            if not inside or held:
                return (f"{T.show(k)}: F3 at {r.point}: in the domain {inside}, "
                        f"holds {held} ({r.message})")
            return None
        if not T.fv(k):
            if float_holds(replace(k, dom=()), {}):
                return f"{T.show(k)} is true by the math module ({r.message})"
            return None
        for env in points(rng or random.Random(SEED), k, 5):
            if judge_at(k, env)[1]:
                return f"{T.show(k)} holds at {env} ({r.message})"
    except Skip:
        return f"{T.show(k)}: the refutation {r.message!r} cannot be read here"
    return None


def property_problems(results=None):
    results = results or property_results()
    out = []
    for name, s in results.items():
        out += [f"{name}: {v}" for v in s.violations[:3]]
        if name == "refutation":
            if s.accepted < MIN_REFUTED:
                out.append(f"refutation: only {s.accepted} refutations checked")
            continue
        if s.accepted < MIN_ACCEPTED or s.evaluated < MIN_POINTS:
            out.append(f"{name}: {s.accepted} accepted, {s.evaluated} points "
                       f"evaluated ({s.skipped} skipped): below {MIN_ACCEPTED} "
                       f"and {MIN_POINTS}")
    return out


def property_summary(results):
    return "; ".join(f"{n} {s.accepted}/{s.evaluated}/{s.skipped}"
                     for n, s in results.items())


# ---------------------------------------------------------------- unittest

class Expected(unittest.TestCase):
    def test_every_certificate_is_accepted_and_found(self):
        for row in expected_certificates():
            with self.subTest(where=row[0]):
                self.assertEqual(expected_problems(row), [])


class MustReject(unittest.TestCase):
    def test_reasons_cover_the_cases(self):
        self.assertEqual(set(REJECT_REASONS), {c["id"] for c in X.DISCHARGE_MUST_REJECT
                                               + SQRT_FACT_MUST_REJECT
                                               + SIGN_PRODUCT_MUST_REJECT
                                               + CONSOLIDATION_MUST_REJECT})
        self.assertEqual(len(X.DISCHARGE_MUST_REJECT), 32)

    def test_each_is_rejected_for_its_reason(self):
        for c in X.DISCHARGE_MUST_REJECT:
            with self.subTest(case=c["id"]):
                self.assertEqual(must_reject_problems(c), [])

    def test_sqrt_fact_cases(self):
        for c in SQRT_FACT_MUST_REJECT:
            with self.subTest(case=c["id"]):
                self.assertEqual(must_reject_problems(c), [])
        for c in SQRT_FACT_CHECKER_ACCEPTS:
            with self.subTest(case=c["id"]):
                self.assertEqual(checker_accept_problems(c), [])

    def test_consolidation_cases(self):
        for c in SIGN_PRODUCT_MUST_REJECT + CONSOLIDATION_MUST_REJECT:
            with self.subTest(case=c["id"]):
                self.assertEqual(must_reject_problems(c), [])
        for c in SIGN_PRODUCT_CHECKER_ACCEPTS + CONSOLIDATION_CHECKER_ACCEPTS:
            with self.subTest(case=c["id"]):
                self.assertEqual(checker_accept_problems(c), [])

    def test_each_neighbour_is_accepted(self):
        self.assertEqual(len(X.DISCHARGE_CHECKER_ACCEPTS), 9)
        for c in X.DISCHARGE_CHECKER_ACCEPTS:
            with self.subTest(case=c["id"]):
                self.assertEqual(checker_accept_problems(c), [])

    def test_signed_member_needs_a_strict_item(self):
        self.assertEqual(hyp_signed_member_problems(), [])

    def test_reasons_are_the_checkers(self):
        for reason in REJECT_REASONS.values():
            self.assertIn(reason.split("/")[-1], DC.REASONS)

    def test_unknown_fields_and_methods_reject(self):
        k = key("x > 0", "(0, 1)")
        good = cert_of(X._RANGE_LO)
        self.assertIsNotNone(DC.check(k, good))
        for bad in ({**good, "extra": 1}, {**good, "method": "fm"}, "farkas", None,
                    {**good, "method": ["farkas"]},
                    {k2: v for k2, v in good.items() if k2 != "sense"}):
            with self.subTest(cert=bad):
                self.assertIsNone(DC.check(k, bad))

    def test_equations_and_regularity_are_never_targets(self):
        for s in ("x == x @ [0, 1]", "sin x in C^0([0, 1])"):
            self.assertIsNone(DC.check(judgement(s), {"method": "norm_num"}))


class Regularity(unittest.TestCase):
    def test_must_reject(self):
        self.assertEqual(len(REG_MUST_REJECT), 22)
        for c in REG_MUST_REJECT:
            with self.subTest(case=c["id"]):
                self.assertEqual(reg_must_reject_problems(c), [])

    def test_checker_accepts(self):
        self.assertEqual(len(REG_CHECKER_ACCEPTS), 17)
        for c in REG_CHECKER_ACCEPTS:
            with self.subTest(case=c["id"]):
                self.assertEqual(checker_accept_problems(c), [])

    def test_decided_false(self):
        for c in X.REG_DECIDED_FALSE:
            with self.subTest(case=c["id"]):
                self.assertEqual(reg_decided_false_problems(c), [])

    def test_sides_listed(self):
        self.assertEqual(reg_sides_listed_problems(), [])

    def test_review_must_reject(self):
        for c in REG_REVIEW_MUST_REJECT:
            with self.subTest(case=c["id"]):
                self.assertEqual(reg_must_reject_problems(c), [])

    def test_review_decided_false(self):
        for c in X.REG_REVIEW_DECIDED_FALSE:
            with self.subTest(case=c["id"]):
                self.assertEqual(reg_decided_false_problems(c), [])

    def test_side_key_rule(self):
        for row in reg_side_key_rows():
            with self.subTest(where=row[0]):
                self.assertEqual(reg_side_key_problems(row), [])

    def test_reasons_are_the_checkers(self):
        for reason in X.REG_REASONS:
            self.assertIn(reason, DC.REASONS)


class DecidedFalse(unittest.TestCase):
    def test_messages(self):
        for where, spec in decided_false_cases():
            with self.subTest(where=where):
                self.assertEqual(decided_false_problems(spec), [])

    def test_undecided(self):
        for row in undecided_cases():
            with self.subTest(case=row[0]):
                self.assertEqual(undecided_problems(row), [])

    def test_tan_zero(self):
        self.assertEqual(tan_zero_problems(), [])


class Entries(unittest.TestCase):
    def test_pinned(self):
        self.assertEqual(entries_problems(), [])


class Property(unittest.TestCase):
    def test_every_accept_holds_and_every_refutation_is_false(self):
        results = property_results()
        self.assertEqual(property_problems(results), [],
                         f"seed {SEED}: {property_summary(results)}")


if __name__ == "__main__":
    unittest.main()
