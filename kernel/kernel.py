"""The kernel: proof states, the rules P1 needs, and `step`.

Trusted (DESIGN.md §15.2 items 2, 3 and 5). This file holds the rules
(`rewrite`, `fact`, `ftc`, `close`, `int_subst`, `int_flip`, and §6.1's
refl/trans/cong inside them, p1_expected E16; int_subst is §6.4's
substitution, forward and reverse, with E46's flip, as INT_SUBST_RULE states
it; int_flip is §5.1's reversed integral, as INT_FLIP_RULE states it, E51),
E56's one orientation rule for every range a step builds (`_range_of`), the
matcher and instantiator (REWRITE_RULE), the obligation tracker, and
§15.3's handles. kernel/ARCHITECTURE.md §4 is the
contract for `step`. p1_expected.py is the specification, and it is never
imported here. Nothing in this file names a P1 term: every obligation, tag
and refusal is computed by the rules.

**Protection: handles for facts, sentinel for proof states** (§15.3 asks
which is in force; both are, one per kind of object, and HANDLES_IN_FORCE
says so).

- *Handles for facts* (p1_expected E17). `fact` mints a `Handle`: an id and
  a lineage, nothing else. The kernel keeps the minted object in `_MINTED`,
  and a fact slot accepts only that object, by identity, from the same
  lineage. Copies, pickles, altered ids, bare ints and raw Judgements are
  all refused 'fact-not-minted-handle', without raising. So a theorem
  cannot be built, copied, pickled or faked from outside the kernel.
- *The sentinel for proof states.* ProofState's constructor demands the
  private `_TOKEN`, and step() and report() refuse any state not in
  `_STATES`. That is enough for states because a finished state, the only
  kind report() gives a verdict for, is only ever produced by step():
  install() makes the first, open, state and every later one is step()'s
  output, so no caller assembles one. §15.3's realistic failure is a buggy
  tactic that builds a result object instead of calling the kernel, and
  a state built without the token, or copied, is refused.

What neither stops is a deliberate write through private names, which
§15.3 says Python cannot prevent: `_TOKEN`, `object.__setattr__`, `gc`,
`state._tracker._entries.clear()` (a finished state then reports
'Proved.'), or rebinding `_MINTED[h.id]` (a genuine handle then stands for
any conclusion). Nobody does these by accident. The records the accessors
return (Obligation, StepRecord, a handle's conclusion) are frozen and
slotted, so no `vars()` or `__dict__` write reaches them. §16.3's API
boundary, not built in this milestone, replaces in-process states with
ids, so that no state crosses it.

**Obligations** (§5.4). Each obligation is keyed by its Judgement, domain
included (E8), and has one of three statuses, decided once, at emission
(p1_expected E32, DISCHARGE_RULE's order): E7's norm_num; the exact values
then norm_num (E31); a certificate the untrusted search proposes and the
trusted checker (discharge.py) accepts; otherwise the untrusted refuter may
decide it false, which refuses the step 'obligation-decided-false' (E33),
and failing that it is admitted with a reason (REASON_NONE,
REASON_EMPTY or REASON_REJECTED) and the untrusted tagger's tag. 'open' is
a status the tracker knows and this milestone never produces. A regularity
judgement e in C^k(D) is decided by E60's REG_DISCHARGE_ORDER instead
(`_discharge_reg`): the search's derivation checked by discharge.py's
regularity checker, E63's decided-false through its definedness sides, or
an admission tagged by the tagger.

**The Int and D formers** (p1_expected E64, §18 Q23). Wherever a term
enters, after its E6/E26 formers, a statable Int owes its integrand in C^0
on its range and a D[x] e owes e in C^1 at its position domain; ring and
field then read both as atoms (E66 (1)), and only an unstatable Int is
still refused, by them and by E57's step 2a.

**refl, trans and cong** (§6.1) are not moves (E16). trans is the linear
proof state: each accepted step replaces the goal by one proved equal to it.
cong is the matcher's congruence step (REWRITE_RULE step 5), so it inherits
the D[x] restriction. refl is `close` proving lhs == value by its check.

**Untrusted imports.** There are five, and none of them can yield a
theorem: tagger (tags are relied on for nothing), residual (it renders the
residual of a refused step), schema (the closed whitelist, which only sets
how strong a statement is, §9, and E27's check, which only refuses),
search (it proposes a certificate, and only discharge.check's acceptance
discharges; a search bug costs an admission, E28) and refute (decided
false, which can only refuse a step, and a refused step changes nothing,
E13, E33).

**Definedness** (p1_expected E6, E26 (a)). A former owes its condition
where its term enters the proof: '/' and negative powers their divisor
d # 0, RPow its base > 0, and each partial builtin its natural domain
(NATURAL_DOMAINS: ln u owes u > 0, sqrt u owes u >= 0, and so on). ring's
identities hold only where every atom is defined, so a builtin that owed
nothing would let ring cancel an undefined atom (0*ln(-1) == ?A would close
as 'Proved.'). Integral and Deriv nodes have no condition the kernel can
state, and field.py refuses to normalise them instead (E26 (b)).

**Seams** (ARCHITECTURE.md §7). `derivative_domain`, `_Tracker.add`,
`NATURAL_DOMAINS`, `_encloses`, `_charge_formers`, `_range_of`, `_decided`
and `_no_trees_erased`,
int_subst's rule functions (`_select`, `_fresh`, `_subst_under_D`,
`_new_orientation`, `_subst_deriv`, `_reverse_check`, `_endpoint`,
`_forward_premises`, `_reverse_premises`, `_new_integrand`,
`_new_integral`), and int_flip's (`_flip_under_D`, `_flipped`), are ordinary code
that the planted-bug and definedness-mutation runs replace in a child process.
Keep their names and signatures. Call them only as written below, and never
bind them anywhere else.
"""

import itertools
import math
import weakref
from dataclasses import dataclass, replace
from fractions import Fraction
from types import MappingProxyType

import deriv as DV
import limits as LM
import domains
import field as FD
import discharge
import refute
import residual
import schema
import search
import tagger
import trig_norm
import complexes
import entries
import roots
from entries import ENTRIES
from terms import (Arc, CInt, Join, Open, PV, PathP, Rev, Seg, Const, NEG_INF, POS_INF, Add, App, Branch, Call, CVar, Deriv, Div, Integral, Mul,
                   Interval, MVar, Neg, NegInf, NonZero, Num, PosInf, Pow,
                   Refused, Reg, Rel, RPow, Term, Var, _shown, bv, check_goal,
                   check_names, children, fv, instantiate, parse_term,
                   show, show_goal, statable, subst, trees, with_domain, check_sorts, sort_of)

# §15.3: "say which is in force". Both are, one per kind of object. Fact
# slots take handles, accepted only by identity with the kernel's record
# (E17). Proof states are protected by §15.3's sentinel, the private
# _TOKEN, because a verdict-carrying (finished) ProofState is only ever
# produced by step(); §15.3's realistic threat is a buggy tactic building a
# result object, which the sentinel stops; and §16.3's API boundary, not
# built here, will replace in-process states with ids. p1_expected's value
# must match this one, since the script compares them.
HANDLES_IN_FORCE = "handles for facts, sentinel for proof states"
DISCHARGED, ADMITTED, OPEN = "discharged", "admitted", "open"
# An admission's reason (p1_expected E32; 'discharge not built' is retired).
REASON_REG = "regularity not built"  # retired (p1_expected E60): no key carries it
REASON_NONE = "no method decides it"         # tagged ('none', ())
REASON_REJECTED = "certificate not accepted"  # a method is named, but the
# checker refused the search's certificate, or none was built
REASON_EMPTY = "domain inconsistent"  # §5.3's pre-check found the domain
# infeasible and nothing else closed the key: vacuously true, admitted
DECIDED_FALSE = "obligation-decided-false"  # E33
VERDICT = "Proved modulo {n} admissions"
MOVES = ("rewrite", "fact", "ftc", "close", "int_subst", "int_flip",
         "int_parts", "int_improper", "taylor_lagrange", "bound", "verify",
         "quad_t", "sep_autonomous", "energy_integral", "cint_param",
         "residues", "int_even", "int_re", "int_im")
# E96: the moves an order goal takes; `bound` takes nothing else. The ODE
# rules (E149) mint a handle and leave any goal as it is.
ORDER_MOVES = ("rewrite", "fact", "taylor_lagrange", "bound", "quad_t",
               "sep_autonomous", "energy_integral")
ORDERINGS = ("<", "<=", ">", ">=")

# The documented public API. No name here returns a ProofState from a str,
# bytes or dict (FORGERIES json_roundtrip_state, no_loader).
__all__ = ("HANDLES_IN_FORCE", "DISCHARGED", "ADMITTED", "OPEN",
           "REASON_REG", "REASON_NONE", "REASON_REJECTED", "REASON_EMPTY",
           "DECIDED_FALSE", "VERDICT", "MOVES", "Refusal", "Obligation",
           "StepRecord", "Handle", "ProofState", "install", "step", "report",
           "derivative_domain", "Assumption", "assumptions")


# ---------------------------------------------------------------- records

@dataclass(frozen=True, slots=True)
class Refusal:
    """What step and install return instead of a state. The input state is
    unchanged, and nothing was emitted (E13)."""
    code: str
    message: str
    residual: object = None  # a Term: lhs − rhs of a failed check (E14)


@dataclass(frozen=True, slots=True)
class Obligation:
    """One tracker entry, or one key of a step's emission list.

    key      the Judgement, domain included (E8, E5)
    sources  frozenset of SOURCES codes ("former", "orient", "d_ln", ...)
    status   DISCHARGED or ADMITTED (OPEN is never produced here)
    tag      (method, cites): the procedure that closed it, or the tagger's
             proposal for an admission
    reason   REASON_NONE, REASON_EMPTY or REASON_REJECTED for
             an admission, else None
    certificate  the certificate discharge.check accepted (methods 1-6),
             deep-frozen (dicts read-only, lists tuples), else None
             (norm_num, ftc's premise, every admission)
    """
    key: object
    sources: frozenset
    status: str
    tag: tuple
    reason: object = None
    certificate: object = None


@dataclass(frozen=True, slots=True)
class StepRecord:
    """What produced a state. `emitted` has one Obligation per key the step
    emitted, carrying that step's sources only, whether or not the key was
    already tracked. It comes from the step's own buffer, never from the
    tracker. There is no `new` flag: the caller compares against the
    previous state's obligations()."""
    move: str  # "install" or one of MOVES
    emitted: tuple
    occurrences: object = None  # rewrite: how many places it acted on (E2)
    trace: object = None  # ftc: deriv's TraceEntry tuple
    output: object = None  # ftc: deriv(F)
    handle: object = None  # fact: the minted Handle


@dataclass(frozen=True, eq=False)
class Handle:
    """An opaque theorem handle (§15.3, E17). Constructing one, or copying
    or unpickling a real one, gives an object no fact slot accepts. Not
    slotted, so E17's copy and pickle round trips succeed and the identity
    check is what refuses them."""
    id: int
    lineage: int


@dataclass(frozen=True, slots=True)
class _Minted:
    handle: Handle
    lineage: int
    conclusion: object  # the Judgement statement[inst], hypotheses as its dom
    entry: str  # the ENTRIES name, cited in tags ("sqrt_sq_val")
    inst: tuple = ()  # the inst values, whose formers each use of the fact charges

    def __post_init__(self):
        """E175 (the K1 review's B1): a minted conclusion is sort-checked
        where every move mints one, so no handle states an order on a
        complex term (exp_pos at u := i*pi minted exp(i*pi) > 0, and
        bound read it to prove 0 > 1)."""
        check_sorts(self.conclusion)


_MINTED = {}  # handle id -> _Minted
_GAMMA = {}  # lineage -> its tuple of Assumption, fixed at install (E147)


@dataclass(frozen=True, slots=True)
class Assumption:
    """E147: for every `var` in `interval`, `judgement` (whose dom is ()).
    One item of Γ, which install takes beside the goal and checks (E148)."""
    name: str
    var: str
    interval: object  # an Interval on var
    judgement: object  # a law, an order judgement or Reg(f(var), k)
_IDS = itertools.count(1)  # handle ids, unique across the kernel
_LINEAGES = itertools.count(1)  # one per install
_STATES = weakref.WeakSet()  # every ProofState the kernel has made
_TOKEN = object()  # ProofState's constructor demands it


MESSAGE_LIMIT = 400  # characters of a term a refusal's message prints


def _brief(x):
    """show(x) for a refusal's message, cut at MESSAGE_LIMIT characters, and
    never raising: a number too long for str() (a residual's constant, say)
    is named, not printed. The Refusal's `residual` keeps the whole term."""
    try:
        text = show(x)
    except ValueError:  # Python's int-to-str digit limit
        return f"(a {type(x).__name__} too large to print)"
    return text if len(text) <= MESSAGE_LIMIT else text[:MESSAGE_LIMIT] + " ..."


def _merged(old, new):
    """E8: a second emission of a key adds its sources and nothing else."""
    if old is None:
        return new
    return replace(old, sources=old.sources | new.sources)


# ---------------------------------------------------------------- tracker

class _Tracker:
    """Insertion-ordered map key -> Obligation. Private: nothing outside
    this module holds one. A state's tracker is never changed after the
    state exists. A step works on `copy()` and publishes it only on
    success."""

    def __init__(self):
        self._entries = {}

    def copy(self):
        """A tracker with the same entries. It must not go through `add`."""
        new = _Tracker()
        new._entries = dict(self._entries)
        return new

    def add(self, emission):
        """The only way into a tracker, and a seam (ARCHITECTURE.md §7).

        `emission` is an Obligation. A new key is inserted. A known key
        gains the emission's sources, and its status, tag and reason do not
        change (E8), except that an ADMITTED key a DISCHARGED emission
        reaches takes that discharge, sources unioned (E250).
        """
        k = emission.key
        old = self._entries.get(k)
        if old is not None and old.status == ADMITTED and \
                emission.status == DISCHARGED:
            self._entries[k] = replace(emission,
                                       sources=old.sources | emission.sources)
            return
        self._entries[k] = _merged(old, emission)

    def entries(self):
        """The entries as a tuple of Obligation, in insertion order."""
        return tuple(self._entries.values())


# ---------------------------------------------------------------- state

class ProofState:
    """An immutable proof state. Only install and step make one."""

    __slots__ = ("_goal", "_original", "_lineage", "_tracker", "_last",
                 "_theorem", "__weakref__")

    def __init__(self, token, goal, original, lineage, tracker, last,
                 theorem=None):
        """Raises TypeError unless `token` is the kernel's private token.
        Registers the new state in _STATES."""
        if token is not _TOKEN:
            raise TypeError("only the kernel makes proof states")
        for name, value in (("_goal", goal), ("_original", original),
                            ("_lineage", lineage), ("_tracker", tracker),
                            ("_last", last), ("_theorem", theorem)):
            object.__setattr__(self, name, value)
        _STATES.add(self)

    def __setattr__(self, name, value):
        raise AttributeError("a proof state is immutable")

    def __delattr__(self, name):
        raise AttributeError("a proof state is immutable")

    @property
    def goal(self):
        """The current Goal, or None once `close` has succeeded."""
        return self._goal

    @property
    def original(self):
        """The Goal as installed. It is the one `close` instantiates and
        scope-checks against (E19)."""
        return self._original

    @property
    def lineage(self):
        return self._lineage

    @property
    def last(self):
        """The StepRecord that produced this state."""
        return self._last

    @property
    def theorem(self):
        """After close, instantiate(original, value). Otherwise None."""
        return self._theorem

    def obligations(self):
        """The tracker, as a tuple of Obligation records in insertion order.
        The records are the tracker's own objects, shared with every later
        state. They are frozen and slotted, so only a deliberate
        `object.__setattr__` can alter one: the private route §15.3
        accepts."""
        return self._tracker.entries()

    def conclusion(self, handle):
        """The Judgement a handle of this state's lineage stands for: the
        kernel's own, frozen and slotted like every term. Raises ValueError
        for anything that _resolve_fact would refuse."""
        try:
            return _resolve_fact(self, handle).conclusion
        except Refused as r:
            raise ValueError(r.message) from None


def _kernel_state(state):
    return type(state) is ProofState and state in _STATES


# ---------------------------------------------------------------- API

def install(goal, assumptions=()):
    """Start a proof of `goal`, a Goal tree (usually from parse_goal), under
    Γ = `assumptions`, a tuple of Assumption (E147), checked by E148 after
    the goal ('assume-shape', 'assume-scope'). Γ is kept for the lineage
    and read only by the ODE rules (E154).

    It refuses a goal that is not exactly one judgement, an equation
    ('goal-shape'), and anything check_goal refuses (its GRAMMAR code). A
    goal hypothesis holding an Int or D node is refused
    'Int-or-D-not-normalisable' (E26 (b)) whether or not any key carries
    it: a hypothesis about such a value presupposes that it exists. It
    builds each Integral's range by E56 (_range_of), refusing
    'range-same-infinity', and 'orientation-undecided' when a key uses a
    range whose order discharge proves neither way. It then
    charges the formers of each goal hypothesis at the hypotheses before it,
    so `@ x > 0, ln x > 0` owes x > 0 @ x > 0, and every former of the
    judgement's sides at its position domain (E6: '/' and negative powers
    give d # 0, RPow bases give b > 0; E26: each partial builtin its
    NATURAL_DOMAINS items; source 'former'), with E25 and E7. The
    orientation of a range is emitted only when some key's domain uses it.
    Returns the first ProofState, with a
    fresh lineage and last.move == "install", or a Refusal.
    """
    try:
        if type(goal) is not tuple or len(goal) != 1:
            raise Refused("goal-shape", "a goal here is exactly one judgement")
        check_goal(goal)
        # E168: the goal's domain is realified in place, so every later
        # reader of it (discharge's Γ, keys' domains) sees real items only
        if complexes.has_complex(goal[0].dom):
            goal = (replace(goal[0], dom=complexes.realify_dom(goal[0].dom)),)
            check_goal(goal)
        g = goal[0]
        if not (isinstance(g, Rel) and (g.op == "==" or g.op in ORDERINGS)):
            raise Refused("goal-shape", "the moves here prove an equation "
                          "or an order judgement (E96)")
        for node in trees(g.dom):          # E26 (b): a hypothesis about an Int/D value
            FD.hypothesis_tree(node)       # presupposes it exists; refused, never admitted
        buf = {}
        for i, h in enumerate(g.dom):      # E6/E26 (a): hypotheses enter at install too
            parts = ((h.lo, h.hi) if isinstance(h, Interval) else
                     (h.lhs, h.rhs) if isinstance(h, Rel) else (h.e,))
            for t in parts:
                if isinstance(t, Term):    # skip oo ends
                    _charge_formers(buf, t, g.dom[:i], g.dom)
        for side in _sides(g):
            _charge_formers(buf, side, g.dom, g.dom)
        gamma = _check_assumptions(goal, assumptions)
    except Refused as r:
        return Refusal(r.code, r.message, r.residual)
    tracker = _Tracker()
    for ob in buf.values():
        tracker.add(ob)
    lineage = next(_LINEAGES)
    _GAMMA[lineage] = gamma
    return ProofState(_TOKEN, goal, goal, lineage, tracker,
                      StepRecord("install", tuple(buf.values())))


def assumptions(state):
    """Γ, the tuple of Assumption the state's lineage was installed under
    (E147): the theorem a proof reaches is its goal under Γ. () for a
    state that is not the kernel's."""
    if not _kernel_state(state):
        return ()
    return _GAMMA.get(state.lineage, ())


def _has_call(x):
    """x (a term, judgement or interval) holds a Call."""
    if isinstance(x, Call):
        return True
    return any(_has_call(k) for _, k in children(x)
               if isinstance(k, (Term, Interval, Rel, NonZero, Reg)))


def _assume_kind(j, var):
    """E148: 'law', 'order' or 'reg' for a judgement of that shape on var,
    else None."""
    if type(j) is Reg:
        ok = (type(j.e) is Call and j.e.args == (Var(var),) and j.dom == ()
              and (j.k == "omega" or (type(j.k) is int and j.k >= 1)))
        return "reg" if ok else None
    if type(j) not in (Rel, NonZero) or j.dom != ():
        return None
    nodes = list(trees(j))
    if type(j) is Rel and j.op == "==":
        if all(type(n) is Deriv and n.var == var and type(n.body) is Call
               and n.body.args == (Var(var),) for n in nodes):
            return "law"
        return None
    if (type(j) is NonZero or j.op in ORDERINGS) and not nodes:
        return "order"
    return None


def _check_assumptions(goal, gamma):
    """E148. Returns Γ as a tuple, or raises 'assume-shape' or
    'assume-scope'."""
    if type(gamma) not in (tuple, list):
        raise Refused("assume-shape", "assumptions are a tuple of Assumption")
    gamma = tuple(gamma)
    names, free, bound = set(), fv(goal), bv(goal)
    for a in gamma:
        if type(a) is not Assumption:
            raise Refused("assume-shape", f"{a!r} is not an Assumption")
        if not (type(a.name) is str and a.name.isascii()
                and a.name.isidentifier() and a.name not in names):
            raise Refused("assume-shape", f"{a.name!r} is not a fresh "
                          "variable-like name")
        names.add(a.name)
        v, i = a.var, a.interval
        if not _names_variable(v) or type(i) is not Interval or i.var != v:
            raise Refused("assume-shape", f"{a.name}: its interval is not "
                          f"on its variable {v!r}")
        ends = [e for e in (i.lo, i.hi) if isinstance(e, Term)]
        if any(_unfit(e) or _has_call(e) or v in fv(e) for e in ends):
            raise Refused("assume-shape", f"{a.name}: an end of its interval "
                          "holds an Int, D or Call, or its variable")
        try:
            check_goal((replace(a.judgement, dom=(i,)),))
        except (Refused, TypeError, AttributeError) as r:
            raise Refused("assume-shape", f"{a.name}: "
                          f"{getattr(r, 'message', 'not a judgement')}") from None
        if _assume_kind(a.judgement, v) is None:
            raise Refused("assume-shape", f"{a.name}: {_brief(a.judgement)} "
                          "is not a law, an order judgement or a reg on "
                          f"{v}")
        if v in free or v in bound:
            raise Refused("assume-scope", f"{a.name}: {v} is a variable of "
                          "the goal")
        out = (fv(a.judgement) | fv(i)) - {v} - free
        if out:
            raise Refused("assume-scope", f"{a.name} mentions "
                          f"{', '.join(sorted(out))}, not in the goal")
    check_names(goal, *(replace(a.judgement, dom=(a.interval,))
                        for a in gamma))
    return gamma


def step(state, move, args):
    """Apply one move (ARCHITECTURE.md §4). Returns a new ProofState or a
    Refusal.

    Common checks come first, in order: the state is one of _STATES
    ('state-not-minted'); its goal is open ('proof-finished'); `move` is in
    MOVES ('bad-move'); `args` is a dict with exactly that move's keys, each
    of the right type ('bad-args'). Every fact slot is then resolved by
    _resolve_fact. The move's own function runs next, collecting emissions in
    a buffer. On success, the tracker is copied, each emission goes through
    _Tracker.add, and the new state is built. terms.Refused becomes a
    returned Refusal at this one point, with nothing emitted. Any other
    exception propagates: it is a kernel bug, not a refusal (E21).

      rewrite  {"entry": str, "inst": {str: Term}, "at": Term,
                optionally "occurrence": int}
      fact     {"entry": str, "inst": {str: Term}, "bind": str}
      ftc      {"F": Term, "check": "ring" | "field", "facts": list | tuple}
      close    {"value": Term, "check": "ring" | "field", "facts": list |
                tuple}
      int_subst  INT_SUBST_RULE's args (p1_expected INT_SUBST_ARGS)
      int_flip   {} or {"occurrence": int}
    """
    if not _kernel_state(state):
        return Refusal("state-not-minted", "not a state this kernel made")
    try:
        if state.goal is None:
            raise Refused("proof-finished", "the goal is already closed")
        if type(move) is not str or move not in MOVES:
            raise Refused("bad-move", f"the moves are {', '.join(MOVES)}")
        _goal_shape(state.goal[0], move)
        _check_args(move, args, state.goal)
        minted = [_resolve_fact(state, f) for f in args.get("facts", ())]
        buf = {}
        goal, theorem, extra = _MOVE[move](state, args, minted, buf)
        if goal is not None:
            _statable_again(buf, state.goal[0], goal[0])  # E83
    except Refused as r:
        return Refusal(r.code, r.message, r.residual)
    tracker = state._tracker.copy()
    for ob in buf.values():
        tracker.add(ob)
    return ProofState(_TOKEN, goal, state.original, state.lineage, tracker,
                      StepRecord(move, tuple(buf.values()), **extra), theorem)


def _goal_shape(g, move):
    """E96: an order goal takes ORDER_MOVES only, and bound takes an order
    goal only."""
    if g.op != "==" and move not in ORDER_MOVES:
        raise Refused("goal-shape", f"{move} proves an equation; an order "
                      "goal takes " + ", ".join(ORDER_MOVES))
    if g.op == "==" and move == "bound":
        raise Refused("goal-shape", "bound closes an order goal; an "
                      "equation is closed by close")


def report(state):
    """The one report string for a state (§5.4, §15.6).

    Closed with N admissions, N > 0: VERDICT.format(n=N). Closed with none
    admitted and every obligation discharged: "Proved.", which no PROOFS run
    reaches (a goal that owes nothing, e.g. '1 + 1 == ?A' closed with 2,
    does report it). A status other than discharged or admitted counts as
    open, so an unknown one blocks rather than passes. Not closed:
    "Open: " + show_goal(goal). Raises TypeError for anything
    that is not in _STATES. There is no other parameter, so no caller can
    supply a count or a status.
    """
    if not _kernel_state(state):
        raise TypeError("report takes a proof state this kernel made")
    if state.goal is not None:
        return "Open: " + show_goal(state.goal)
    obs = state.obligations()
    n = sum(ob.status == ADMITTED for ob in obs)
    stuck = sum(ob.status not in (DISCHARGED, ADMITTED) for ob in obs)
    if stuck:  # §5.4: an open obligation, or anything unknown, blocks
        return f"Stuck: {stuck} open obligations"
    return VERDICT.format(n=n) if n else "Proved."


def derivative_domain(closed):
    """The interval ftc's derivative premise, deriv and the check run on:
    the open interval with `closed`'s ends (§6.4).

    A seam (ARCHITECTURE.md §7). ftc calls it by this global name, once,
    and the C¹ premise builds its own open interval without it. The two are
    kept apart on purpose: the planted bug ftc_derivative_premise_on_closed
    replaces this one alone.
    """
    return Interval(closed.var, closed.lo, False, closed.hi, False)


# ---------------------------------------------------------------- arguments

_ARGS = {"rewrite": ("entry", "inst", "at"), "fact": ("entry", "inst", "bind"),
         "ftc": ("F", "check", "facts"), "close": ("value", "check", "facts"),
         "int_subst": ("var", "sub", "new_var", "lo", "hi", "check", "facts"),
         "int_flip": (), "int_parts": ("var", "u", "v", "check", "facts"),
         "int_improper": ("F", "check", "facts"),
         "taylor_lagrange": ("bind", "f", "var", "lo", "hi", "at", "derivs",
                             "side", "sense", "check", "facts"),
         "bound": ("check", "facts"), "verify": ("check", "facts"),
         # p1_expected ODE_ARGS (E149)
         "quad_t": ("bind", "law", "regs", "lo", "hi", "var", "F", "check",
                    "facts"),
         "sep_autonomous": ("bind", "law", "regs", "lo", "hi", "var", "f",
                            "F", "range", "using", "check", "facts"),
         "energy_integral": ("bind", "law", "kin", "regs", "lo", "hi", "var",
                             "f", "F", "range", "using", "check", "facts"),
         "cint_param": (),  # E191
         "residues": (),  # E200
         "int_even": (),  # E217
         "int_re": ("F",), "int_im": ("F",)}  # E257
_TERM_ARGS = ("at", "F", "value", "sub", "lo", "hi", "f", "u", "v", "scale")


def _names_variable(v):
    """v is a str the parser reads as that variable (not pi, sin or e)."""
    try:
        return type(v) is str and parse_term(v) == Var(v)
    except Refused:
        return False


def _node_at(t, path):
    """The subterm of t at `path` (_positions' slots), or None."""
    for slot in path:
        kids = dict(children(t)) if isinstance(t, Term) else {}
        if slot not in kids:
            return None
        t = kids[slot]
    return t


def _statable_again(buf, old, new):
    """E83: at each path where `new` holds a statable Int and `old` an
    unstatable one, that Int's E64 former, as _tree_formers charges it.
    Only an edit inside a limit makes an Int statable, and no other rule
    owes the former then."""
    G = new.dom
    old_sides = _sides(old)
    for i, side in enumerate(_sides(new)):
        walk = list(_positions(side, G))
        body = {p: (d, a) for p, _, d, a in walk}
        for p, t, _, _ in walk:
            if not (isinstance(t, Integral) and statable(t)):
                continue
            was = _node_at(old_sides[i], p) if i < len(old_sides) else None
            if isinstance(was, Integral) and not statable(was):
                bd, ba = body[p + ("body",)]
                _int_former(buf, t, bd, ba, G)


def _check_args(move, args, goal):
    """'bad-args' unless args has exactly the move's keys (rewrite may add
    `occurrence`; int_subst `mode` and `occurrence`, and in reverse mode
    needs `f`), each of the right type. A term argument must be a Term
    with no ?A, and check_goal must accept it as a side (its GRAMMAR code
    otherwise), so every term that can enter the goal is well formed; an
    int_subst term holds no oo either (close's rule). With the goal, the
    terms must pass check_names as one statement."""
    need = set(_ARGS[move])
    optional = ({"occurrence"} if move in ("rewrite", "int_flip", "ftc",
                                           "int_parts", "int_improper",
                                           "cint_param", "int_even",
                                           "int_re", "int_im")
                else {"occurrence", "region", "half"} if move == "residues"
                else {"scale"} if move == "bound" else set())
    if move == "int_subst":  # INT_SUBST_RULE step 1 (E36, E45, E48)
        optional = {"mode", "occurrence"}
        if type(args) is dict and args.get("mode") == "reverse":
            need |= {"mode", "f"}
    ok = type(args) is dict and need <= set(args) <= need | optional
    inst = args.get("inst", {}) if ok else None
    ok = ok and type(inst) is dict and all(type(k) is str for k in inst)
    ok = ok and all(type(args[k]) is str
                    for k in ("entry", "bind") if k in args)
    ok = ok and type(args.get("occurrence", 0)) is int
    if ok and move in ("ftc", "close", "int_subst", "int_parts",
                       "int_improper", "taylor_lagrange", "verify",
                       *_ODE_MOVES):
        facts = args["facts"]
        ok = (type(args["check"]) is str and args["check"] in ("ring", "field")
              and type(facts) in (list, tuple)
              and not (args["check"] == "ring" and facts))
    if ok and move in ("int_flip", "ftc", "int_improper",
                       "cint_param", "residues", "int_even", "int_re",
                       "int_im"):  # E51, E73, E191, E200, E257
        ok = args.get("occurrence", 0) >= 0
    if ok and move == "residues":  # E201: a list of conditions
        region = args.get("region", ())
        ok = type(region) in (list, tuple) and all(
            type(j) in (Rel, NonZero) and j.dom == () for j in region)
        # E213: upper or lower reads a line Int, and takes no region
        ok = ok and ("half" not in args or (args["half"] in (
            "upper", "lower", "keyhole", "sector") and "region" not in args))
        try:
            for j in region if ok else ():
                check_sorts(j)
        except Refused:
            ok = False
    if ok and move == "int_parts":  # INT_PARTS_RULE step 1
        ok = args.get("occurrence", 0) >= 0 and _names_variable(args["var"])
    if ok and move == "bound":  # E99: ring's lone fact is the order one
        ok = (type(args["check"]) is str and args["check"] in ("ring", "field")
              and type(args["facts"]) in (list, tuple))
    if ok and move == "taylor_lagrange":  # E97
        ds = args["derivs"]
        ok = (type(ds) in (list, tuple)
              and 2 <= len(ds) <= domains.REG_MAX_CLASS
              and type(args["side"]) is str
              and args["side"] in ("lower", "upper")
              and type(args["sense"]) is str
              and args["sense"] in TAYLOR_SENSES
              and _names_variable(args["var"]))
    if ok and move in _ODE_MOVES:  # E149
        names = ("law", "kin")
        lists = ("regs", "using")
        ok = (all(type(args[k]) is str for k in names if k in args)
              and all(type(args[k]) in (list, tuple)
                      and all(type(x) is str for x in args[k])
                      for k in lists if k in args)
              and type(args["bind"]) is str and _names_variable(args["var"]))
        if ok and "range" in args:
            r = args["range"]
            ok = (type(r) is Interval and r.var == args["var"]
                  and r.lo_closed is False and r.hi_closed is False)
            try:  # E159: the range as check_goal reads a domain item
                ok = ok and (check_goal((Rel("==", Var(r.var), Var(r.var),
                                             (r,)),)) is None)
            except Refused:
                ok = False
    if ok and move == "int_subst":
        ok = (type(args.get("mode", "forward")) is str
              and args.get("mode", "forward") in ("forward", "reverse")
              and args.get("occurrence", 0) >= 0
              and _names_variable(args["var"]) and _names_variable(args["new_var"]))
    if not ok:
        raise Refused("bad-args", f"{move} takes {', '.join(sorted(need))}"
                      if need else f"{move} takes no argument but occurrence")
    given = [args[k] for k in _TERM_ARGS if k in args] + list(inst.values())
    if move in _ODE_MOVES and "range" in args:  # E152: the range's ends
        given += [e for e in (args["range"].lo, args["range"].hi)
                  if isinstance(e, Term)]
    if move == "taylor_lagrange":
        given += list(args["derivs"])
    for t in given:  # check_goal first: it refuses a malformed node unread
        if not isinstance(t, Term):
            raise Refused("bad-args", f"not a term without ?A: {_shown(t)}")
        try:
            check_goal((Rel("==", t, t),))
        except RecursionError:  # E85: deeper than the checker's stack
            raise Refused("bad-args", "a term too deep to check") from None
        except Refused as r:
            if r.code != "mvar-misplaced":
                raise
            raise Refused("bad-args", f"not a term without ?A: "
                          f"{_shown(t)}") from None
        if (move in ("int_subst", "int_parts", "int_improper",
                     "taylor_lagrange") and _holds_infinity(t)):
            raise Refused("bad-args", f"{show(t)} mentions oo")
        if move in _ODE_MOVES and (_holds_infinity(t) or _unfit(t)):
            raise Refused("bad-args", f"{_brief(t)} holds oo, an Int or a "
                          "D node")
        if move == "taylor_lagrange" and _unfit(t):  # E102
            raise Refused("bad-args", f"{_brief(t)} holds an Int or D node")
    check_names(goal, *given)  # no x(y) into a goal whose x is a variable


def _resolve_fact(state, obj):
    """The _Minted record for `obj`, or raise Refused. It never raises
    anything else, whatever obj is.

    The record is returned only when type(obj) is Handle, obj.id is an int
    in _MINTED, and that record's handle `is` obj. Anything else raises
    'fact-not-minted-handle'. A record whose lineage is not state.lineage
    raises 'fact-foreign-state-handle'. The lineage compared is the
    kernel's record of it, never the handle's own field.
    """
    hid = getattr(obj, "id", None) if type(obj) is Handle else None
    rec = _MINTED.get(hid) if type(hid) is int else None
    if rec is None or rec.handle is not obj:
        raise Refused("fact-not-minted-handle", "a fact must be a handle that "
                      "a `fact` step minted (§15.3)")
    if rec.lineage != state.lineage:
        raise Refused("fact-foreign-state-handle", "that handle was minted in "
                      "another proof (§15.3)")
    return rec


# ---------------------------------------------------------------- positions
#
# A position's `anc` lists what encloses it, outermost first: a Deriv node,
# or an _IntScope for an Int whose *body* holds the position (REWRITE_RULE
# step 2). An occurrence in an Int's lo or hi is outside that Int. A
# position's domain is the goal's own domain, then the range of each
# enclosing Int. A node's children are terms.children's, the one table.

@dataclass(frozen=True, slots=True, eq=False)
class _IntScope:
    """An Int enclosing a position through its body: the Int and its range
    Interval. `pending` is True when the ends are symbolic, so the order is
    E56's to decide: `range` is then a placeholder [lo, hi], recognised by
    identity in a domain, that _decided replaces by the decided interval
    when a key whose domain holds it is emitted (E56_AMENDMENTS,
    laziness). Otherwise `range` is the interval itself, owing no order."""
    integral: Integral
    range: Interval
    pending: bool = False


def _subterms(t):
    """t and every Term below it, pre-order."""
    yield t
    for _, k in children(t):
        if isinstance(k, Term):
            yield from _subterms(k)


def _sides(g):
    """The sides of an equation goal that moves act on: never ?A (§9)."""
    return (g.lhs,) if isinstance(g.rhs, MVar) else (g.lhs, g.rhs)


ORIENTATION_UNDECIDED = "orientation-undecided"  # E56, every step's one code


# E56_AMENDMENTS: each orientation question, memoised per key. Discharge is
# a function of the key and ENTRIES alone (E32), so a repeated question has
# the same answer; a child process that patches a seam starts with it
# empty. Cleared when it grows past _ORDER_MEMO_BOUND keys.
_ORDER_MEMO = {}
_ORDER_MEMO_BOUND = 4096


def _settles(key):
    """DISCHARGE_RULE's steps (3)-(5) alone, as E56 asks of an orientation
    candidate: norm_num, the exact values then norm_num, or a certificate
    the trusted checker accepts. It never refutes and never emits. The
    answer is memoised per key (_ORDER_MEMO)."""
    if key in _ORDER_MEMO:
        return _ORDER_MEMO[key]
    said, stable = _settles_uncached(key)
    if stable:  # a RecursionError's answer depends on the stack, not the key
        if len(_ORDER_MEMO) >= _ORDER_MEMO_BOUND:
            _ORDER_MEMO.clear()
        _ORDER_MEMO[key] = said
    return said


def _settles_uncached(key):
    """(answer, stable). `stable` is False when a RecursionError decided the
    answer, raised here or mapped by the checker to 'too-deep': that answer
    depends on the depth of the stack it ran on, not on the key alone, so
    it is not memoised."""
    try:
        said = FD.norm_num(key)
        if said is None:
            new, _ = discharge.exact_values(key)
            said = FD.norm_num(new)
        if said is not None:
            return said, True
        cert = search.propose(key)
        if cert is None:
            return False, True
        tag, why = discharge.verdict(key, cert)
        return tag is not None, not (why or "").endswith("too-deep")
    except Refused:
        return False, True
    except RecursionError:
        return False, False


def _range_of(v, lo, hi, dom):
    """E56, the one orientation rule: the Interval of v between the limits
    lo and hi, and the orientation key its step emits (source 'orient'), or
    None. Every step that builds a range calls this function, through
    _range or directly (int_subst's new range).

    Two infinite ends: the whole line, or 'range-same-infinity' when they
    are equal. One infinite end: open there and on its own side. Two
    rational literals (field.rational_value): [min, max] with the original
    end terms, owing nothing. Otherwise lo <= hi, then hi <= lo, each at the
    position domain `dom` (with E5), goes to DISCHARGE_RULE's steps (3)-(5)
    with no refutation (_settles); the first that holds is the key, and the
    interval is [lo, hi] or [hi, lo] accordingly. Neither: Refused
    'orientation-undecided'. A proved order is never wrong, so the interval
    is exactly the points between the limits and never empty.

    A seam (ARCHITECTURE.md §7): its callers look it up by this global name,
    and E56's planted bugs replace it in a child process.

    E224: a marked end (Open) is ordered by its term, and the interval is
    open there; a+ must end up the lower end and b- the upper, else
    'open-end-side'."""
    if type(lo) is Open or type(hi) is Open:
        return _marked_range(v, lo, hi, dom)
    inf = [e for e in (lo, hi) if isinstance(e, (PosInf, NegInf))]
    if len(inf) == 2:
        if type(lo) is type(hi):
            raise Refused("range-same-infinity", f"the range of {v} is empty")
        return Interval(v, NEG_INF, False, POS_INF, False), None
    if inf:
        c = hi if inf[0] is lo else lo
        if isinstance(inf[0], PosInf):
            return Interval(v, c, True, POS_INF, False), None
        return Interval(v, NEG_INF, False, c, True), None
    ql, qh = FD.rational_value(lo), FD.rational_value(hi)
    if ql is not None and qh is not None:
        a, b = (lo, hi) if ql <= qh else (hi, lo)
        return Interval(v, a, True, b, True), None
    for a, b in ((lo, hi), (hi, lo)):
        key = with_domain(Rel("<=", a, b), dom)
        if _settles(key):
            return Interval(v, a, True, b, True), key
    raise Refused(ORIENTATION_UNDECIDED, f"the order of {show(lo)} and "
                  f"{show(hi)} is not decided; state it in the goal's domain")


def _marked_range(v, lo, hi, dom):
    """E224, with E231's correction: a marked range is ordered STRICTLY,
    so it is never empty. An infinite other end orders it; two rational
    literals decide it, and equal ones refuse 'open-end-empty'; otherwise
    lo < hi, then hi < lo, by _settles at `dom`, the one that holds being
    the orientation key. The mark must then sit on the interior side."""
    bl, bh = _bare(lo), _bare(hi)
    key = None
    if isinstance(bh, PosInf) or isinstance(bl, NegInf):
        low, high = lo, hi
    elif isinstance(bl, PosInf) or isinstance(bh, NegInf):
        low, high = hi, lo
    else:
        ql, qh = FD.rational_value(bl), FD.rational_value(bh)
        if ql is not None and qh is not None:
            if ql == qh:
                raise Refused("open-end-empty", f"the range of {v} is empty: "
                              "a marked range needs distinct ends (E231)")
            low, high = (lo, hi) if ql < qh else (hi, lo)
        else:
            for a, b in ((lo, hi), (hi, lo)):
                k = with_domain(Rel("<", _bare(a), _bare(b)), dom)
                if _settles(k):
                    low, high, key = a, b, k
                    break
            else:
                raise Refused(ORIENTATION_UNDECIDED, f"the strict order of "
                              f"{show(bl)} and {show(bh)} is not decided; a "
                              "marked range needs one (E231)")
    if (type(low) is Open and low.side != "+") or (
            type(high) is Open and high.side != "-"):
        raise Refused("open-end-side", "a marked end is approached from "
                      "inside its range: write the lower end a+ and the "
                      "upper b- (E224)")
    bl, bh = _bare(low), _bare(high)
    return Interval(v, bl, not isinstance(bl, NegInf) and type(low) is not
                    Open, bh, not isinstance(bh, PosInf) and type(high) is
                    not Open), key


def _bare(e):
    """An end without its E222 mark."""
    return e.e if type(e) is Open else e


def _open_end(it, move):
    """E227: a move that reads an Int's ends refuses a marked one."""
    if type(it.lo) is Open or type(it.hi) is Open:
        raise Refused("int-open-end", f"{move} does not take a marked end "
                      f"({show(it.lo if type(it.lo) is Open else it.hi)}); "
                      "int_improper is the route (E227)")


def _range(integral, pos_dom):
    """E56 for Integral[v = lo .. hi] at its own position domain: _range_of
    on its variable and limits."""
    return _range_of(integral.var, integral.lo, integral.hi, pos_dom)


def _symbolic(lo, hi):
    """The ends E56 orders by discharge: neither infinite, and not two
    rational literals. Only such a range has an order to decide."""
    return (not any(isinstance(e, (PosInf, NegInf)) for e in (lo, hi))
            and (FD.rational_value(lo) is None or FD.rational_value(hi) is None))


def _decided(buf, dom, anc, goal_dom):
    """E56_AMENDMENTS: `dom` with every pending range it holds decided,
    outermost first, each at its own position domain (the items before it,
    already decided), by _range_of: the placeholder is replaced by the
    decided interval, and the decided order is emitted as its key (source
    'orient'), or 'orientation-undecided' names that range. A key is only
    ever emitted on a domain this returns, so no emitted key's domain holds
    an undecided interval, the enclosing Ints' ranges of a position domain
    included; and a range no emitted key's domain holds is never decided.

    A seam (ARCHITECTURE.md §7): every caller looks it up by this global
    name, and the planted bug enclosing_range_undecided replaces it."""
    out, orients = list(dom), []
    for a in anc:
        if not (isinstance(a, _IntScope) and a.pending):
            continue
        at = next((i for i, item in enumerate(out) if item is a.range), None)
        if at is None:
            continue
        it = a.integral
        out[at], orient = _range_of(it.var, it.lo, it.hi, tuple(out[:at]))
        orients.append(orient)
    for orient in orients:
        if orient is not None:
            _emit(buf, orient, "orient", goal_dom)
    return tuple(out)


def _encloses(slot):
    """True when an Integral's child at `slot` is inside its binder's scope:
    its body only. Its lo and hi are outside (REWRITE_RULE step 2, GRAMMAR.md
    §5), so a limit gets neither the Int's variable nor its range, and a
    limit's formers are charged at the outer position domain.

    A seam (ARCHITECTURE.md §7): _positions calls it by this global name, and
    the mutation limit_former_on_own_range replaces it in a child process."""
    return slot == "body"


def _positions(t, dom, anc=(), path=()):
    """Pre-order walk of one term, children in GRAMMAR.md §7's field order.
    For each subterm it yields (path, subterm, position domain, anc). An
    Int's range is built as the walk reaches it, so every Int of a walked
    term has its range (infinite and literal ends, E4's, at once;
    'range-same-infinity'). A symbolic range's order is not decided here
    (E56_AMENDMENTS, laziness): the range stands as a placeholder [lo, hi]
    in the inner domain, which _decided resolves when a key whose domain
    holds it is emitted, so an Int whose body owes nothing never needs an
    order. rewrite (REWRITE_RULE steps 2, 6, 7, 9), int_subst's and
    int_flip's selectors and former charging (E6) all use it."""
    yield path, t, dom, anc
    if isinstance(t, (CInt, PV)):  # E192, E266: opaque; the bound variable
        return                     # stays inside
    inner_dom, inner_anc = dom, anc + ((t,) if isinstance(t, Deriv) else ())
    if isinstance(t, Integral):
        if _symbolic(_bare(t.lo), _bare(t.hi)):  # E224: the bare ends
            scope = _IntScope(t, Interval(t.var, _bare(t.lo), True,
                                          _bare(t.hi), True), True)
        else:
            scope = _IntScope(t, _range(t, dom)[0])
        inner_dom, inner_anc = dom + (scope.range,), anc + (scope,)
    for s, k in children(t):
        if not isinstance(k, Term):
            continue  # an infinite limit
        body = _encloses(s)  # an Int's lo and hi are outside its scope
        yield from _positions(k, inner_dom if body else dom,
                              inner_anc if body else anc, path + (s,))


def _put(t, path, new):
    """t with the subterm at `path` replaced by `new`, every node rebuilt
    through its constructor (so D17 is re-checked)."""
    if not path:
        return new
    s, rest = path[0], path[1:]
    if isinstance(s, int):
        args = list(t.args)
        args[s] = _put(args[s], rest, new)
        return replace(t, args=tuple(args))
    return replace(t, **{s: _put(getattr(t, s), rest, new)})


# ---------------------------------------------------------------- emission

def _emit(buf, key, source, goal_dom, discharged_by=None, divisor=True):
    """Add one emission to the step buffer (key -> Obligation), deciding its
    status in DISCHARGE_RULE's order (ARCHITECTURE.md §5). A key already in
    the buffer only gains the source. Otherwise: a NonZero divisor whose
    expression ring-normalises to zero refuses 'divisor-normalises-to-zero'
    (E25); `divisor` is False only for tan's cos u # 0, a domain and not a
    divisor (E26), which E25 does not test. Then (1) discharged_by given:
    DISCHARGED with that tag; (2) a Reg: _discharge_reg (E60's
    REG_DISCHARGE_ORDER, in place of DISCHARGE_RULE's step (2); E7 never
    sees a Reg);
    (3) field.norm_num True is DISCHARGED ('norm_num', ()), False refuses
    'obligation-refuted' (E7), and a key holding an Int or D node refuses
    'Int-or-D-not-normalisable' (E26 (b)); (4)-(7) _discharge. gamma,
    TAG_RULES' Γ, is the goal's own domain when the key kept its domain,
    else ()."""
    if complexes.has_complex(key):  # E168: every key decided is real
        for k in complexes.realify_judgement(key):
            if not complexes.real_form(k):
                raise Refused("complex-key", f"{show(k)} is not real")
            _emit(buf, k, source, goal_dom, discharged_by, divisor)
        return
    if key in buf:
        buf[key] = replace(buf[key], sources=buf[key].sources | {source})
        return
    if divisor and isinstance(key, NonZero) and FD.ring_is_zero(key.e):
        raise Refused("divisor-normalises-to-zero",
                      f"the divisor {show(key.e)} is zero in ring (E25)")
    sources = frozenset((source,))
    if discharged_by:
        ob = Obligation(key, sources, DISCHARGED, discharged_by)
    elif isinstance(key, Reg):
        ob = _discharge_reg(key, sources, goal_dom if key.dom else ())
    else:
        said = FD.norm_num(key)
        if said is False:
            raise Refused("obligation-refuted", f"norm_num: {show(key)} is false")
        if said:
            ob = Obligation(key, sources, DISCHARGED, ("norm_num", ()))
        else:
            ob = _discharge(key, sources, goal_dom if key.dom else ())
    buf[key] = ob


def _discharge(key, sources, gamma):
    """DISCHARGE_RULE's steps (4)-(7) for a key E7 did not decide. (4) The
    exact values (E31): if they change the key and make it literal,
    norm_num decides it, True DISCHARGED ('norm_num', entries used), False
    refused 'obligation-decided-false' (F1); a Refused inside the rewrite
    changes nothing. (5) The untrusted search proposes one certificate and
    the trusted checker decides it on the key as emitted, the exact values
    applied inside, so its tag already cites them. (6) The untrusted
    refuter: F2 or F3 refuses 'obligation-decided-false'. (7) ADMITTED with
    the tagger's tag (E24) and a reason."""
    # A key deeper than the stack (RecursionError) gets no rewrite, no
    # certificate and no refutation, so it is admitted: steps (4)-(6) only
    # ever withhold what they cannot decide.
    try:
        new, used = discharge.exact_values(key)
    except (Refused, RecursionError):
        new, used = key, ()
    said = FD.norm_num(new) if new != key else None
    tag = "norm_num"
    if said is None and new != key:  # E239: E206 after the exact values
        said, tag = FD.surd_decide(new), "norm_num_surd"
    if said:
        return Obligation(key, sources, DISCHARGED, (tag, used))
    if said is False:
        found = refute.exact_false(key)  # F1's message; the verdict is norm_num's
        raise Refused(DECIDED_FALSE, found.message if found else
                      f"{show(key)} is false: it reads {show(new)}")
    try:
        cert = search.propose(key)
    except RecursionError:
        cert = None
    tag = None if cert is None else discharge.check(key, cert)
    if tag is not None:
        return Obligation(key, sources, DISCHARGED, tag, None, _frozen(cert))
    # E249: E206 on a closed key no certificate closed, last before the
    # refuter, so a cite with its certificate keeps its place
    said = FD.surd_decide(new)
    if said:
        return Obligation(key, sources, DISCHARGED, ("norm_num_surd", used))
    if said is False:
        raise Refused(DECIDED_FALSE, f"{show(key)} is false: it reads "
                      f"{show(new)} (E206)")
    try:
        found = refute.refute(key, _owed)
    except RecursionError:
        found = None
    if found is not None:
        raise Refused(DECIDED_FALSE, found.message)
    tag = tagger.tag(key, gamma)
    try:
        empty = search.domain_empty(key)
    except RecursionError:
        empty = False
    reason = (REASON_EMPTY if empty else
              REASON_NONE if tag == ("none", ()) else REASON_REJECTED)
    return Obligation(key, sources, ADMITTED, tag, reason)


def _discharge_reg(key, sources, gamma):
    """REG_DISCHARGE_ORDER (E60): (2r-b) the untrusted search proposes one
    regularity certificate and the trusted checker decides it, DISCHARGED
    ('reg', cites) with the certificate; (2r-c) otherwise the untrusted
    refuter walks the C^0 sides of the term's derivation (E63), and one
    decided false refuses 'obligation-decided-false'; (2r-d) otherwise
    ADMITTED with the tagger's tag, REASON_NONE when it is ('none', ()),
    else REASON_REJECTED. A RecursionError withholds, as in _discharge."""
    try:
        cert = search.propose(key)
        tag = None if cert is None else discharge.check(key, cert)
        if tag is not None:
            return Obligation(key, sources, DISCHARGED, tag, None, _frozen(cert))
    except RecursionError:  # deeper than the stack: no certificate (§5)
        pass
    try:
        found = refute.refute_reg(key, _owed)
    except RecursionError:
        found = None
    if found is not None:
        raise Refused(DECIDED_FALSE, found.message)
    try:
        tag = tagger.tag(key, gamma)
    except RecursionError:
        tag = ("none", ())
    return Obligation(key, sources, ADMITTED, tag,
                      REASON_NONE if tag == ("none", ()) else REASON_REJECTED)


def _frozen(x):
    """A certificate as the tracker keeps it: every dict a read-only
    mapping and every list a tuple, all the way down, so no caller can
    change the certificate an obligation records. Iterative, so a
    certificate of any depth (a regularity derivation follows its term)
    freezes without exhausting the stack."""
    done, todo = [], [(x, False)]
    while todo:
        node, ready = todo.pop()
        if isinstance(node, dict):
            items = list(node.items())
            if not ready:
                todo.append((node, True))
                todo.extend((v, False) for _, v in reversed(items))
                continue
            vals = done[len(done) - len(items):] if items else []
            del done[len(done) - len(items):]
            done.append(MappingProxyType({k: v for (k, _), v in zip(items, vals)}))
        elif isinstance(node, (list, tuple)):
            if not ready:
                todo.append((node, True))
                todo.extend((v, False) for v in reversed(node))
                continue
            vals = done[len(done) - len(node):] if node else []
            del done[len(done) - len(node):]
            done.append(tuple(vals))
        else:
            done.append(node)
    return done[0]


def _emit_at(buf, prop, dom, anc, source, goal_dom, divisor=True):
    """prop at a position (E5). A key with no free variable has domain ()
    and uses no range. Any other holds the whole position domain, so each
    pending range there is decided first (_decided, outermost first, its
    order emitted, or 'orientation-undecided' before the key is), and the
    key is stated on the decided intervals."""
    key = with_domain(prop, dom)
    if key.dom:
        sub = {}
        key = with_domain(prop, _decided(sub, dom, anc, goal_dom))
        _emit(buf, key, source, goal_dom, divisor=divisor)
        for k, ob in sub.items():  # the orders after the key, as E4 had them
            buf[k] = _merged(buf.get(k), ob)
        return
    _emit(buf, key, source, goal_dom, divisor=divisor)


# E26 (a)'s natural-domain table lives in domains.py, the one datum the
# formers here and the regularity checker in discharge.py both read
# (p1_expected E61): `_owed` looks it up as domains.NATURAL_DOMAINS at call
# time, the seam the definedness mutations swap (ARCHITECTURE.md §7).


def _owed(s):
    """What the former at node s owes, as (prop, divisor) pairs: E6's
    Div(_, d) and Pow(d, n<0) give the divisor NonZero(d), RPow(b, _) gives
    b > 0, and E26's partial builtins give their NATURAL_DOMAINS items, none
    of which is a divisor (tan's cos u # 0 included). Every other node owes
    nothing. The propositions are not charged for their own formers (KEYING):
    their subterms were charged as part of s."""
    if isinstance(s, Div):
        return ((NonZero(s.b), True),)
    if isinstance(s, Pow) and s.n < 0:
        return ((NonZero(s.base), True),)
    if isinstance(s, RPow):
        return ((Rel(">", s.base, Num(0)), False),)
    if isinstance(s, Branch):  # E171: log, arg and sqrt[theta] owe w # 0
        return ((NonZero(s.arg), False),)
    if isinstance(s, App) and s.fn == "tanh" and sort_of(s.arg) == "C":
        # E175 (B2): over C, tanh w = sinh w / cosh w owes cosh w # 0
        return ((NonZero(App("cosh", s.arg)), False),)
    table = domains.NATURAL_DOMAINS
    if isinstance(s, App) and s.fn in table:
        return tuple((p, False) for p in table[s.fn](s.arg))
    return ()


def _charge_formers(buf, term, dom, goal_dom, anc=()):
    """E6 and E26 (a) for one term entering the proof at a position with
    domain `dom` and enclosures `anc`: each former's _owed propositions, with
    source 'former'. Positions inside an Integral's body get its range (and
    its orientation, when a key uses that range). Each divisor goes through
    E25 in _emit, and each key through E7.

    A seam (ARCHITECTURE.md §7): rewrite, int_subst and int_flip are its
    only callers that pass `anc`, by keyword, and the mutations
    rewrite_R_former_at_goal_domain and rewrite_R_former_on_ranges_only
    replace it in a child process that runs PROOFS and the case tables.
    Since E52 PROOFS holds P1.1-sheet, whose int_subst acts on a top-level
    Int of a goal with no domain, where both mutations charge what the rule
    charges (P1_1_SHEET_TRACES: N 5, no change).

    Then E64's formers, after every E6/E26 former of the term, in pre-order
    among themselves (FORMER_RULE, 'When'), so that no existing refusal
    changes its cause: a statable Int owes its integrand in C^0 on its
    range, and a D[x] e owes e in C^1 at its position domain."""
    walk = list(_positions(term, dom, anc))
    _e6_formers(buf, walk, goal_dom)
    _tree_formers(buf, walk, goal_dom)


def _e6_formers(buf, walk, goal_dom):
    """E6 and E26 (a): each node's _owed propositions at its position. A
    seam (ARCHITECTURE.md §7): the planted bug former_div_dropped replaces
    it."""
    for _, s, d, a in walk:
        for prop, divisor in _owed(s):
            _emit_at(buf, prop, d, a, "former", goal_dom, divisor)


def _tree_formers(buf, walk, goal_dom):
    """E64 (§18 Q23's formers), for the positions `walk` of one term, in
    pre-order: _int_former at each statable Integral, _d_former at each
    Deriv. An unstatable Int owes nothing (E65). A seam (ARCHITECTURE.md
    §7)."""
    body = {p: (d, a) for p, _, d, a in walk}
    for p, s, d, a in walk:
        if isinstance(s, Integral) and statable(s):
            bd, ba = body[p + ("body",)]
            _int_former(buf, s, bd, ba, goal_dom)
        elif isinstance(s, Deriv):
            _d_former(buf, s, d, a, goal_dom)


def _int_former(buf, it, body_dom, body_anc, goal_dom):
    """A statable Int[x = a .. b] f owes Reg(f, 0) on its body's position
    domain, P plus its range I (built by E56: the range's order is decided
    here, since this key uses it, and emitted; neither order refuses
    'orientation-undecided'). Continuity on a closed bounded interval gives
    Riemann integrability, so this is the statable, sufficient form of 'f
    integrable on [a, b]', and it is ftc's own f premise (E64). A seam
    (ARCHITECTURE.md §7)."""
    _emit_at(buf, Reg(it.body, 0), body_dom, body_anc, "former", goal_dom)


def _d_former(buf, dx, dom, anc, goal_dom):
    """D[x] e owes Reg(e, 1) at the node's own position domain P: e is C^1
    near every point of P, so D[x] e denotes there (E64). D[z] for a CVar
    z owes deriv's own side conditions instead, holomorphy's (E186). A
    seam (ARCHITECTURE.md §7)."""
    if any(type(n) is CVar and n.name == dx.var for n in DV._nodes(dx.body)):
        for key, _ in DV.deriv(dx.body, dx.var, ()).emissions:
            _emit_at(buf, key, dom, anc, "former", goal_dom)
        return
    _emit_at(buf, Reg(dx.body, 1), dom, anc, "former", goal_dom)


S_TRIG = "trig_norm"  # E88: a trig_norm instance's hypotheses
TRIG_MAX = 64  # the most instances a proposal may hold


def _trig_instances(lhs, rhs, facts):
    """E94: _trig_fence, total. Any RecursionError or Refused in it abandons
    the fallback."""
    try:
        return _trig_fence(lhs, rhs, facts)
    except (RecursionError, Refused):
        return None


def _trig_fence(lhs, rhs, facts):
    """E88: trig_norm's proposal as (entry name, inst, conclusion) triples,
    or None. The tactic is untrusted, so anything it returns that is not a
    list of at most TRIG_MAX (name, inst) pairs naming an ENTRIES equation
    and binding exactly its schema to terms with no MVar, no infinity, no
    Int or D node and no variable outside lhs and rhs, abandons the
    fallback, as does any exception it raises."""
    try:
        got = trig_norm.propose(lhs, rhs, tuple(facts))
    except Exception:  # noqa: BLE001 (untrusted: E88)
        return None
    if type(got) is not list or not got or len(got) > TRIG_MAX:
        return None
    names = fv(lhs) | fv(rhs)
    out = []
    for item in got:
        if type(item) is not tuple or len(item) != 2:
            return None
        name, inst = item
        e = ENTRIES.get(name) if type(name) is str else None
        if e is None or not (isinstance(e.statement, Rel)
                             and e.statement.op == "=="):
            return None
        if type(inst) is not dict or set(inst) != set(e.schema):
            return None
        for v in inst.values():
            if not isinstance(v, Term) or _unfit(v) or not fv(v) <= names:
                return None
        out.append((name, dict(inst), subst(e.statement, inst)))
    return out


def _unfit(t):
    """A term no instance may hold: an MVar, an infinity, an Int or a D."""
    if isinstance(t, (MVar, PosInf, NegInf, Integral, Deriv, CInt)):
        return True
    return any(_unfit(k) for _, k in children(t) if isinstance(k, Term))


def _check(check, lhs, rhs, minted, dom, goal_dom, buf, code, trig=False):
    """Run `ring` or `field` on lhs == rhs with the facts of the resolved
    `minted` records. Emit each returned divisor as NonZero at dom (source
    'field_div'), and for each fact the formers of its inst values (source
    'former', E6 and E26 (a)) and its hypotheses (source 'fact_hyp'), all at
    dom, so the result inherits what its facts owe: an instance built from
    ln(-1) is refuted here, as it would be anywhere else it entered, and an
    instance's tan u owes cos u # 0. field.NotEqual becomes
    Refused(code) carrying residual.residual_term(r), which is lhs − rhs
    (E14). A fact that is not an equation refuses 'field-fact-shape'."""
    facts = []
    for rec in minted:
        c = rec.conclusion
        if not (isinstance(c, Rel) and c.op == "=="):
            raise Refused("field-fact-shape", f"{show(c)} is not an equation")
        facts.append((c.lhs, c.rhs))
    if complexes.has_complex((lhs, rhs)):
        return _check_complex(check, lhs, rhs, minted, facts, dom, goal_dom,
                              buf, code, trig)
    extra = ()
    try:
        done = FD.ring(lhs, rhs) if check == "ring" else FD.field(lhs, rhs,
                                                                  facts)
    except FD.NotEqual as e:
        res = residual.residual_term(e.residual)
        refusal = Refused(code, f"{check} leaves lhs - rhs = {_brief(res)}",
                          res)
        # E88: trig_norm, a fallback after field fails and never before;
        # any failure of it is the original refusal
        inst = _trig_instances(lhs, rhs, facts) if trig and check == "field" \
            else None
        if inst is None:
            raise refusal from None
        try:
            done = FD.field(lhs, rhs, facts + [(c.lhs, c.rhs)
                                               for _, _, c in inst])
        except (FD.NotEqual, Refused, RecursionError):
            raise refusal from None
        extra = inst
    for d in done.divisors:
        _emit(buf, with_domain(NonZero(d), dom), "field_div", goal_dom)
    for rec in minted:
        for v in rec.inst:
            _charge_formers(buf, v, dom, goal_dom)
        for h in rec.conclusion.dom:
            _emit(buf, with_domain(h, dom), "fact_hyp", goal_dom)
    for _, inst, c in extra:
        for v in inst.values():
            _charge_formers(buf, v, dom, goal_dom)
        for h in c.dom:
            _emit(buf, with_domain(h, dom), S_TRIG, goal_dom)
    return tuple(dict.fromkeys(name for name, _, _ in extra))


def _check_complex(check, lhs, rhs, minted, facts, dom, goal_dom, buf, code,
                   trig=False):
    """E169: lhs == rhs over C is the real parts equal and the imaginary
    parts equal, each by ring or field; both checks' divisors are emitted.
    A fact holding a Complex term is refused (K1); a real fact is used on
    both parts. The residual is re + i*im of the parts' residuals. With
    trig, a part field fails takes E88's fallback on its own (E197)."""
    if complexes.has_complex(tuple(x for f in facts for x in f)):
        raise Refused("field-fact-shape", "a fact about complex terms is "
                      "not read by field yet (K1)")
    (a, b), (c, d) = complexes.split(lhs), complexes.split(rhs)
    R = complexes._real
    done, residuals, extra = [], [], []
    for x, y in ((R(a), R(c)), (R(b), R(d))):
        try:
            done.append(FD.ring(x, y) if check == "ring" else
                        FD.field(x, y, facts))
            residuals.append(None)
        except FD.NotEqual as e:
            inst = _trig_instances(x, y, facts) if trig and \
                check == "field" else None
            try:
                if inst is None:
                    raise FD.NotEqual(e.residual)
                done.append(FD.field(x, y, facts + [(c.lhs, c.rhs)
                                                    for _, _, c in inst]))
                residuals.append(None)
                extra.extend(inst)
            except (FD.NotEqual, Refused, RecursionError):
                residuals.append(residual.residual_term(e.residual))
    if any(r is not None for r in residuals):
        res = complexes.join(tuple(residuals))
        raise Refused(code, f"{check} leaves lhs - rhs = {_brief(res)}", res)
    for ok in done:
        for dv in ok.divisors:
            _emit(buf, with_domain(NonZero(dv), dom), "field_div", goal_dom)
    for rec in minted:
        for v in rec.inst:
            _charge_formers(buf, v, dom, goal_dom)
        for h in rec.conclusion.dom:
            _emit(buf, with_domain(h, dom), "fact_hyp", goal_dom)
    for _, inst, c in extra:
        for v in inst.values():
            _charge_formers(buf, v, dom, goal_dom)
        for h in c.dom:
            _emit(buf, with_domain(h, dom), S_TRIG, goal_dom)
    return tuple(dict.fromkeys(name for name, _, _ in extra))


# ---------------------------------------------------------------- moves
#
# Each move takes (state, args, minted facts, buffer) and returns (new goal,
# theorem, StepRecord extras). It changes nothing outside the buffer except
# `fact`, which registers its handle as its last act.

# Partial formers whose natural domain is not open (§6.9; REWRITE_RULE 9a).
_NOT_OPEN = frozenset(("sqrt", "asin", "acos", "acosh"))


def _open_in(h, x):
    """REWRITE_RULE step 9(a) for one proposition h that mentions x: strict
    (<, > or # 0), and no subterm mentioning x is an application of a
    _NOT_OPEN builtin, or a D or Int node. h is an entry's hypothesis or a
    former R owes (_owed), so a Rel or NonZero, never an interval."""
    if isinstance(h, NonZero):
        strict, sides = True, (h.e,)
    else:
        strict, sides = h.op in ("<", ">"), (h.lhs, h.rhs)
    return strict and not any(
        x in fv(s) and (isinstance(s, (Deriv, Integral))
                        or isinstance(s, App) and s.fn in _NOT_OPEN)
        for side in sides for s in _subterms(side))


def _no_trees_erased(lhs, inst, at):
    """REWRITE_RULE step 2a (E57, narrowed by E66 (3)): refuse
    'Int-or-D-not-normalisable' when any inst value, or the target `at`,
    holds an UNSTATABLE Integral (an infinite limit, or a limit holding an
    Int or D node), whichever branch step 3 takes. Step 3's tree branch,
    for a left side that is not an App (pyth's sum, pyth_cos's power),
    never normalises, and an entry whose right side drops a schema
    variable (pyth's 1) would erase the node. No rule may erase an Int or
    D node unless its definedness is owed (E57_PRINCIPLE): a statable Int
    or a D node in the target was owed where it entered, and R's are
    charged at step 10 (E64), so only an unstatable Int, whose convergence
    no rule states yet (E65), is refused. Both halves are tested, each alone (the suite
    calls this function directly, since under today's ENTRIES each half is
    redundant through the moves). `lhs`, the instantiated left side, is not
    read here: the seam's signature carries the branch so that the planted
    bug rewrite_tree_branch_skips_E57 can test it.

    A seam (ARCHITECTURE.md §7): rewrite calls it by this global name; the
    planted bug rewrite_tree_branch_skips_E57 and the BACKSTOPS case
    rewrite_closing_check_goal replace it in a child process."""
    for t in (*inst.values(), at):  # a CInt is never statable (E192, E199)
        if any(not statable(n) for n in trees(t)):
            raise Refused("Int-or-D-not-normalisable", f"{_brief(t)} holds an "
                          "improper or unstatable Int, which a rewrite could "
                          "erase (E57, E65)")


def _no_trees_in_limits(*limits):
    """SECOND_REVIEW_RULE (E57's principle, amended): an Integral or Deriv
    node in a limit of the Int that ftc, int_subst or int_flip acts on (or
    in int_subst's new lo and hi) refuses 'Int-or-D-not-normalisable',
    before anything is emitted and before any order is decided. Such a
    limit has no definedness condition the kernel can state, and F(b) -
    F(a), the endpoint images or the new integral would carry it into the
    goal. An infinite limit holds no node."""
    for t in limits:
        if isinstance(t, Term) and next(trees(t), None) is not None:
            raise Refused("Int-or-D-not-normalisable", f"the limit {_brief(t)} "
                          "holds an Int or D node, whose definedness no rule "
                          "can state (E57)")


def _rewrite(state, args, minted, buf):
    """REWRITE_RULE steps 1–11 with E57's step 2a, then check_goal on the
    new goal. That last check is a backstop: an inst value carrying an Int
    into a same-named Int's body is refused by step 2a (E57) and step 3's
    ring_nf (E26 (b)) first. The suite reaches it through the
    field.ring_equal and _no_trees_erased seams (ARCHITECTURE.md §7,
    BACKSTOPS), so call it only as written here.
    Returns (new goal, None, occurrences)."""
    at = args["at"]
    if args["entry"] == "parts":  # E170: T -> re T + i*im T, checked
        if args["inst"]:
            raise Refused("bad-args", "parts takes no instantiation")
        inst = {}
        lhs, (rhs, hyps) = at, _parts(at)
    else:
        e, inst = entries.resolve(args["entry"], args["inst"]) or (None, None)
        if e is None or e.statement.op != "==" or set(inst) != set(e.schema):
            raise Refused("bad-args", "rewrite takes an equation entry and "
                          "exactly its schema's variables")
        st = e.statement  # a Rel (entries._load); pi_pos is not an equation
        lhs, rhs = subst(st.lhs, inst), subst(st.rhs, inst)  # step 1
        hyps = [subst(h, inst) for h in e.hyps]
        for h in hyps:  # E175: a complex inst in an order hypothesis
            check_sorts(h)
    g = state.goal[0]
    sides = _sides(g)
    found = [(i, p, d, a) for i, side in enumerate(sides)  # step 2
             for p, s, d, a in _positions(side, g.dom) if s == at]
    if "occurrence" in args:
        k = args["occurrence"]
        found = found[k:k + 1] if k >= 0 else []
    if not found:
        raise Refused("rewrite-target-not-found",
                      f"{show(at)} is not in the goal's non-?A side")
    _no_trees_erased(lhs, inst, at)  # step 2a (E57)
    if isinstance(lhs, App):  # steps 3-5: congruence up to ring_nf
        ok = (isinstance(at, App) and at.fn == lhs.fn
              and FD.ring_equal(lhs.arg, at.arg))
    elif isinstance(lhs, RPow):  # E163: a real power, through both fields
        ok = (isinstance(at, RPow) and FD.ring_equal(lhs.base, at.base)
              and FD.ring_equal(lhs.exp, at.exp))
    elif isinstance(lhs, Branch):  # E172: a branch, through its argument
        ok = (isinstance(at, Branch) and at.fn == lhs.fn
              and at.theta == lhs.theta and FD.ring_equal(lhs.arg, at.arg))
    else:
        ok = lhs == at
    if not ok:
        raise Refused("rewrite-lhs-mismatch", f"{show(at)} does not match "
                      f"{show(lhs)} up to ring")
    names = frozenset().union(*map(fv, inst.values()))
    for _, _, _, a in found:  # step 6
        out = names - fv(g) - {x.integral.var for x in a
                               if isinstance(x, _IntScope)}
        if out:
            raise Refused("rewrite-scope", f"{', '.join(sorted(out))} is not "
                          "in scope at the target")
    # Step 9 tests H and every proposition step 10 charges from R, formers
    # nested in a divisor included: both bound the equation's domain. (a)
    # asks each of them for openness in x; (b) refuses a range mentioning x
    # between D[x] and the occurrence whenever any of them is owed there,
    # since each is emitted on that closed, x-dependent range.
    bounds = hyps + [p for s in _subterms(rhs) for p, _ in _owed(s)]
    # E66 (3): the Reg formers step 10 charges from R's statable Ints and D
    # nodes (E64). A Reg is never open, so one whose proposition or domain
    # (the node's own limits included) mentions x is not open in x
    regs = [n for n in _subterms(rhs) if isinstance(n, Deriv)
            or isinstance(n, Integral) and statable(n)]
    for _, _, _, a in found:  # step 9, for each D[x] above the occurrence
        for i, dx in enumerate(a):
            if isinstance(dx, _IntScope):
                continue
            x = dx.var
            through = [y.integral for y in a[i + 1:]
                       if isinstance(y, _IntScope)]
            if (any(x in fv(h) and not _open_in(h, x) for h in bounds)
                    or any(x in fv(n) for n in regs) or (bounds or regs)
                    and any(x in fv(y.lo) | fv(y.hi) for y in through)):
                raise Refused("rewrite-under-D-needs-open-domain",
                              f"under D[{x}] the equation's domain in {x} "
                              "must be open (§6.1 rev 9)")
    for _, _, d, a in found:  # steps 7, 8 and 10
        for h in hyps:
            _emit_at(buf, h, d, a, "rewrite_hyp", g.dom)
        _charge_formers(buf, rhs, d, g.dom, anc=a)
    new = list(sides)  # step 11
    for i, p, _, _ in found:
        new[i] = _put(new[i], p, rhs)
    goal = (replace(g, lhs=new[0], rhs=new[1] if len(new) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"occurrences": len(found)}


def _parts(at):
    """E170: (re T + i*im T, the hypotheses it owes) for `rewrite parts at
    T`. split is trusted; the two parts are offered in field's normal form
    by the untrusted residual printer, and each offer is kept only when
    the trusted field proves it equal to split's part, its divisors then
    owed as hypotheses. An offer that fails falls back to split's raw
    part, which owes nothing beyond T's own formers."""
    if not complexes.has_complex(at):
        raise Refused("bad-args", f"parts: {show(at)} holds no complex term")
    raw = complexes.split(at)
    parts, hyps = [], []
    for x in raw:
        if x is None:
            parts.append(None)
            continue
        try:
            num, den, atoms = FD.field_parts(_tidy(x))
            offer = residual.residual_term(_Parts(num, den, atoms))
            ok = FD.field(x, offer)
            parts.append(offer)
            hyps.extend(NonZero(d) for d in ok.divisors)
        except (FD.NotEqual, Refused, RecursionError):
            parts.append(x)
    parts = [None if p is not None and FD.ring_is_zero(p) else p
             for p in parts]
    return complexes.join(tuple(parts)), list(dict.fromkeys(hyps))


def _tidy(t):
    """t with each function's argument in field's normal form, innermost
    first, so that an offer reads cos pi, not cos(1*pi). Untrusted: the
    offer it shapes is checked by field (_parts)."""
    if isinstance(t, (App, Branch)):
        try:
            num, den, atoms = FD.field_parts(_tidy(t.arg))
            return replace(t, arg=residual.residual_term(_Parts(num, den,
                                                                atoms)))
        except (Refused, RecursionError):
            return t
    kids = {n: _tidy(c) for n, c in children(t) if isinstance(c, Term)}
    return replace(t, **kids) if kids and not isinstance(t, Call) else t


class _Parts:
    """field_parts' triple, read by residual.residual_term."""
    __slots__ = ("num", "den", "atoms")

    def __init__(self, num, den, atoms):
        self.num, self.den, self.atoms = num, den, atoms


def _fact(state, args, minted, buf):
    """E10: mint and register a Handle for ENTRIES[entry].statement[inst],
    hypotheses kept as its domain, and the inst values beside it. Emits
    nothing: whoever uses the handle inherits the hypotheses and the inst
    values' formers (E6, E26 (a)), charged by _check at that step's domain.
    The statement's own formers are not re-charged: over schema variables
    each is the entry's hypothesis or always true, and the library
    statement is trusted (§6.8)."""
    e, inst = entries.resolve(args["entry"], args["inst"]) or (None, None)
    if e is None or set(inst) != set(e.schema):
        raise Refused("bad-args", "fact takes an entry and exactly its "
                      "schema's variables")
    conclusion = subst(e.statement, inst)
    h = Handle(next(_IDS), state.lineage)
    _MINTED[h.id] = _Minted(h, state.lineage, conclusion, e.name,
                            tuple(inst[k] for k in e.schema))
    return state.goal, None, {"handle": h}


def _ftc(state, args, minted, buf):
    """E9 (i)–(vi) with §6.4's four premises. Returns (new goal, None,
    deriv's trace and output). The range is E56's (_range): the premises
    are on [min, max] and (min, max) of the limits, the order discharge
    proved, and the new goal is F(b) - F(a) with the limits as written,
    which holds for either order (§5.1).

    Everything that can refuse runs in the order ARCHITECTURE.md §4 gives:
    the orientation, F's formers, F's C^0 premise (a Reg, decided by
    regularity or refused by E63), deriv, the check, the other premises,
    the new goal's formers,
    then check_goal on the new goal. That last check is the only guard
    against a variable free in F that the goal's rhs binds
    (D11-bound-and-free). An Int inside F, whose binder could be free in
    the rhs, is refused earlier by deriv (E26 (b)).
    The emissions are buffered in §6.4's premise order, so the tracker lists
    the four premises together."""
    g = state.goal[0]
    G, it, F, check = g.dom, g.lhs, args["F"], args["check"]
    nested = "occurrence" in args  # E73
    if nested:
        side, path, it, P, anc = _ftc_select(g, args["occurrence"])
    elif not isinstance(it, Integral):
        raise Refused("ftc-no-integral", "ftc needs an Int as the goal's lhs")
    else:
        P = G
    if any(isinstance(e, (PosInf, NegInf)) for e in (it.lo, it.hi)):
        raise Refused("ftc-infinite-endpoint", "F(oo) is not a term (§5.1); "
                      "an infinite range needs int_improper")
    _open_end(it, "ftc")
    _no_trees_in_limits(it.lo, it.hi)  # SECOND_REVIEW_RULE
    if nested:
        _ftc_scope(g, anc, it.var, F)  # E84
        _subst_under_D(anc, it, (F,))  # E73, E48
        P = _decided(buf, P, anc, G)
    x, f = it.var, it.body
    closed, orient = _range(it, P)
    on_ab = P + (closed,)  # [a, b]
    on_open = P + (Interval(x, closed.lo, False, closed.hi, False),)  # C¹'s
    on_deriv = P + (derivative_domain(closed),)  # (a, b), through the seam
    if orient is not None:
        _emit(buf, orient, "orient", G)
    _ftc_F_formers(buf, F, on_ab, G)
    # F's C^0 premise is decided here, before deriv (REG_BAD_MOVES
    # ftc_F_across_pole: an F undefined inside [a, b] is refused by E63
    # through it even when its formers are not charged), and listed in
    # §6.4's premise order below
    pre = {}
    _emit(pre, with_domain(Reg(F, 0), on_ab), "ftc_F_C0", G)
    later = {}
    d = DV.deriv(F, x, on_deriv)
    for key, source in d.emissions:
        _emit(later, key, source, G)
    trig = _check(check, d.output, f, minted, on_deriv, G, later,
                  "ftc-check-failed", trig=True)
    cites = tuple(dict.fromkeys(
        (*(rec.entry for rec in minted), *trig)))
    for ob in pre.values():
        buf[ob.key] = _merged(buf.get(ob.key), ob)
    _emit(buf, with_domain(Reg(F, 1), on_open), "ftc_F_C1", G)
    _emit(buf, with_domain(Rel("==", Deriv(x, F), f), on_deriv), "ftc_D", G,
          ("deriv+" + check, cites))
    _emit(buf, with_domain(Reg(f, 0), on_ab), "ftc_f_C0", G)
    for ob in later.values():
        buf[ob.key] = _merged(buf.get(ob.key), ob)
    lhs = Add(subst(F, {x: it.hi}), Neg(subst(F, {x: it.lo})))  # F(b) - F(a)
    if nested:  # E73: in place, the new term's formers at its position
        sides = list(_sides(g))
        sides[side] = _put(sides[side], path, lhs)
        _charge_formers(buf, lhs, P, G, anc=anc)
        goal = (replace(g, lhs=sides[0],
                        rhs=sides[1] if len(sides) > 1 else g.rhs),)
        check_goal(goal)
        return goal, None, {"trace": d.trace, "output": d.output}
    goal = (replace(g, lhs=lhs),)
    for side in _sides(goal[0]):
        _charge_formers(buf, side, G, G)
    check_goal(goal)
    return goal, None, {"trace": d.trace, "output": d.output}


def _ftc_scope(g, anc, x, F):
    """E84: F in scope at the selected Int's position, plus its variable."""
    try:
        _subst_scope(g, anc, [("F", F, {x})])
    except Refused as r:
        if r.code != "int-subst-scope":
            raise
        raise Refused("ftc-scope", r.message) from None


def _ftc_select(g, k):
    """E73: int_flip's selector at occurrence k, with ftc's code."""
    try:
        return _flip_select(g, k)
    except Refused as r:
        raise Refused("ftc-no-integral", r.message) from None


def _ftc_F_formers(buf, F, on_ab, G):
    """E9 (ii): F's formers on [a, b]. A seam (ARCHITECTURE.md §7): the
    planted bug ftc_no_F_formers replaces it, and E63 then refuses F's own
    C^0 premise at the same point (REG_BAD_MOVES ftc_F_across_pole)."""
    _charge_formers(buf, F, on_ab, G)


def _holds_infinity(t):
    """An Int limit below t is oo or -oo (close's rule for its value)."""
    return any(isinstance(k, (PosInf, NegInf, Open)) for s in _subterms(t)
               for _, k in children(s))  # E231: a marked end too


def _close(state, args, minted, buf):
    """§9, E19, E23: refl behind the scope check and the whitelist, then
    check_goal on the theorem (D5-uncalled when the value names a symbol
    the original calls). Returns (None, the theorem instantiate(original,
    value), no extras)."""
    g, v = state.goal[0], args["value"]
    if not isinstance(g.rhs, MVar):
        raise Refused("close-no-mvar", "close needs ?A as the goal's rhs")
    # Trusted, not left to schema.py: no obligation charges an improper
    # integral's convergence, so a lax whitelist must not admit one.
    if _holds_infinity(v):
        raise Refused("bad-args", "an answer cannot mention oo")
    clash = fv(v) & bv(state.original)
    if clash:
        raise Refused("close-scope-bound-variable", f"?A may not mention "
                      f"{', '.join(sorted(clash))}, bound in the goal (§9)")
    if not schema.closed_ok(v):
        raise Refused("close-schema-not-closed", f"{show(v)} is not in the "
                      "closed schema (§9)")
    _charge_formers(buf, v, g.dom, g.dom)
    _check(args["check"], g.lhs, v, minted, g.dom, g.dom, buf,
           "close-check-failed")
    theorem = instantiate(state.original, v)
    check_goal(theorem)
    # E27, untrusted, and LAST: every refusal above wins, so
    # 'close-not-evaluated' means right value, unevaluated form. Every goal
    # carries the `closed` schema, the only one there is (E23).
    schema.check_evaluated(v)
    return None, theorem, {}


# ---------------------------------------------------------------- int_subst
#
# p1_expected's INT_SUBST_RULE (DESIGN.md §6.4, E36-E49), step by step. Each
# rule a planted bug removes is its own function, looked up by its global
# name at call time (ARCHITECTURE.md §7): _select, _fresh, _subst_under_D,
# _old_range, _new_orientation, _sub_formers, _subst_deriv, _reverse_check,
# _endpoint, _forward_premises, _reverse_premises, _new_integrand and
# _new_integral.

S_SUBST_LO, S_SUBST_HI = "int_subst_lo", "int_subst_hi"
S_SUBST_C1, S_SUBST_C0 = "int_subst_phi_C1", "int_subst_f_C0"
S_SUBST_INT = "int_subst_integrand"


def _select(g, var, k):
    """Step 2 (E48): the Integral nodes of the non-?A side(s), in
    REWRITE_RULE's pre-order; the k-th, or with no k the one binding var.
    Returns (side index, path, the Int, its position domain P, anc)."""
    ints = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
            for p, s, d, a in _positions(side, g.dom) if isinstance(s, Integral)]
    if k is not None:
        if k >= len(ints):
            raise Refused("int-subst-no-integral",
                          f"the goal holds no integral at occurrence {k}")
        if ints[k][2].var != var:
            raise Refused("int-subst-wrong-variable", f"the integral is over "
                          f"{ints[k][2].var}, not {var}")
        return ints[k]
    over = [x for x in ints if x[2].var == var]
    if not over:
        if ints:
            raise Refused("int-subst-wrong-variable",
                          f"no integral in the goal is over {var}")
        raise Refused("int-subst-no-integral", "the goal holds no integral")
    if len(over) > 1:
        raise Refused("int-subst-ambiguous", f"{len(over)} integrals are over "
                      f"{var}; give an occurrence")
    return over[0]


def _fresh(goal, v):
    """Step 4 (E42): new_var occurs nowhere in the goal, free or bound."""
    if v in fv(goal) | bv(goal):
        raise Refused("int-subst-not-fresh", f"{v} already occurs in the goal; "
                      "choose a fresh variable")


def _subst_scope(g, anc, parts):
    """Step 5 (E42, E48): each (part, term, extra names) has its free
    variables in scope at the position (the goal's free names and the
    enclosing Ints' binders) plus the extra ones."""
    scope = fv(g) | {a.integral.var for a in anc if isinstance(a, _IntScope)}
    for part, t, extra in parts:
        out = sorted(fv(t) - scope - extra)
        if out:
            raise Refused("int-subst-scope", f"{part} {show(t)} mentions "
                          f"{out[0]}, which is not in scope")


def _subst_under_D(anc, it, terms):
    """Step 6 (E48), REWRITE_RULE step 9 at the position: below a D[y], y
    may occur neither in the selected Int (limits, body), nor in the args'
    terms, nor in a limit of an Int between the D[y] and the position."""
    for i, dx in enumerate(anc):
        if isinstance(dx, _IntScope):
            continue
        y = dx.var
        through = [a.integral for a in anc[i + 1:] if isinstance(a, _IntScope)]
        if (any(y in fv(t) for t in (it, *terms))
                or any(y in fv(j.lo) | fv(j.hi) for j in through)):
            raise Refused("rewrite-under-D-needs-open-domain",
                          f"under D[{y}] the equation's domain in {y} must be "
                          "open (§6.1 rev 9)")


def _new_orientation(buf, v, lo, hi, P, G):
    """Step 8: (flip, I'), the new range by E56 (_range_of at P). Two
    rational literals are ordered, owing nothing, and kept. Otherwise the
    order discharge proves is emitted (source 'orient'): lo <= hi keeps the
    limits, hi <= lo flips the new integral (E46's form, kept as a choice
    since E56); neither refuses 'orientation-undecided'."""
    new_range, orient = _range_of(v, lo, hi, P)
    if orient is None:
        return False, new_range
    _emit(buf, orient, "orient", G)
    return new_range.lo != lo, new_range


def _subst_deriv(sub, x, D):
    """Step 10 (E38): deriv on the closed range, whose side conditions are
    therefore owed at its ends."""
    return DV.deriv(sub, x, D)


def _reverse_check(check, body, Fg, dg, f, minted, D, G, buf):
    """Step 11 (E45): body == Fg * g' at D by `check`, recorded discharged
    ('deriv+' + check, the facts' entries), certificate None."""
    rhs = Mul(Fg, dg)
    try:
        _check(check, body, rhs, minted, D, G, buf, "int-subst-check-failed")
    except Refused as r:
        if r.code != "int-subst-check-failed":
            raise
        raise Refused(r.code, "the integrand is not f(g(x))*g'(x) for f := "
                      f"{_brief(f)}", r.residual) from None
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    _emit(buf, with_domain(Rel("==", body, rhs), D), S_SUBST_INT, G,
          ("deriv+" + check, cites))


def _endpoint(check, image, limit, end, source, minted, P, G, buf):
    """Step 12 (E39): image == limit at P, after the exact values (E31), by
    `check`; recorded as written, discharged (check, the exact values'
    entries then the facts'), never admitted and never refuted."""
    eq = with_domain(Rel("==", image, limit), P)
    rewritten, used = discharge.exact_values(eq)
    try:
        _check(check, rewritten.lhs, rewritten.rhs, minted, P, G, buf,
               "int-subst-endpoint-mismatch")
    except Refused as r:
        if r.code != "int-subst-endpoint-mismatch":
            raise
        raise Refused(r.code, f"{_brief(image)} == {_brief(limit)} fails at the "
                      f"{end} limit", r.residual) from None
    cites = tuple(dict.fromkeys(used + tuple(rec.entry for rec in minted)))
    _emit(buf, eq, source, G, (check, cites))


def _old_range(buf, it, P, G):
    """Step 8, reverse mode: the old range I by E56 (_range), owing the
    order discharge proved at P when its ends are not two literals, since
    the premises use I; neither order refuses 'orientation-undecided'."""
    old, orient = _range(it, P)
    if orient is not None:
        _emit(buf, orient, "orient", G)
    return old


def _sub_formers(buf, sub, Fg, D, G, anc):
    """Step 9: the substitution's formers on the closed range D, then, in
    reverse mode, f(g(x))'s: phi (or g) is defined on the whole range, ends
    included, which makes the endpoint images defined (E39, E45)."""
    _charge_formers(buf, sub, D, G, anc=anc)
    if Fg is not None:
        _charge_formers(buf, Fg, D, G, anc=anc)


def _forward_premises(sub, F, D, it, P):
    """Step 13 (E38): phi in C^1 and the composed f(phi(t)) in C^0, both on
    the new closed range (§6.4, §11.1's correction)."""
    return [(with_domain(Reg(sub, 1), D), S_SUBST_C1),
            (with_domain(Reg(F, 0), D), S_SUBST_C0)]


def _reverse_premises(sub, Fg, D, f, v, lo, hi, P):
    """Step 13 (E45): g in C^1 and f(g(x)) in C^0, both on the old closed
    range, so no image of g is stated and g may be non-monotone."""
    return [(with_domain(Reg(sub, 1), D), S_SUBST_C1),
            (with_domain(Reg(Fg, 0), D), S_SUBST_C0)]


def _new_integrand(F, dphi):
    """Step 14, forward: f(phi(t)) * phi'(t), phi' as deriv gave it (E41)."""
    return Mul(F, dphi)


def _new_integral(v, lo, hi, body, flip):
    """Step 14: Int[v = lo .. hi] body, limits as given (E40), or flipped,
    Int[v = hi .. lo] -body, on a discharged hi <= lo (E46, §5.1)."""
    return Integral(v, hi, lo, Neg(body)) if flip else Integral(v, lo, hi, body)


def _int_subst(state, args, minted, buf):
    """INT_SUBST_RULE steps 2-15, forward (x := sub over new_var) or
    reverse (new_var := sub, the learner's f). Returns (new goal, None,
    deriv's trace and output). Everything that can refuse runs in the
    rule's order, and every emission goes through _emit."""
    g = state.goal[0]
    G, reverse = g.dom, args.get("mode") == "reverse"
    var, sub, v, lo, hi = (args[k] for k in ("var", "sub", "new_var", "lo", "hi"))
    check, f = args["check"], args.get("f")
    side, path, it, P, anc = _select(g, var, args.get("occurrence"))  # step 2
    a, b, body = it.lo, it.hi, it.body
    _open_end(it, "int_subst")
    for end in (a, b):  # step 3
        if isinstance(end, (PosInf, NegInf)):
            raise Refused("int-subst-infinite-endpoint", "int_subst needs finite "
                          f"limits, and {'oo' if isinstance(end, PosInf) else '-oo'}"
                          " is not (int_improper is the route)")
    _no_trees_in_limits(a, b, lo, hi)  # SECOND_REVIEW_RULE, after step 3
    _fresh(state.goal, v)  # step 4
    parts = ([("the substitution", sub, {var}), ("the new integrand", f, {v})]
             if reverse else [("the substitution", sub, {v})])
    _subst_scope(g, anc, parts + [("the lower limit", lo, set()),
                                  ("the upper limit", hi, set())])  # step 5
    _subst_under_D(anc, it, (sub, lo, hi) + ((f,) if reverse else ()))  # step 6
    if reverse:  # step 7: the images and the composition, by terms.subst
        Fg = subst(f, {v: sub})
        eqs = ((subst(sub, {var: a}), lo), (subst(sub, {var: b}), hi))
    else:
        F = subst(body, {var: sub})
        eqs = ((subst(sub, {v: lo}), a), (subst(sub, {v: hi}), b))
    # step 8, first (E56_AMENDMENTS): every key below is at P or a domain
    # extending it, so P's enclosing ranges are decided now, outermost first
    P = _decided(buf, P, anc, G)
    if reverse:  # step 8: the old range, owing its orientation
        old = _old_range(buf, it, P, G)
    for t in (lo, hi):
        _charge_formers(buf, t, P, G, anc=anc)
    flip, new_range = _new_orientation(buf, v, lo, hi, P, G)
    D = P + ((old,) if reverse else (new_range,))
    _sub_formers(buf, sub, Fg if reverse else None, D, G, anc)  # step 9
    d = _subst_deriv(sub, var if reverse else v, D)  # step 10
    for key, source in d.emissions:
        _emit(buf, key, source, G)
    if reverse:  # step 11
        _reverse_check(check, body, Fg, d.output, f, minted, D, G, buf)
    for (image, limit), end, source in zip(eqs, ("lower", "upper"),
                                           (S_SUBST_LO, S_SUBST_HI)):
        _endpoint(check, image, limit, end, source, minted, P, G, buf)  # step 12
    premises = (_reverse_premises(sub, Fg, D, f, v, lo, hi, P) if reverse
                else _forward_premises(sub, F, D, it, P))
    for key, source in premises:  # step 13
        _emit(buf, key, source, G)
    new_body = f if reverse else _new_integrand(F, d.output)  # step 14
    new = _new_integral(v, lo, hi, new_body, flip)
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, G, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"trace": d.trace, "output": d.output}


# ---------------------------------------------------------------- int_flip
#
# p1_expected's INT_FLIP_RULE (E51): §5.1's reversed integral with pointwise
# linearity, Int[x = a .. b] f == Int[x = b .. a] -(f), for every a and b, so
# the step owes no order of its own and has no premise. Its rule functions
# are seams like int_subst's: _flip_select, _flip_under_D and _flipped.

def _flip_select(g, k):
    """Step 2: int_subst's selector (E48) without a variable. The Integral
    nodes of the non-?A side(s) in REWRITE_RULE's pre-order; the k-th, or
    with no k the only one. Returns (side index, path, the Int, its
    position domain P, anc)."""
    ints = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
            for p, s, d, a in _positions(side, g.dom) if isinstance(s, Integral)]
    if k is not None:
        if k >= len(ints):
            raise Refused("int-flip-no-integral",
                          f"the goal holds no integral at occurrence {k}")
        return ints[k]
    if not ints:
        raise Refused("int-flip-no-integral", "the goal holds no integral")
    if len(ints) > 1:
        raise Refused("int-flip-ambiguous", f"{len(ints)} integrals in the "
                      "goal; give an occurrence")
    return ints[0]


def _flip_under_D(anc, it):
    """Step 3: E48's D[y] test for the selected Int, whose new closed range
    step 4's keys may be charged on."""
    _subst_under_D(anc, it, ())


def _flipped(it):
    """Step 4: Int[x = b .. a] -(f) for Int[x = a .. b] f."""
    return Integral(it.var, it.hi, it.lo, Neg(it.body))


def _int_flip(state, args, minted, buf):
    """INT_FLIP_RULE steps 2-4: the selected Int replaced by its flip, whose
    formers are charged as a new term's at its position (its limits at P,
    its body on its own range, built by E56 with its orientation when a
    key uses it), then check_goal. Returns (new goal, None, no extras)."""
    g = state.goal[0]
    side, path, it, P, anc = _flip_select(g, args.get("occurrence"))  # step 2
    _open_end(it, "int_flip")
    _no_trees_in_limits(it.lo, it.hi)  # SECOND_REVIEW_RULE
    _flip_under_D(anc, it)  # step 3
    new = _flipped(it)  # step 4
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, g.dom, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


# ---------------------------------------------------------------- cint_param
#
# p1_expected E191: a contour integral is defined by its parametrisation.

S_CINT_JOIN, S_CINT_C1 = "cint_join", "cint_path_C1"


def _cint_select(g, k):
    """The CInt nodes of the non-?A side(s), pre-order; the k-th, or the
    only one. Returns (side index, path, the CInt, P, anc)."""
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom) if isinstance(s, CInt)]
    if k is not None:
        if k >= len(found):
            raise Refused("cint-no-integral", f"the goal holds no contour "
                          f"integral at occurrence {k}")
        return found[k]
    if not found:
        raise Refused("cint-no-integral", "the goal holds no contour integral")
    if len(found) > 1:
        raise Refused("cint-ambiguous", f"{len(found)} contour integrals in "
                      "the goal; give an occurrence")
    return found[0]


def _ends(g, t):
    """(start, end) of a path."""
    k = type(g)
    if k is Seg:
        return g.a, g.b
    if k is Arc:
        at = lambda u: Add(g.c, Mul(g.r, App("exp", Mul(Const("i"), u))))
        return at(g.t1), at(g.t2)
    if k is PathP:
        return subst(g.phi, {g.var: g.lo}), subst(g.phi, {g.var: g.hi})
    if k is Rev:
        a, b = _ends(g.g, t)
        return b, a
    return _ends(g.a, t)[0], _ends(g.b, t)[1]  # Join


def _plus(a, b):
    return b if a == Num(0) else a if b == Num(0) else Add(a, b)


def _times(a, b):
    return b if a == Num(1) else a if b == Num(1) else Mul(a, b)


def _minus(b, a):
    return b if a == Num(0) else Add(b, Neg(a))


def _path_data(g):
    """E199: the terms a path is built from, outside any path[s] binder:
    seg's ends, arc's centre, radius and angles, path[s]'s bounds (its phi
    is owed by Reg(phi, 1) on its range)."""
    k = type(g)
    if k is Seg:
        return [g.a, g.b]
    if k is Arc:
        return [g.c, g.r, g.t1, g.t2]
    if k is PathP:
        return [g.lo, g.hi]
    if k is Rev:
        return _path_data(g.g)
    return _path_data(g.a) + _path_data(g.b)  # Join


def _pieces(g, t, sign, out, joins):
    """Each piece of g as (sign, lo, hi, phi(t), phi'(t), the C^1 owed or
    None), and each join's end == start equation, in order."""
    k = type(g)
    if k is Seg:
        d = _minus(g.b, g.a)  # E195: built without 0 + or 1* padding
        out.append((sign, Num(0), Num(1), _plus(g.a, _times(Var(t), d)), d,
                    None))
    elif k is Arc:
        e = App("exp", Mul(Const("i"), Var(t)))
        out.append((sign, g.t1, g.t2, _plus(g.c, _times(g.r, e)),
                    _times(_times(Const("i"), g.r), e), None))
    elif k is PathP:
        phi = subst(g.phi, {g.var: Var(t)})
        d = DV.deriv(phi, t, ())
        out.append((sign, g.lo, g.hi, phi, d.output, (phi, d)))
    elif k is Rev:
        _pieces(g.g, t, -sign, out, joins)
    else:  # Join: g.a then g.b, owing a's end == b's start (E203)
        joins.extend(_meets(_end_info(g.a, True), _end_info(g.b, False)))
        _pieces(g.a, t, sign, out, joins)
        _pieces(g.b, t, sign, out, joins)


def _cint_param(state, args, minted, buf):
    """E191: the selected CInt replaced by the sum of its pieces'
    integrals, Int[t = lo .. hi] f(phi(t))*phi'(t), negated under rev;
    each join owes its end == start; path[s]'s phi owes C^1 on its range
    and deriv's sides; the new term's formers are charged as any new
    term's (E64: the integrand C^0 on each piece's range), then
    check_goal."""
    g = state.goal[0]
    side, path, ci, P, anc = _cint_select(g, args.get("occurrence"))
    taken = fv(g) | bv(g) | fv(ci.path) | bv(ci.body)
    t = next(n for n in itertools.chain(
        ("t",), (f"t_{j}" for j in itertools.count(1))) if n not in taken)
    pieces, joins = [], []
    _pieces(ci.path, t, 1, pieces, joins)
    for j in joins:
        _owe(buf, j, S_CINT_JOIN, P, anc, g.dom)
    for x in _path_data(ci.path):  # E199: the path's own data is owed
        _charge_formers(buf, x, P, g.dom, anc=anc)
    new = None
    for sign, lo, hi, phi, dphi, owe in pieces:
        f = _times(subst(ci.body, {ci.var: phi}), dphi)
        # E199: rev's sign inside the integrand, so ftc can take the Int
        it = Integral(t, lo, hi, f if sign > 0 else Neg(f))
        new = it if new is None else Add(new, it)
        if owe is not None:  # path[s]: phi in C^1 and deriv's sides
            rng = _range(it, P)[0]
            _emit_at(buf, Reg(owe[0], 1), P + (rng,), anc, S_CINT_C1, g.dom)
            for key, _ in owe[1].emissions:
                _emit_at(buf, key, P + (rng,), anc, S_CINT_C1, g.dom)
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, g.dom, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


# ---------------------------------------------------------------- residues
#
# p1_expected E200-E208: COMPLEX.md Z8, Cauchy's theorem and the residue
# theorem as one rule. U is open and convex (E201), so star-shaped; every
# hypothesis is owed (E202); the finders (roots.py, the branch choices
# below) are untrusted, and each thing they find is checked or owed.

S_RES_CLOSED, S_RES_IN_U = "residues_closed", "residues_path_in_U"
S_RES_HOLO, S_RES_ROOTS = "residues_holomorphic", "residues_roots"
S_RES_WIND, S_RES_POLE = "residues_wind", "residues_pole"
SQRT_FACT = "sqrt_sq_val"


def _pi_multiple(t):
    """q when t is ring-equal to q*pi for a rational q (0 included), else
    None."""
    try:
        (p,), atoms = FD.ring_polys([t])
    except Refused:
        return None
    if not p:
        return Fraction(0)
    if len(p) != 1:
        return None
    (mono, q), = p.items()
    if len(mono) != 1 or mono[0][1] != 1 or atoms[mono[0][0]] != Const("pi"):
        return None
    return Fraction(q)


def _end_info(g, last):
    """g's start (last False) or end: ('arc', c, r, angle) when it is an
    arc's, else ('pt', the point)."""
    k = type(g)
    if k is Arc:
        return ("arc", g.c, g.r, g.t2 if last else g.t1)
    if k is Rev:
        return _end_info(g.g, not last)
    if k is Join:
        return _end_info(g.b if last else g.a, last)
    s, e = _ends(g, None)
    return ("pt", e if last else s)


def _cos_sin(q):
    """(cos, sin) of q*pi exactly when q*pi is a multiple of pi/6 or pi/4,
    else None (E211); entries.cos_sin_table since E239."""
    return entries.cos_sin_table(q)


def _point(info):
    if info[0] == "arc":
        _, c, r, s = info
        q = _pi_multiple(s)
        cs = None if q is None else _cos_sin(q)
        if cs is None:
            return Add(c, Mul(r, App("exp", Mul(Const("i"), s))))
        cos, sin = cs  # E211: exact, so a closed end decides
        w = cos if sin == Num(0) else _plus(cos, _times(sin, Const("i")))
        return _plus(c, _times(r, w))
    return info[1]


def _joins(g):
    """(end, start) at each ++ of g, rev's included (E211)."""
    if type(g) is Rev:
        return [(s, e) for e, s in _joins(g.g)]
    if type(g) is Join:
        return (_joins(g.a) + [(_end_info(g.a, True), _end_info(g.b, False))]
                + _joins(g.b))
    return []


def _meets(end, start):
    """E203: the equations that make `end` meet `start`. Two arc ends meet
    when their centres and radii are equal and their angles differ by
    2*pi*k; any other pair by E191's end == start."""
    if end[0] == start[0] == "arc":
        _, c1, r1, s1 = end
        _, c2, r2, s2 = start
        q1, q2 = _pi_multiple(s1), _pi_multiple(s2)
        # E211: only the same circle, else the points are compared
        if q1 is not None and q2 is not None and c1 == c2 and r1 == r2 \
                and ((q1 - q2) / 2).denominator == 1:
            k = int((q1 - q2) / 2)
            out = []
            if s1 != s2:
                turn = Mul(Num(2 * abs(k)), Const("pi"))
                out.append(Rel("==", s1, s2 if k == 0 else
                               Add(s2, Neg(turn) if k < 0 else turn)))
            return out
    return [Rel("==", _point(end), _point(start))]


def _ring_holds(j):
    """An equation ring proves, over C by its split parts."""
    if type(j) is not Rel or j.op != "==":
        return False
    try:
        if complexes.has_complex(j):
            (a, b), (c, d) = complexes.split(j.lhs), complexes.split(j.rhs)
            R = complexes._real
            FD.ring(R(a), R(c))
            FD.ring(R(b), R(d))
        else:
            FD.ring(j.lhs, j.rhs)
        return True
    except (FD.NotEqual, Refused, RecursionError):
        return False


def _closed_verdict(k):
    """A closed real key decided: norm_num, the exact values then norm_num,
    then E206's surds. True, False or None."""
    try:
        said = FD.norm_num(k)
        if said is not None:
            return said
        new, _ = discharge.exact_values(k)
        said = FD.norm_num(new)
        return said if said is not None else FD.surd_decide(new)
    except Refused:
        return None


def _real_keys(prop, P):
    key = with_domain(prop, P)
    return complexes.realify_judgement(key) if complexes.has_complex(key) \
        else (key,)


def _verdict(prop, P):
    """The finder's test (untrusted): True when every real key of prop at P
    settles, False when a closed one is false, else None."""
    out = True
    try:
        keys = _real_keys(prop, P)
    except Refused:
        return None
    for k in keys:
        if k.dom == ():
            v = _closed_verdict(k)
            if v is False:
                return False
            if v is None and not _settles(k):
                out = None
        elif not _settles(k):
            out = None
    return out


def _owe(buf, prop, source, P, anc, gd):
    """Emit prop at P. An equation ring proves is discharged ('ring'); a
    closed key E206 decides is discharged ('norm_num_surd') or refused
    'obligation-refuted'; anything else is emitted as any key is."""
    if _ring_holds(prop):
        for k in _real_keys(prop, P):
            if k not in buf:
                _emit(buf, k, source, gd, discharged_by=("ring", ()),
                      divisor=False)
        return
    keys = _real_keys(prop, P)
    if all(k.dom == () for k in keys):
        for k in keys:
            said = FD.norm_num(k)
            if said is None:
                new, used = discharge.exact_values(k)
                if FD.norm_num(new) is None:
                    v = FD.surd_decide(new)
                    if v is False:
                        raise Refused("obligation-refuted", f"E206: "
                                      f"{show(k)} is false")
                    if v:
                        _emit(buf, k, source, gd, divisor=False,
                              discharged_by=("norm_num_surd", tuple(used)))
                        continue
            _emit(buf, k, source, gd, divisor=False)
        return
    _emit_at(buf, prop, P, anc, source, gd, divisor=False)


def _choose(branches, P, code, what):
    """The first branch whose every condition settles (the finder,
    untrusted): (its value, its conditions). None settling refuses
    `code`."""
    for value, conds in branches:
        if all(_verdict(c, P) is True for c in conds):
            return value, conds
    raise Refused(code, f"no branch of {what} is decided")


# -- the region (E201)

def _sq(t):
    return Pow(t, 2)


def _norm2c(w):
    """|w|^2 in w's parts."""
    return Add(_sq(App("re", w)), _sq(App("im", w)))


def _sub(a, b):
    return a if b == Num(0) else Add(a, Neg(b))


def _region(conds, z):
    """U's conditions, each ('half', diff, alpha, beta, j) for diff > 0
    affine with diff(z) == alpha*re z + beta*im z + diff(0), or ('disk', c,
    rho, j) for abs(z - c) < rho."""
    zc, out = CVar(z), []
    for j in conds:
        if type(j) is not Rel or j.dom:
            raise Refused("region-not-convex", f"{_brief(j)} is not an "
                          "open half-plane or disk (E201)")
        j = Rel(j.op, subst(j.lhs, {z: zc}), subst(j.rhs, {z: zc}))
        if z not in fv(Add(j.lhs, j.rhs)) or any(type(n) is CVar and n.name != z
                                 for n in DV._nodes(Add(j.lhs, j.rhs))):
            raise Refused("region-wrong-variable", f"{show(j)} is not a "
                          f"condition on {z} alone (E201)")
        if j.op not in ("<", ">"):
            raise Refused("region-not-convex", f"{show(j)}: only < and > "
                          "make an open region (E201)")
        lo, hi = (j.lhs, j.rhs) if j.op == "<" else (j.rhs, j.lhs)
        if type(lo) is App and lo.fn == "abs" and z in fv(lo.arg) and \
                z not in fv(hi):
            c0 = subst(lo.arg, {z: Num(0)})
            c = c0.a if type(c0) is Neg else Num(0) if c0 == Num(0) \
                else Neg(c0)
            if not _ring_holds(Rel("==", lo.arg, _sub(zc, c))):
                raise Refused("region-not-convex", f"{show(j)} is not an "
                              "open disk abs(z - c) < r (E201)")
            out.append(("disk", c, hi, j))
            continue
        diff = _sub(hi, lo)
        g0 = subst(diff, {z: Num(0)})
        alpha = _sub(subst(diff, {z: Num(1)}), g0)
        beta = _sub(subst(diff, {z: Const("i")}), g0)
        affine = Add(Add(Mul(alpha, App("re", zc)), Mul(beta, App("im", zc))),
                     g0)
        try:
            ok = sort_of(diff) == "R" and FD.ring_equal(
                complexes.realify(diff), complexes.realify(affine))
        except Refused:
            ok = False
        if not ok:
            raise Refused("region-not-convex", f"{show(j)} is not an open "
                          "half-plane or disk (E201)")
        out.append(("half", diff, alpha, beta, j))
    return out


def _in_U(U, p, z):
    """The keys saying the point p is in U."""
    out = []
    for item in U:
        if item[0] == "half":
            out.append(Rel(">", subst(item[1], {z: p}), Num(0)))
        else:
            _, c, rho, _ = item
            out += [Rel(">", rho, Num(0)),
                    Rel("<", _norm2c(_sub(p, c)), _sq(rho))]
    return out


def _not_in_U(U, p, z):
    """One branch per condition, each saying p fails it."""
    out = []
    for item in U:
        if item[0] == "half":
            out.append([Rel("<=", subst(item[1], {z: p}), Num(0))])
        else:
            _, c, rho, _ = item
            out.append([Rel(">=", _norm2c(_sub(p, c)), _sq(rho))])
    return out


def _piece_in_U(U, piece, z, P):
    """E202 (2): (keys, extra domain) for a path piece inside U."""
    k = type(piece)
    if k is Seg:
        return _in_U(U, piece.a, z) + _in_U(U, piece.b, z), ()
    if k is Arc:
        out = []
        c, r = piece.c, piece.r
        for item in U:
            if item[0] == "half":
                _, diff, alpha, beta, _ = item
                Lc = subst(diff, {z: c})
                out += [Rel(">", Lc, Num(0)),
                        Rel(">", _sq(Lc), Mul(_sq(r), Add(_sq(alpha),
                                                          _sq(beta))))]
            else:
                _, c0, rho, _ = item
                out += [Rel(">", r, Num(0)), Rel(">", _sub(rho, r), Num(0)),
                        Rel("<", _norm2c(_sub(c, c0)), _sq(_sub(rho, r)))]
        return out, ()
    rng, orient = _range_of(piece.var, piece.lo, piece.hi, P)  # path[s]
    phi = piece.phi
    return [Rel(item[-1].op, subst(item[-1].lhs, {z: phi}),
                subst(item[-1].rhs, {z: phi})) for item in U], (rng, orient)


def _flat(g):
    """g's pieces, unoriented."""
    if type(g) is Rev:
        return _flat(g.g)
    if type(g) is Join:
        return _flat(g.a) + _flat(g.b)
    return [g]


def _oriented(g, back=False):
    """g's pieces in traversal order, each with True when run backwards."""
    if type(g) is Rev:
        return _oriented(g.g, not back)
    if type(g) is Join:
        a, b = _oriented(g.a, back), _oriented(g.b, back)
        return b + a if back else a + b
    return [(g, back)]


# -- completeness of S (E204)

def _side_conditions(f, z):
    """(divisors, other side conditions) holomorphy owes for f: deriv's
    under D[z] (E184; refuses what is not holomorphic) and f's own
    formers, deduplicated."""
    props = [k for k, _ in DV.deriv(f, z, ()).emissions]
    props += [p for _, s, _, _ in _positions(f, ()) for p, _ in _owed(s)]
    divs, other = [], []
    for p in props:
        p = with_domain(p, ())
        if type(p) is NonZero:
            if p.e not in divs:
                divs.append(p.e)
        elif p not in other:
            other.append(p)
    return divs, other


def _c_term(c):
    return roots.root_term((c, roots.ZERO, 1))


def _zminus(z, r):
    zc = CVar(z)
    if r == Num(0):
        return zc
    return Add(zc, r.a) if type(r) is Neg else Add(zc, Neg(r))


def _factored(lc, rts, z, skip=None):
    """lc*(z - r)^m*... over the roots but `skip`."""
    out = None if lc == Num(1) else lc
    for r, m in rts:
        if r == skip:
            continue
        f = _zminus(z, r)
        f = f if m == 1 else Pow(f, m)
        out = f if out is None else Mul(out, f)
    return Num(1) if out is None else out


def _factor_divisor(d, z, buf, P, anc, gd):
    """E204: (exp arguments, lc, [(root, m)]) for the divisor d, the
    factorisation checked by field on split parts with sqrt_sq_val facts,
    and lc # 0 owed."""
    rest, us = complexes._exp_factors(d)
    if rest is None:
        return us, Num(1), []
    if z not in fv(rest):
        _owe(buf, NonZero(rest), S_RES_ROOTS, P, anc, gd)
        return us, rest, []
    p = roots.poly(rest, z)
    if p is not None and len(p) <= 1:  # E211: z cancels, no root
        _owe(buf, NonZero(rest), S_RES_ROOTS, P, anc, gd)
        return us, rest, []
    if p is None:  # E273: factor by factor, symbolic ones by E274
        return _factor_symbolic(rest, us, z, buf, P, anc, gd)
    found = roots.factor(p)
    if found is None:
        raise Refused("residue-roots-not-found", f"no factorisation of "
                      f"{_brief(rest)} was found (E204)")
    lc, rts = _c_term(found[0]), [(roots.root_term(r), m)
                                  for r, m in found[1]]
    surds = sorted({r[2] for r, _ in found[1] if r[2] != 1})
    facts = [(Pow(App("sqrt", Num(s)), 2), Num(s)) for s in surds]
    (a, b), (c, e) = complexes.split(rest), complexes.split(
        _factored(lc, rts, z))
    R = complexes._real
    try:
        FD.field(R(a), R(c), facts)
        FD.field(R(b), R(e), facts)
    except (FD.NotEqual, Refused, RecursionError):
        raise Refused("residue-roots-not-found", f"the factorisation of "
                      f"{_brief(rest)} does not check (E204)") from None
    for s in surds:  # sqrt_sq_val's hypothesis, a >= 0
        _owe(buf, Rel(">=", Num(s), Num(0)), S_RES_ROOTS, P, anc, gd)
    _owe(buf, NonZero(lc), S_RES_ROOTS, P, anc, gd)
    return us, lc, rts


def _num_den(t, z):
    """E279: (N, D) with t == N/D by structure, through quotients,
    products, negation and integer powers; None for anything else that
    holds z outside a polynomial shape."""
    k = type(t)
    if z not in fv(t) or _poly_shape(t, z):
        return t, Num(1)
    if k is Div or k is Mul:
        a, b = _num_den(t.a, z), _num_den(t.b, z)
        if a is None or b is None:
            return None
        if k is Mul:
            return _times(a[0], b[0]), _times(a[1], b[1])
        return _times(a[0], b[1]), _times(a[1], b[0])
    if k is Neg:
        a = _num_den(t.a, z)
        return None if a is None else (Neg(a[0]), a[1])
    if k is Pow:
        a = _num_den(t.base, z)
        if a is None:
            return None
        n, d = a if t.n >= 0 else (a[1], a[0])
        return Pow(n, abs(t.n)), Pow(d, abs(t.n))
    return None


def _degree_up(t, z):
    """E279: an upper bound on t's degree in z, by structure."""
    if z not in fv(t):
        return 0
    k = type(t)
    if k is CVar:
        return 1
    if k is Add:
        return max(_degree_up(t.a, z), _degree_up(t.b, z))
    if k is Mul:
        return _degree_up(t.a, z) + _degree_up(t.b, z)
    if k is Neg or k is Div:
        return _degree_up(t.a, z)
    if k is Pow:
        return t.n * _degree_up(t.base, z)
    return 10 ** 6


def _poly_shape(t, z):
    """t built from z, z-free terms, +, -, *, integer powers >= 0 and
    division by a z-free term: a polynomial in z with z-free coefficients."""
    if z not in fv(t):
        return True
    k = type(t)
    if k is CVar:
        return True
    if k in (Add, Mul):
        return _poly_shape(t.a, z) and _poly_shape(t.b, z)
    if k is Neg:
        return _poly_shape(t.a, z)
    if k is Div:
        return z not in fv(t.b) and _poly_shape(t.a, z)
    if k is Pow:
        return t.n >= 0 and _poly_shape(t.base, z)
    return False


def _factor_list(t, z, e=1):
    """E273: (factor, exponent) pairs of t through products, powers and
    negation; a z-free factor is kept as a constant."""
    k = type(t)
    if k is Mul:
        return _factor_list(t.a, z, e) + _factor_list(t.b, z, e)
    if k is Pow and t.n > 0:
        return _factor_list(t.base, z, e * t.n)
    if k is Neg:
        return [(Neg(Num(1)), e)] + _factor_list(t.a, z, e)
    return [(t, e)]


def _c_normal(t):
    """A z-free coefficient in field's normal form, over C by its parts,
    where field checks the two equal; else t (E279)."""
    try:
        if complexes.has_complex(t):
            a, b = complexes.split(t)
            parts = tuple(None if x is None else _whole_normal(
                complexes._real(x)) for x in (a, b))
            parts = tuple(None if x == Num(0) else x for x in parts)
            new = complexes.join(parts) if parts != (None, None) else Num(0)
        else:
            new = _whole_normal(t)
        return new if _ring_holds_field(t, new) else t
    except (Refused, RecursionError):
        return t


def _quadratic_roots(f, z, P):
    """E274: (lead, [(root, m)], [(E, key)]) for a factor of degree <= 2
    with z-free coefficients, the signs of its discriminant settled at P;
    None when it is not one, or its discriminant's sign is not decided."""
    zc = CVar(z)
    c0 = subst(f, {z: Num(0)})
    f1, fm = subst(f, {z: Num(1)}), subst(f, {z: Neg(Num(1))})
    c1 = Div(_sub(f1, fm), Num(2))
    c2 = _sub(Div(Add(f1, fm), Num(2)), c0)
    c0, c1, c2 = (_c_normal(c) for c in (c0, c1, c2))  # E279: readable
    if not _ring_holds(Rel("==", f, Add(Add(Mul(c2, Pow(zc, 2)),
                                               Mul(c1, zc)), c0))):
        return None
    if _ring_holds(Rel("==", c2, Num(0))):
        if _ring_holds(Rel("==", c1, Num(0))):
            return None
        return c1, [(_c_normal(Neg(Div(c0, c1))), 1)], []
    # E280: monic first, so proportional factors give the same roots
    lead = c2
    c1, c0, c2 = _c_normal(Div(c1, c2)), _c_normal(Div(c0, c2)), Num(1)
    D = _sub(Pow(c1, 2), Mul(Mul(Num(4), c2), c0))
    try:
        re, im = complexes.split(D)
    except Refused:
        return None
    if im is not None and not _ring_holds(Rel("==", complexes._real(im),
                                               Num(0))):
        return None
    E = Num(0) if re is None else _c_normal(complexes._real(re))
    if _ring_holds(Rel("==", E, Num(0))):
        return lead, [(_c_normal(Neg(Div(c1, Num(2)))), 2)], []
    half = _c_normal(Neg(Div(c1, Num(2))))  # E280: no -0 left in a root
    for op, rad, imag in ((">", E, False), ("<", Neg(E), True)):
        key = Rel(op, E, Num(0))
        if _verdict(key, P) is True:
            rad = _c_normal(rad)
            s = Div(App("sqrt", rad), Num(2))
            s = Mul(Const("i"), s) if imag else s
            return lead, [(s if half == Num(0) else Add(half, s), 1),
                          (Neg(s) if half == Num(0) else Add(half, Neg(s)),
                           1)], [(rad, key)]
    return None


def _factor_symbolic(rest, us, z, buf, P, anc, gd):
    """E273-E275: rest factored factor by factor, symbolic quadratics by
    E274, the whole checked by field on split parts with sqrt_sq_val
    facts, the leading coefficient and each discriminant's sign owed."""
    lc, rts, rads = Num(1), [], []
    for f, e in _factor_list(rest, z):
        if z not in fv(f):
            lc = _times(lc, f if e == 1 else Pow(f, e))
            continue
        if not _poly_shape(f, z):
            raise Refused("residue-divisor-not-polynomial", f"the divisor "
                          f"factor {_brief(f)} is not a polynomial in {z} "
                          "(E273)")
        p = roots.poly(f, z)
        found = roots.factor(p) if p is not None and len(p) >= 2 else None
        if found is not None:
            lead = _c_term(found[0])
            got = [(roots.root_term(r), m) for r, m in found[1]]
            rads += [(Num(r[2]), Rel(">=", Num(r[2]), Num(0)))
                     for r, _ in found[1] if r[2] != 1]
        else:
            q = _quadratic_roots(f, z, P)
            if q is None:
                raise Refused("residue-roots-not-found", f"no factorisation "
                              f"of {_brief(f)} was found (E273, E274)")
            lead, got, more = q
            rads += more
        lc = _times(lc, lead if e == 1 else Pow(lead, e))
        for r, m in got:
            for k, (r0, m0) in enumerate(rts):
                if r0 == r:
                    rts[k] = (r0, m0 + m * e)
                    break
            else:
                rts.append((r, m * e))
    facts, seen = [], set()
    for rad, key in rads:
        atom = App("sqrt", rad)
        if atom not in seen:
            seen.add(atom)
            facts.append((Pow(atom, 2), rad))
            _owe(buf, key, S_RES_ROOTS, P, anc, gd)
    (a, b), (c, e) = complexes.split(rest), complexes.split(
        _factored(lc, rts, z))
    R = complexes._real
    try:
        FD.field(R(a), R(c), facts)
        FD.field(R(b), R(e), facts)
    except (FD.NotEqual, Refused, RecursionError):
        raise Refused("residue-roots-not-found", f"the factorisation of "
                      f"{_brief(rest)} does not check (E274)") from None
    _owe(buf, NonZero(lc), S_RES_ROOTS, P, anc, gd)
    return us, lc, rts


# -- winding numbers (E205)

def _height(c, r, a, q, angle):
    """im c + r*sin(angle) - im a, with sin exact at multiples of pi/6
    and pi/4 (E211)."""
    cs = _cos_sin(q)
    sin = cs[1] if cs is not None else App("sin", angle)
    return _sub(Add(App("im", c), _times(r, sin)) if sin != Num(0)
                else App("im", c), App("im", a))


def _cross_branches(up, ys, ye, XR, XN, count):
    """Sunday's rule for one monotone piece: count where it crosses right
    of a, 0 otherwise."""
    if up:
        H = [Rel("<=", ys, Num(0)), Rel(">", ye, Num(0))]
        miss = [[Rel(">", ys, Num(0))], [Rel("<=", ye, Num(0))]]
    else:
        H = [Rel("<=", ye, Num(0)), Rel(">", ys, Num(0))]
        miss = [[Rel(">", ye, Num(0))], [Rel("<=", ys, Num(0))]]
    return ([(count, H + x) for x in XR] + [(0, m) for m in miss]
            + [(0, x) for x in XN])


def _wind(g, a, P, anc, gd, buf):
    """wind(g, a) by crossings of the ray right of a, each branch owed;
    g's avoidance of a owed too."""
    total = 0
    for piece, back in _oriented(g):
        k = type(piece)
        if k is Seg:
            p, q = (piece.b, piece.a) if back else (piece.a, piece.b)
            P_, Q_ = _sub(p, a), _sub(q, a)
            xp, yp = App("re", P_), App("im", P_)
            xq, yq = App("re", Q_), App("im", Q_)
            cross = Add(Mul(xp, yq), Neg(Mul(xq, yp)))
            dp = Add(Mul(App("re", _sub(a, p)), App("re", _sub(q, p))),
                     Mul(App("im", _sub(a, p)), App("im", _sub(q, p))))
            dq = Add(Mul(App("re", _sub(a, q)), App("re", _sub(p, q))),
                     Mul(App("im", _sub(a, q)), App("im", _sub(p, q))))
            avoid = [(0, [NonZero(cross)]), (0, [Rel("<", dp, Num(0))]),
                     (0, [Rel("<", dq, Num(0))])]
            said = [_verdict(c, P) for _, (c,) in avoid]
            if all(v is False for v in said):
                raise Refused("residue-pole-on-path", f"{show(a)} lies on "
                              f"{show(piece)} (E205)")
            # the first branch that settles, else the first, owed
            _owe(buf, next((c for v, (_, (c,)) in zip(said, avoid) if v),
                           avoid[0][1][0]), S_RES_WIND, P, anc, gd)
            up = [Rel("<=", yp, Num(0)), Rel(">", yq, Num(0))]
            down = [Rel(">", yp, Num(0)), Rel("<=", yq, Num(0))]
            branches = [(1, up + [Rel(">", cross, Num(0))]),
                        (-1, down + [Rel("<", cross, Num(0))]),
                        (0, [Rel("<=", yp, Num(0)), Rel("<=", yq, Num(0))]),
                        (0, [Rel(">", yp, Num(0)), Rel(">", yq, Num(0))]),
                        (0, up + [Rel("<", cross, Num(0))]),
                        (0, down + [Rel(">", cross, Num(0))])]
            n, conds = _choose(branches, P, "wind-undecided",
                               f"{show(piece)}'s crossing")
        elif k is Arc:
            c, r = piece.c, piece.r
            t1, t2 = (piece.t2, piece.t1) if back else (piece.t1, piece.t2)
            q1, q2 = _pi_multiple(t1), _pi_multiple(t2)
            if q1 is None or q2 is None:
                raise Refused("wind-not-computable", f"{show(piece)}'s "
                              "angles are not rational multiples of pi (E205)")
            # E211: the crossing rules read r > 0 (r < 0 is the circle
            # turned through its centre)
            _owe(buf, Rel(">", r, Num(0)), S_RES_WIND, P, anc, gd)
            D2, r2 = _norm2c(_sub(a, c)), _sq(r)
            off = NonZero(_sub(D2, r2))
            if _verdict(off, P) is False:
                raise Refused("residue-pole-on-path", f"{show(a)} lies on "
                              f"the circle of {show(piece)} (E205)")
            _owe(buf, off, S_RES_WIND, P, anc, gd)
            lo, hi = min(q1, q2), max(q1, q2)
            cuts, j = [], math.floor(lo - Fraction(1, 2)) + 1
            while j + Fraction(1, 2) < hi:
                if j + Fraction(1, 2) > lo:
                    cuts.append(j + Fraction(1, 2))
                j += 1
            ends = [lo] + cuts + [hi]
            sign = 1 if q2 >= q1 else -1
            terms = {q1: t1, q2: t2}
            dx = _sub(App("re", c), App("re", a))
            n, conds = 0, []
            for u, v in zip(ends, ends[1:]):
                mid = ((u + v) / 2) % 2
                right = mid < Fraction(1, 2) or mid > Fraction(3, 2)
                yu = _height(c, r, a, u, terms.get(u, Mul(_frac(u), Const("pi"))))
                yv = _height(c, r, a, v, terms.get(v, Mul(_frac(v), Const("pi"))))
                if right:
                    XR = [[Rel(">", dx, Num(0))], [Rel("<", D2, r2)]]
                    XN = [[Rel("<=", dx, Num(0)), Rel(">=", D2, r2)]]
                else:
                    XR = [[Rel(">", dx, Num(0)), Rel(">", D2, r2)]]
                    XN = [[Rel("<=", dx, Num(0))], [Rel("<=", D2, r2)]]
                up = right == (sign > 0)
                ys, ye = (yu, yv) if sign > 0 else (yv, yu)
                m, cs = _choose(_cross_branches(up, ys, ye, XR, XN,
                                                1 if up else -1),
                                P, "wind-undecided", f"{show(piece)}'s "
                                "crossing")
                n, conds = n + m, conds + cs
        else:
            raise Refused("wind-not-computable", f"a path[s] piece's "
                          "winding number is not computed yet (E205)")
        for cnd in conds:
            _owe(buf, cnd, S_RES_WIND, P, anc, gd)
        total += n
    return total


def _frac(q):
    return roots._frac(q)


# -- residues (E207)

class _Poles:
    """f's pole orders at one point a, read from the factorisations."""

    def __init__(self, z, a, fac):
        self.z, self.a, self.fac = z, a, fac

    def mult(self, d):
        if self.z not in fv(d):
            return 0
        if d not in self.fac:
            raise Refused("residue-divisor-not-polynomial", f"{_brief(d)} "
                          "has no factorisation (E204)")
        return sum(m for r, m in self.fac[d][2] if r == self.a)

    def order(self, t):
        if self.z not in fv(t):
            return 0
        k = type(t)
        if k is CVar:
            return 0
        if k is Add:
            return max(self.order(t.a), self.order(t.b))
        if k is Neg:
            return self.order(t.a)
        if k is Mul:
            return self.order(t.a) + self.order(t.b)
        if k is Div:
            self._regular(t.b)
            return self.order(t.a) + self.mult(t.b)
        if k is Pow:
            if t.n >= 0:
                return t.n * self.order(t.base)
            self._regular(t.base)
            return -t.n * self.mult(t.base)
        for _, c in children(t):
            if isinstance(c, Term):
                self._regular(c)
        return 0

    def _regular(self, t):
        if self.order(t):
            raise Refused("residue-not-a-pole", f"{_brief(t)} has a pole "
                          f"at {show(self.a)} inside a function, so the "
                          "singularity is not a pole (E207)")

    def zpow(self, j):
        f = _zminus(self.z, self.a)
        return Num(1) if j == 0 else f if j == 1 else Pow(f, j)

    def reduced(self, d):
        us, lc, rts = self.fac[d]
        out = _factored(lc, rts, self.z, skip=self.a)
        for u in us:
            out = _times(App("exp", u), out)
        return out

    def times(self, t, k):
        """(z - a)^k * t, built by structure, for k >= order(t)."""
        o = self.order(t)
        if o == 0:
            return _times(self.zpow(k), t)
        kind = type(t)
        if kind is Add:
            return Add(self.times(t.a, k), self.times(t.b, k))
        if kind is Neg:
            return Neg(self.times(t.a, k))
        if kind is Mul:
            oa = self.order(t.a)
            return _times(self.times(t.a, oa), self.times(t.b, k - oa))
        if kind is Div:
            x = self.times(t.a, k - self.mult(t.b))
            d = self.reduced(t.b)
            return x if d == Num(1) else Div(x, d)
        if t.n > 0:  # Pow
            p = self.order(t.base)
            return _times(self.zpow(k - t.n * p), Pow(self.times(t.base, p),
                                                       t.n))
        mu = -t.n * self.mult(t.base)
        d = self.reduced(t.base)
        return _times(self.zpow(k - mu), Num(1) if d == Num(1) else Pow(d, t.n))


RESIDUE_NODES_MAX = 15000  # E221: D^(m-1) phi's size, checked per step


def _pow01(t):
    if type(t) is Pow and t.n in (0, 1):
        return Num(1) if t.n == 0 else t.base
    return t


def _residue(f, z, a, fac, buf, P, anc, gd):
    """E207: (m, the residue term) at a, m == 0 for a removable point."""
    poles = _Poles(z, a, fac)
    m = poles.order(f)
    if m == 0:
        return 0, None
    phi = poles.times(f, m)
    for _, s, _, _ in _positions(phi, ()):  # phi holomorphic at a
        for p, _ in _owed(s):
            if type(p) is NonZero:
                _owe(buf, NonZero(subst(p.e, {z: a})), S_RES_POLE, P, anc, gd)
    for _ in range(m - 1):  # E221: u^0 is 1 and u^1 is u between steps
        phi = discharge._rebuild(DV.deriv(phi, z, ()).output, _pow01)
        if sum(1 for _ in DV._nodes(phi)) > RESIDUE_NODES_MAX:
            raise Refused("residues-too-large", f"the derivatives at "
                          f"{show(a)}, a pole of order up to {m}, grow past "
                          f"{RESIDUE_NODES_MAX} nodes (E221)")
    R = subst(phi, {z: a})
    if m > 2:
        R = Div(R, Num(math.factorial(m - 1)))
    return m, R


def _residues(state, args, minted, buf):
    """E200-E208: the selected CInt[z on g] f replaced by 2*pi*i times the
    sum of wind(g, a)*res(f, a) over S, with every hypothesis owed."""
    if args.get("half") == "keyhole":  # E232: Z11
        return _residues_keyhole(state, args, minted, buf)
    if args.get("half") == "sector":  # E243: Z12
        return _residues_sector(state, args, minted, buf)
    if "half" in args:  # E213: Z10, on a line Int
        return _residues_line(state, args, minted, buf)
    g = state.goal[0]
    side, path, ci, P, anc = _cint_select(g, args.get("occurrence"))
    z, gd = ci.var, g.dom
    U = _region(args.get("region", ()), z)
    for x in _path_data(ci.path):  # E199: the path's own data is owed
        _charge_formers(buf, x, P, gd, anc=anc)
    # (1) closed, and every join meeting (E211)
    for end, start in _joins(ci.path) + [(_end_info(ci.path, True),
                                          _end_info(ci.path, False))]:
        for j in _meets(end, start):
            _owe(buf, j, S_RES_CLOSED, P, anc, gd)
    for piece in _flat(ci.path):  # E211: path[s]'s phi, as cint_param's
        if type(piece) is PathP:
            rng, orient = _range_of(piece.var, piece.lo, piece.hi, P)
            if orient is not None:
                _emit(buf, orient, "orient", gd)
            _charge_formers(buf, piece.phi, P + (rng,), gd, anc=anc)
            _emit_at(buf, Reg(piece.phi, 1), P + (rng,), anc, S_CINT_C1, gd)
            for key, _ in DV.deriv(piece.phi, piece.var, ()).emissions:
                _emit_at(buf, key, P + (rng,), anc, S_CINT_C1, gd)
    # (2) g in U
    if U:
        for piece in _flat(ci.path):
            keys, extra = _piece_in_U(U, piece, z, P)
            dom = P
            if extra:
                rng, orient = extra
                if orient is not None:
                    _emit(buf, orient, "orient", gd)
                dom = P + (rng,)
            for key in keys:
                _owe(buf, key, S_RES_IN_U, dom, anc, gd)
    # (3) holomorphic on U minus S
    divs, other = _side_conditions(ci.body, z)
    conds = tuple(item[-1] for item in U)
    for p in other:  # a cut: on all of U
        _emit_at(buf, p, P + conds, anc, S_RES_HOLO, gd, divisor=False)
    fac, found = {}, []
    for d in divs:
        fac[d] = _factor_divisor(d, z, buf, P, anc, gd)
        for r, _ in fac[d][2]:
            if r not in found:
                found.append(r)
    S = []
    for r in found:  # E204: each root in S, or outside U
        inside = _in_U(U, r, z)
        if not U or all(_verdict(c, P) is True for c in inside):
            S.append(r)
            for c in inside:
                _owe(buf, c, S_RES_ROOTS, P, anc, gd)
            continue
        out = next((b for b in _not_in_U(U, r, z)
                    if all(_verdict(c, P) is True for c in b)), None)
        for c in out or inside:
            _owe(buf, c, S_RES_ROOTS, P, anc, gd)
        if out is None:
            S.append(r)
    # (4) S distinct, avoided, and each winding number
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            _owe(buf, NonZero(_sub(a, b)), S_RES_ROOTS, P, anc, gd)
    total, trace = None, []
    for a in S:
        w = _wind(ci.path, a, P, anc, gd, buf)
        m, R = (0, None) if w == 0 else _residue(ci.body, z, a, fac, buf,
                                                  P, anc, gd)
        trace.append((a, m, w))
        if R is None:
            continue
        term = R if w == 1 else Neg(R) if w == -1 else \
            Mul(Num(abs(w)), R) if w > 0 else Neg(Mul(Num(-w), R))
        total = term if total is None else Add(total, term)
    new = Num(0) if total is None else Mul(
        Mul(Mul(Num(2), Const("pi")), Const("i")), total)
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, gd, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"trace": tuple(trace)}


# ---------------------------------------------------------------- Z10
#
# p1_expected E212-E217: a line integral closed in a half-plane (Z10), and
# int_even. The decay certificate's split is structural and trusted
# (E214); P/Q and the roots are proposed (roots.py) and checked.

S_LINE_CERT, S_LINE_POLE = "residues_line_certificate", "residues_line_pole"
S_EVEN = "int_even_check"


def _exp_split(t, z):
    """E214: (u, g) with t == exp(u)*g by exp's laws, u None for no exp;
    an exp under a sum, or in a head that is not exp, refuses."""
    if z not in fv(t):
        return None, t
    k = type(t)
    if k is App and t.fn == "exp":
        if any(type(n) is App and n.fn == "exp" and z in fv(n)
               for n in DV._nodes(t.arg)):  # E221: a z-free one is a constant
            raise Refused("decay-not-certified", f"{_brief(t)}: an exp "
                          "inside an exp (E214)")
        return t.arg, Num(1)
    add = lambda a, b: b if a is None else a if b is None else Add(a, b)
    neg = lambda a: None if a is None else Neg(a)
    if k is Mul or k is Div:
        (ua, ga), (ub, gb) = _exp_split(t.a, z), _exp_split(t.b, z)
        if k is Mul:
            return add(ua, ub), _times(ga, gb)
        return add(ua, neg(ub)), ga if gb == Num(1) else Div(ga, gb)
    if k is Neg:
        u, g = _exp_split(t.a, z)
        return u, Neg(g)
    if k is Pow:
        u, g = _exp_split(t.base, z)
        return (None if u is None else _times(Num(t.n) if t.n >= 0 else
                                              Neg(Num(-t.n)), u)), Pow(g, t.n)
    if any(type(n) is App and n.fn == "exp" and z in fv(n)
           for n in DV._nodes(t)):
        raise Refused("decay-not-certified", f"{_brief(t)}: an exp under a "
                      "sum or another head; Z10 reads exp(i*a*z)*g with g "
                      "rational (E214)")
    return None, t


def _const_split(t, z):
    """E242: (c, r) with t == c*r by structure, c the z-free factors of
    t's products and quotients (Num(1) for none), so a parameter such as
    u_0 in a numerator does not stop the rational certificate."""
    if z not in fv(t):
        return t, Num(1)
    k = type(t)
    if k is Mul or k is Div:
        (ca, ra), (cb, rb) = _const_split(t.a, z), _const_split(t.b, z)
        if k is Mul:
            return _times(ca, cb), _times(ra, rb)
        c = ca if cb == Num(1) else Div(ca, cb)
        return c, ra if rb == Num(1) else Div(ra, rb)
    if k is Neg:
        c, r = _const_split(t.a, z)
        return c, Neg(r)
    return Num(1), t


def _line_select(g, k):
    """The Int nodes of the non-?A side(s), pre-order; the k-th, or the
    only one, which must run over the whole line (E216)."""
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom)
             if isinstance(s, (Integral, PV))]  # E267: a PV too
    if not found:
        raise Refused("residues-no-integral", "the goal holds no integral")
    if k is not None:
        if k >= len(found):
            raise Refused("residues-no-integral", f"no integral at "
                          f"occurrence {k}")
        hit = found[k]
    elif len(found) > 1:
        raise Refused("residues-ambiguous", f"{len(found)} integrals in the "
                      "goal; give an occurrence")
    else:
        hit = found[0]
    it = hit[2]
    _open_end(it, "residues")
    if not (isinstance(it.lo, NegInf) and isinstance(it.hi, PosInf)):
        raise Refused("residues-line-not-whole", f"{_brief(it)} is not over "
                      "the whole line, -oo .. oo (E216)")
    return hit


def _residues_line(state, args, minted, buf):
    """E213-E216: Int[x = -oo .. oo] f as 2*pi*i times the residues in the
    upper (or lower) half-plane, under a decay certificate."""
    g = state.goal[0]
    up = args["half"] == "upper"
    side, path, it, P, anc = _line_select(g, args.get("occurrence"))
    z, gd = it.var, g.dom
    zc = CVar(z)
    f = subst(it.body, {z: zc})
    u, gr = _exp_split(f, z)
    cst, gr = _const_split(gr, z)  # E242: a z-free factor kept aside
    proposal = roots.rational(gr, z)
    sym = None
    if proposal is None:  # E279: symbolic coefficients
        sym = _num_den(gr, z)
        if sym is None or not _poly_shape(sym[0], z) or \
                not _poly_shape(sym[1], z):
            raise Refused("decay-not-certified", f"{_brief(gr)} is not "
                          f"rational in {z} (E214)")
        Pt, Qt = sym
    else:
        pp, qq = proposal
        Pt, Qt = roots.poly_term(pp, z), roots.poly_term(qq, z)
    held = _ring_holds_field(gr, Pt if Qt == Num(1) else Div(Pt, Qt))
    if held is None:  # E221: a resource limit, not a wrong identity
        raise Refused("residues-too-large", f"{_brief(gr)} == P/Q is too "
                      "large for field to check (E221)")
    if not held:
        raise Refused("decay-not-certified", f"{_brief(gr)} == P/Q does not "
                      "check (E214)")
    if sym is None:
        gap = (len(qq) - 1) - (len(pp) - 1 if pp else -1)
    else:  # E279: Q's exact degree from its certified factorisation
        fq = _factor_divisor(Qt, z, buf, P, anc, gd)
        gap = sum(m for _, m in fq[2]) - _degree_up(Pt, z)
    alpha = None
    if u is not None:
        alpha = _sub(subst(u, {z: Num(1)}), subst(u, {z: Num(0)}))
        beta = subst(u, {z: Num(0)})
        if not _ring_holds(Rel("==", u, _plus(_times(alpha, zc), beta))):
            raise Refused("decay-not-certified", f"exp's argument "
                          f"{_brief(u)} is not affine in {z} (E214)")
        if _ring_holds(Rel("==", alpha, Num(0))):
            alpha = None
    if alpha is None:  # (R)
        if gap < 2:
            raise Refused("decay-not-certified", f"deg Q - deg P = {gap} < 2:"
                          " no C/|z|^2 bound (E214)")
    else:  # (J)
        if gap < 1:
            raise Refused("decay-not-certified", f"deg Q - deg P = {gap} < 1:"
                          " Jordan's lemma needs |g| <= C/|z| (E214)")
        _owe(buf, Rel("==", App("re", alpha), Num(0)), S_LINE_CERT, P, anc, gd)
        _owe(buf, Rel(">" if up else "<", App("im", alpha), Num(0)),
             S_LINE_CERT, P, anc, gd)
    # E215: the poles, off the line, and S by side
    fac = {Qt: _factor_divisor(Qt, z, buf, P, anc, gd)}
    S, real = [], []
    pv = isinstance(it, PV)
    if pv:
        _pv_body_formers(it, P, anc, gd, buf)  # E272
    for r, mult in fac[Qt][2]:
        off = NonZero(App("im", r))
        if pv and _verdict(off, P) is not True:  # E267: on the line
            on = Rel("==", App("im", r), Num(0))
            if _verdict(on, P) is not True:
                raise Refused("pv-root-undecided", f"whether {show(r)} is on "
                              "the line is not decided (E267)")
            if mult > 1:
                raise Refused("pv-pole-not-simple", f"{show(r)} is a pole of "
                              f"order {mult} on the line; a principal value "
                              "needs simple ones (E267)")
            _owe(buf, on, S_LINE_POLE, P, anc, gd)
            real.append(r)
            continue
        if _verdict(off, P) is False:
            raise Refused("residue-pole-on-line", f"{show(r)} is a pole on "
                          "the line (E215)")
        _owe(buf, off, S_LINE_POLE, P, anc, gd)
        inside = Rel(">" if up else "<", App("im", r), Num(0))
        outside = Rel("<" if up else ">", App("im", r), Num(0))
        if _verdict(inside, P) is True:
            _owe(buf, inside, S_LINE_POLE, P, anc, gd)
            S.append(r)
        elif _verdict(outside, P) is True:
            _owe(buf, outside, S_LINE_POLE, P, anc, gd)
        else:  # undecided: owed as inside
            _owe(buf, inside, S_LINE_POLE, P, anc, gd)
            S.append(r)
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            _owe(buf, NonZero(_sub(a, b)), S_LINE_POLE, P, anc, gd)
    if not pv:
        _line_divisors(it, z, P, anc, gd, buf, state)  # E251, E263
    body = Pt if Qt == Num(1) else Div(Pt, Qt)
    if u is not None:
        body = _times(App("exp", u), body)
    body = _times(cst, body)
    total, trace = None, []
    for a in S:
        m, R = _residue(body, z, a, fac, buf, P, anc, gd)
        trace.append((a, m, 1))
        if R is not None:
            total = R if total is None else Add(total, R)
    half = None  # E267: the simple real poles' residues
    for a in real:
        m, R = _residue(body, z, a, fac, buf, P, anc, gd)
        trace.append((a, m, 0))
        if R is not None:
            half = R if half is None else Add(half, R)
    pi_i = Mul(Const("pi"), Const("i"))
    new = Num(0) if total is None else Mul(
        Mul(Mul(Num(2), Const("pi")), Const("i")), total)
    if not up and total is not None:
        new = Neg(new)
    if half is not None:
        h = Mul(pi_i, half)
        new = (h if up else Neg(h)) if new == Num(0) else \
            Add(new, h) if up else Add(new, Neg(h))
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, gd, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"trace": tuple(trace)}


def _line_divisors(it, z, P, anc, gd, buf, state=None):
    """E251: each polynomial divisor of the Int's body whose roots all
    settle off the line is nonzero on it; emit its NonZero at the body
    position, as the Int's former charged it, DISCHARGED. E263: the same
    proposition admitted in the tracker on a sub-interval of the line, its
    other domain items free of z, is discharged too."""
    props = set()
    for _, s, d, _a in _positions(it, P, anc):
        for prop, divisor in _owed(s):
            if not divisor or type(prop) is not NonZero or z not in fv(prop.e):
                continue
            dz = subst(prop.e, {z: CVar(z)})
            rest, _us = complexes._exp_factors(dz)
            if rest is None or z not in fv(rest):
                continue
            # the factorisation is checked as E204 checks it, a symbolic
            # one as E274 does (E279)
            try:
                _, _lc, got = _factor_divisor(rest, z, buf, P, anc, gd)
            except Refused:
                continue
            if not got or not all(
                    _verdict(NonZero(App("im", r)), P) is True
                    for r, _ in got):
                continue
            for k in _real_keys(prop, d):
                props.add(replace(k, dom=()))
                old = buf.get(k)
                src = frozenset((S_LINE_POLE,)) | (old.sources if old else
                                                   frozenset())
                if old is None or old.status != DISCHARGED:
                    buf[k] = Obligation(k, src, DISCHARGED,
                                        ("residues_line_roots", ()))
                else:
                    buf[k] = replace(old, sources=src)
    for ob in (state.obligations() if state is not None else ()):
        k = ob.key
        if ob.status != ADMITTED or type(k) is not NonZero or \
                replace(k, dom=()) not in props:
            continue
        ivs = [t for t in k.dom if isinstance(t, Interval)]
        rest = [t for t in k.dom if not isinstance(t, Interval)]
        if len(ivs) == 1 and ivs[0].var == z and not any(
                z in fv(t) for t in rest) and k not in buf:
            buf[k] = Obligation(k, frozenset((S_LINE_POLE,)), DISCHARGED,
                                ("residues_line_roots", ()))


def _ring_holds_field(a, b):
    """a == b by field on split parts (no facts); its divisors are not
    emitted, since the identity is only read where both sides are
    defined."""
    try:
        if complexes.has_complex(Add(a, b)):
            (p, q), (r, s) = complexes.split(a), complexes.split(b)
            R = complexes._real
            FD.field(R(p), R(r))
            FD.field(R(q), R(s))
        else:
            FD.field(a, b)
        return True
    except FD.NotEqual:
        return False
    except Refused as r:  # a power past field's bound is a size, as below
        return None if r.code == FD.POWER_CODE else False
    except RecursionError:
        return None


def _parity_facts(t):
    """E258: sin_odd and cos_even at each sin(-u) and cos(-u) of t, as
    field facts (atom, value)."""
    out, seen = [], set()
    for n in DV._nodes(t):
        if type(n) is App and n.fn in ("sin", "cos") and type(n.arg) is Neg \
                and n not in seen:
            seen.add(n)
            u = n.arg.a
            out.append((n, Neg(App("sin", u)) if n.fn == "sin"
                        else App("cos", u)))
    return out


def _even_select(g, k):
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom)
             if isinstance(s, Integral) and isinstance(s.hi, PosInf) and (
                 _bare(s.lo) == Num(0) or isinstance(s.lo, NegInf))]  # E245
    if not found or (k is not None and k >= len(found)):
        raise Refused("int-even-no-integral", "the goal holds no Int[x = 0 "
                      ".. oo] (E217)")
    if k is None and len(found) > 1:
        raise Refused("int-even-ambiguous", f"{len(found)} such integrals; "
                      "give an occurrence")
    return found[k or 0]


def _int_even(state, args, minted, buf):
    """E217: Int[x = 0 .. oo] f as (1/2)*Int[x = -oo .. oo] f for an even
    f, checked by field on split parts, its divisors owed on the line."""
    g = state.goal[0]
    side, path, it, P, anc = _even_select(g, args.get("occurrence"))
    _open_end(it, "int_even")
    x, f = it.var, it.body
    flipped = subst(f, {x: Neg(Var(x))})
    line = Interval(x, NEG_INF, False, POS_INF, False)
    done = None
    for facts in ([], _parity_facts(flipped)):  # E258: then with parity
        try:
            if complexes.has_complex(f):
                (a, b), (c, d) = complexes.split(f), complexes.split(flipped)
                R = complexes._real
                done = [FD.field(R(a), R(c), facts),
                        FD.field(R(b), R(d), facts)]
            else:
                done = [FD.field(f, flipped, facts)]
            break
        except (FD.NotEqual, Refused, RecursionError):
            continue
    if done is None:
        raise Refused("int-not-even", f"{_brief(f)} is not even in {x}: "
                      f"f(-{x}) == f({x}) fails (E217)") from None
    own = {p.e for _, s, _, _ in _positions(f, ()) for p, _ in _owed(s)
           if type(p) is NonZero}
    flip_of = {subst(o, {x: Neg(Var(x))}): o for o in own}
    for ok in done:
        for dv in ok.divisors:
            # E263: d(-x) # 0 on the line is d(x) # 0 there, since x -> -x
            # maps the line to itself
            dv = dv if dv in own else flip_of.get(dv, dv)
            _emit_at(buf, NonZero(dv), P + (line,), anc, S_EVEN, g.dom)
    if isinstance(it.lo, NegInf):  # E245: the whole line as twice the half
        new = Mul(Num(2), Integral(x, Num(0), POS_INF, f))
    else:
        new = Mul(Div(Num(1), Num(2)), Integral(x, NEG_INF, POS_INF, f))
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, g.dom, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


# ---------------------------------------------------------------- Z11
#
# p1_expected E232-E237: the keyhole, residues keyhole on an Int from 0
# (or 0+) to oo. The power split is structural and trusted (E234); P/Q
# and the roots are proposed and checked, as in Z10.

S_KEY_CERT, S_KEY_POLE = "residues_keyhole_certificate", "residues_keyhole_pole"
_TWO_PI = Mul(Num(2), Const("pi"))


def _power_split(t, x):
    """E234: (alpha, g) with t == x^alpha*g on (0, oo), alpha None for no
    power: sqrt(x) adds 1/2, rpow(x, e) adds e; products add, quotients
    subtract, integer powers scale."""
    if x not in fv(t):
        return None, t
    k = type(t)
    if k is App and t.fn == "sqrt" and t.arg == Var(x):
        return Div(Num(1), Num(2)), Num(1)
    if k is RPow and t.base == Var(x) and x not in fv(t.exp):
        return t.exp, Num(1)
    add = lambda a, b: b if a is None else a if b is None else Add(a, b)
    neg = lambda a: None if a is None else Neg(a)
    if k is Mul or k is Div:
        (ua, ga), (ub, gb) = _power_split(t.a, x), _power_split(t.b, x)
        if k is Mul:
            return add(ua, ub), _times(ga, gb)
        return add(ua, neg(ub)), ga if gb == Num(1) else Div(ga, gb)
    if k is Neg:
        u, g = _power_split(t.a, x)
        return u, Neg(g)
    if k is Pow:
        u, g = _power_split(t.base, x)
        return (None if u is None else _times(Num(t.n) if t.n >= 0 else
                                              Neg(Num(-t.n)), u)), Pow(g, t.n)
    return None, t


def _integer_value(t):
    """t's value when ring makes it an integer literal, else None."""
    try:
        (p,), _ = FD.ring_polys([t])
    except Refused:
        return None
    if not p:
        return 0
    if len(p) != 1:
        return None
    (mono, q), = p.items()
    return int(q) if mono == () and Fraction(q).denominator == 1 else None


def _log_closed(t):
    """E240: log[2*pi](w) at a closed point w with parts in Q(sqrt s) and
    |w|^2 rational, as ln(|w|^2)/2 + i*theta exactly (theta in (0, 2*pi],
    from discharge's principal Arg shifted up by 2*pi when it is not
    positive); anything else unchanged. Exact: log[theta] w is ln|w| +
    i*arg[theta] w by definition (Z6)."""
    if type(t) is not Branch or t.fn != "log" or t.theta != _TWO_PI or \
            fv(t.arg):
        return t
    try:
        re, im = complexes.split(t.arg)
    except Refused:
        return t
    rt = complexes._real(re) if re is not None else Num(0)
    it_ = complexes._real(im) if im is not None else Num(0)
    principal = discharge._arg_value(Branch("arg", Const("pi"), t.arg))
    if principal is None:
        return t
    v = discharge._surd_of(Add(Pow(rt, 2), Pow(it_, 2)))
    if v is None or v[1] != 0 or v[0] <= 0:
        return t
    sgn_im = FD._surd_sign(*discharge._surd_of(it_)) if im is not None else 0
    sgn_re = FD._surd_sign(*discharge._surd_of(rt)) if re is not None else 0
    up = sgn_im > 0 or (sgn_im == 0 and sgn_re < 0)
    theta = principal if up else Add(principal, _TWO_PI)
    ln = Num(0) if v[0] == 1 else Div(App("ln", roots._frac(v[0])), Num(2))
    imag = Mul(Const("i"), theta)
    return imag if ln == Num(0) else Add(ln, imag)


def _not_integer(alpha, P):
    """E240: keys that make alpha no integer: n < alpha and alpha < n + 1
    for the n in [-8, 8] whose keys settle at P (the finder, untrusted;
    the kernel owes them); else sin(pi*alpha) # 0."""
    for n in range(-8, 9):
        lo = Rel("<", Num(n) if n >= 0 else Neg(Num(-n)), alpha)
        hi = Rel("<", alpha, Num(n + 1) if n + 1 >= 0 else Neg(Num(-n - 1)))
        if _verdict(lo, P) is True and _verdict(hi, P) is True:
            return (lo, hi)
    return NonZero(App("sin", Mul(Const("pi"), alpha)))


def _residues_keyhole(state, args, minted, buf):
    """E232-E236: Int[x = 0 (or 0+) .. oo] x^alpha*R(x) by the keyhole
    about the cut of log[2*pi]."""
    g = state.goal[0]
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom)
             if isinstance(s, Integral)]
    if not found:
        raise Refused("residues-no-integral", "the goal holds no integral")
    k = args.get("occurrence")
    if k is not None and k >= len(found):
        raise Refused("residues-no-integral", f"no integral at occurrence {k}")
    if k is None and len(found) > 1:
        raise Refused("residues-ambiguous", f"{len(found)} integrals in the "
                      "goal; give an occurrence")
    side, path, it, P, anc = found[k or 0]
    if not (_bare(it.lo) == Num(0) and (it.lo == Num(0) or it.lo.side == "+")
            and isinstance(it.hi, PosInf)):
        raise Refused("keyhole-not-half-line", f"{_brief(it)} is not over "
                      "[0, oo) or (0, oo) (E235)")
    x, gd = it.var, g.dom
    z, zc = x, CVar(x)
    if any(type(n) is App and n.fn == "exp" for n in DV._nodes(it.body)):
        raise Refused("keyhole-not-certified", f"{_brief(it.body)}: an exp; "
                      "Z11 reads x^alpha times a rational function (E234)")
    alpha, gr = _power_split(it.body, x)
    gz = subst(gr, {x: zc})
    cst, gz = _const_split(gz, z)  # E242
    proposal = roots.rational(gz, z)
    if proposal is None:
        raise Refused("keyhole-not-certified", f"{_brief(gr)} is not rational "
                      f"in {x} over Q(i) (E234)")
    pp, qq = proposal
    n = None if alpha is None else _integer_value(alpha)
    if alpha is None:
        n = 0
    if n is not None:  # the log form: x^n folded in
        mono = [roots.ZERO] * abs(n) + [roots.ONE]
        if n > 0:
            pp = roots._pmul(pp, mono)
        elif n < 0:
            qq = roots._pmul(qq, mono)
    Pt, Qt = roots.poly_term(pp, z), roots.poly_term(qq, z)
    rat = Pt if Qt == Num(1) else Div(Pt, Qt)
    held = _ring_holds_field(gz if n is None or n == 0 else
                             _times(Pow(zc, n) if n else Num(1), gz), rat)
    if held is None:
        raise Refused("residues-too-large", f"{_brief(gr)} == P/Q is too "
                      "large for field to check (E221)")
    if not held:
        raise Refused("keyhole-not-certified", f"{_brief(gr)} == P/Q does "
                      "not check (E234)")
    degp = len(pp) - 1 if pp else -1
    gap = (len(qq) - 1) - degp
    log = Branch("log", _TWO_PI, zc)
    if n is not None:  # log form (E233)
        if gap < 2:
            raise Refused("decay-not-certified", f"deg Q - deg P = {gap} < 2 "
                          "(E233)")
        body = Mul(log, _times(cst, rat))
    else:  # power form: alpha not an integer, both ends' decay (E233)
        m0 = next((j for j, c in enumerate(pp) if c != roots.ZERO), 0)
        a1 = Add(alpha, Num(1))
        bracket = _not_integer(alpha, P)
        bracket = bracket if isinstance(bracket, tuple) else (bracket,)
        settled = all(_verdict(k, P) is True for k in bracket)
        for key in bracket + (
                Rel(">", a1 if m0 == 0 else Add(a1, Num(m0)), Num(0)),
                Rel("<", a1, Num(gap) if gap >= 0 else Neg(Num(-gap)))):
            _owe(buf, key, S_KEY_CERT, P, anc, gd)
        # E240: alpha not an integer makes 1 - exp(2*pi*i*alpha) # 0, the
        # result's divisor; its realified keys are discharged by that, but
        # only when it settled (E241), never on an admission
        two_pi_i = Mul(_TWO_PI, Const("i"))
        for k in _real_keys(NonZero(Add(Num(1), Neg(App("exp", Mul(
                two_pi_i, alpha))))), P) if settled else ():
            if k not in buf:
                _emit(buf, k, S_KEY_CERT, gd, divisor=False,
                      discharged_by=("keyhole_alpha", ()))
        body = Mul(App("exp", Mul(alpha, log)), _times(cst, rat))
    fac = {Qt: _factor_divisor(Qt, z, buf, P, anc, gd)}
    S = []
    for r, _ in fac[Qt][2]:  # E234: off [0, oo)
        branches = [[NonZero(App("im", r))],
                    [Rel("<", App("re", r), Num(0))]]
        said = [_verdict(c[0], P) for c in branches]
        if all(v is False for v in said):
            raise Refused("residue-pole-on-cut", f"{show(r)} is a pole on "
                          "the cut [0, oo) (E234)")
        pick = next((b for v, b in zip(said, branches) if v), branches[0])
        _owe(buf, pick[0], S_KEY_POLE, P, anc, gd)
        S.append(r)
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            _owe(buf, NonZero(_sub(a, b)), S_KEY_POLE, P, anc, gd)
    total, trace = None, []
    for a in S:
        m, R = _residue(body, z, a, fac, buf, P, anc, gd)
        trace.append((a, m, 1))
        if R is not None:
            R = discharge._rebuild(R, _log_closed)  # E240
            total = R if total is None else Add(total, R)
    if total is None:
        new = Num(0)
    elif n is not None:
        new = Neg(total)
    else:
        two_pi_i = Mul(_TWO_PI, Const("i"))
        new = Mul(Div(two_pi_i, Add(Num(1), Neg(App("exp", Mul(two_pi_i,
                                                                alpha))))),
                  total)
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, gd, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"trace": tuple(trace)}


# ---------------------------------------------------------------- Z12
#
# p1_expected E243-E244: the sector for the quadratic phase, and the
# Gaussian it rests on, as residues sector on an Int[x = 0 .. oo].

S_SECTOR = "residues_sector"


def _residues_sector(state, args, minted, buf):
    """E243-E244: Int[x = 0 .. oo] c*h, h exp(k*x^2), cos(a*x^2) or
    sin(a*x^2), by Z12's values, each sign owed."""
    g = state.goal[0]
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom)
             if isinstance(s, Integral)]
    if not found:
        raise Refused("residues-no-integral", "the goal holds no integral")
    k = args.get("occurrence")
    if k is not None and k >= len(found):
        raise Refused("residues-no-integral", f"no integral at occurrence {k}")
    if k is None and len(found) > 1:
        raise Refused("residues-ambiguous", f"{len(found)} integrals in the "
                      "goal; give an occurrence")
    side, path, it, P, anc = found[k or 0]
    _open_end(it, "residues sector")
    if not (it.lo == Num(0) and isinstance(it.hi, PosInf)):
        raise Refused("sector-not-half-line", f"{_brief(it)} is not over "
                      "[0, oo) (E244)")
    x, gd = it.var, g.dom
    cst, h = _const_split(it.body, x)
    while type(h) is Neg:  # E249: a sign is a constant factor
        cst, h = _times(Neg(Num(1)), cst) if cst == Num(1) else Neg(cst), h.a
    bad = Refused("sector-not-certified", f"{_brief(it.body)}: Z12 reads c "
                  "times exp(k*x^2), cos(a*x^2) or sin(a*x^2) (E244)")
    if type(h) is not App or h.fn not in ("exp", "cos", "sin"):
        raise bad
    u = h.arg
    kk = subst(u, {x: Num(1)})
    if x in fv(kk) or not _ring_holds(Rel("==", u, Mul(kk, Pow(Var(x), 2)))):
        raise bad
    sqrt_pi = App("sqrt", Const("pi"))
    i = Const("i")
    if h.fn == "exp":
        if _ring_holds(Rel("==", App("re", kk), Num(0))):
            a = App("im", kk)
            up = _verdict(Rel(">", a, Num(0)), P) is not False and \
                _verdict(Rel("<", a, Num(0)), P) is not True
            _owe(buf, Rel(">" if up else "<", a, Num(0)), S_SECTOR, P, anc, gd)
            mag = a if up else Neg(a)
            turn = Div(Mul(i, Const("pi")), Num(4))
            value = Mul(App("exp", turn if up else Neg(turn)),
                        Div(sqrt_pi, Mul(Num(2), App("sqrt", mag))))
        else:  # the Gaussian
            _owe(buf, Rel("==", App("im", kk), Num(0)), S_SECTOR, P, anc, gd)
            _owe(buf, Rel("<", App("re", kk), Num(0)), S_SECTOR, P, anc, gd)
            value = Div(sqrt_pi, Mul(Num(2), App("sqrt", Neg(App("re", kk)))))
    else:
        if complexes.has_complex(kk):
            raise bad
        _owe(buf, Rel(">", kk, Num(0)), S_SECTOR, P, anc, gd)
        value = Div(sqrt_pi, Mul(Num(2), App("sqrt", Mul(Num(2), kk))))
    new = _times(cst, value)
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, gd, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


# ---------------------------------------------------------------- int_re
#
# p1_expected E257-E259: re and im through an Int.

S_REIM = "int_re_check"


def _pv_body_formers(it, P, anc, gd, buf):
    """E272: a PV's body is defined on its range but at finitely many
    points. Each former of the body is owed on the range, except a divisor
    that is a polynomial in the variable over Q(i) (exp factors aside),
    whose finitely many zeros are the PV's excluded points. A divisor that
    ring makes zero refuses (E25)."""
    x = it.var
    rng, orient = _range_of(x, it.lo, it.hi, P)
    if orient is not None:
        _emit(buf, orient, "orient", gd)
    for _, s, d, a in _positions(it.body, P + (rng,), anc):
        for prop, divisor in _owed(s):
            if divisor and type(prop) is NonZero and x in fv(prop.e):
                rest, _us = complexes._exp_factors(
                    subst(prop.e, {x: CVar(x)}))
                p = None if rest is None else roots.poly(rest, x)
                if p is not None and len(p) >= 2:
                    if FD.ring_is_zero(prop.e):
                        raise Refused("divisor-normalises-to-zero", f"the "
                                      f"divisor {show(prop.e)} is zero (E25)")
                    continue
            _emit_at(buf, prop, d, a, S_PV_BODY, gd, divisor)


S_PV_BODY = "pv_body"


def _int_reim(state, args, minted, buf, part):
    """E257: Int[x = a .. b] f as re (im) of Int[x = a .. b] F, when re F
    (im F) == f by field on split parts, its divisors owed on the range."""
    g = state.goal[0]
    found = [(i, p, s, d, a) for i, side in enumerate(_sides(g))
             for p, s, d, a in _positions(side, g.dom)
             if isinstance(s, (Integral, PV))]  # E268: a PV too
    k = args.get("occurrence")
    if not found or (k is not None and k >= len(found)):
        raise Refused("int-re-no-integral", "the goal holds no integral"
                      + (f" at occurrence {k}" if k is not None else ""))
    if k is None and len(found) > 1:  # E264: ambiguity keeps its own code
        raise Refused("int-re-ambiguous", f"{len(found)} integrals in the "
                      "goal; give an occurrence")
    side, path, it, P, anc = found[k or 0]
    x, f, F = it.var, it.body, args["F"]
    if sort_of(f) != "R":
        raise Refused("int-re-real-only", f"{_brief(f)} is complex; int_re "
                      "and int_im read a real integrand (E259)")
    try:
        _subst_scope(g, anc, [("F", F, {x})])
    except Refused as r:
        raise Refused("int-re-scope", r.message) from None
    if anc:
        _subst_under_D(anc, it, (F,))
    P = _decided(buf, P, anc, g.dom)
    rng, orient = _range_of(x, it.lo, it.hi, P)
    if orient is not None:
        _emit(buf, orient, "orient", g.dom)
    a, b = complexes.split(F)
    want = a if part == "re" else b
    want = Num(0) if want is None else complexes._real(want)
    ok = None
    for facts in ([], _parity_facts(Add(want, f))):  # E264: with parity
        try:
            ok = FD.field(want, f, facts)
            break
        except (FD.NotEqual, Refused, RecursionError):
            continue
    if ok is None:
        raise Refused("int-re-check-failed", f"{part} of {_brief(F)} is not "
                      f"{_brief(f)} by field (E257)")
    if not isinstance(it, PV):  # E268: a PV's points are excluded
        for dv in ok.divisors:
            _emit_at(buf, NonZero(dv), P + (rng,), anc, S_REIM, g.dom)
    else:
        _pv_body_formers(it, P, anc, g.dom, buf)  # E272
    new = App(part, type(it)(x, it.lo, it.hi, F))
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, g.dom, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


def _int_re(state, args, minted, buf):
    return _int_reim(state, args, minted, buf, "re")


def _int_im(state, args, minted, buf):
    return _int_reim(state, args, minted, buf, "im")


# ---------------------------------------------------------------- int_parts
#
# p1_expected's INT_PARTS_RULE (section 19, E71-E75): §6.4's rule, for u, v
# in C^1 on the closed range, Int[x = a .. b] u*v' == (u(b)*v(b) -
# u(a)*v(a)) - Int[x = a .. b] u'*v, which holds for either order of a and
# b. Its selector, scope, under-D and orientation steps are int_subst's.

S_PARTS_INT = "int_parts_integrand"
S_PARTS_U, S_PARTS_V = "int_parts_u_C1", "int_parts_v_C1"


def _parts_select(g, var, k):
    """Step 2 (E75): int_subst's selector, with int_parts' codes."""
    try:
        return _select(g, var, k)
    except Refused as r:
        if not r.code.startswith("int-subst-"):
            raise
        raise Refused("int-parts-" + r.code[len("int-subst-"):],
                      r.message) from None


def _parts_scope(g, anc, var, u, v):
    """Step 4 (E75): u and v in scope at the position, plus var."""
    try:
        _subst_scope(g, anc, [("u", u, {var}), ("v", v, {var})])
    except Refused as r:
        if r.code != "int-subst-scope":
            raise
        raise Refused("int-parts-scope", r.message) from None


def _parts_check(check, body, u, v, dv, minted, D, G, buf):
    """Step 9 (E71): body == u*v' at D by `check`, recorded discharged
    ('deriv+' + check, the facts' entries)."""
    rhs = Mul(u, dv)
    try:
        _check(check, body, rhs, minted, D, G, buf, "int-parts-check-failed")
    except Refused as r:
        if r.code != "int-parts-check-failed":
            raise
        raise Refused(r.code, f"the integrand is not u*v' for u := "
                      f"{_brief(u)}, v := {_brief(v)}", r.residual) from None
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    _emit(buf, with_domain(Rel("==", body, rhs), D), S_PARTS_INT, G,
          ("deriv+" + check, cites))


def _parts_term(x, a, b, u, v, du):
    """Step 11: (u(b)*v(b) - u(a)*v(a)) - Int[x = a .. b] u'*v."""
    at = lambda t, e: subst(t, {x: e})  # noqa: E731
    boundary = Add(Mul(at(u, b), at(v, b)), Neg(Mul(at(u, a), at(v, a))))
    return Add(boundary, Neg(Integral(x, a, b, Mul(du, v))))


def _int_parts(state, args, minted, buf):
    """INT_PARTS_RULE steps 2-11. Returns (new goal, None, no extras).
    Everything that can refuse runs in the rule's order, and every
    emission goes through _emit."""
    g = state.goal[0]
    G, var, u, v, check = (g.dom, args["var"], args["u"], args["v"],
                           args["check"])
    side, path, it, P, anc = _parts_select(g, var, args.get("occurrence"))
    _open_end(it, "int_parts")
    for end in (it.lo, it.hi):  # step 3
        if isinstance(end, (PosInf, NegInf)):
            raise Refused("int-parts-infinite-endpoint", "int_parts needs "
                          "finite limits, and "
                          f"{'oo' if isinstance(end, PosInf) else '-oo'} is "
                          "not (int_improper is the route)")
    _no_trees_in_limits(it.lo, it.hi)  # SECOND_REVIEW_RULE
    _parts_scope(g, anc, var, u, v)  # step 4
    _subst_under_D(anc, it, (u, v))  # step 5
    P = _decided(buf, P, anc, G)  # step 6
    old = _old_range(buf, it, P, G)
    D = P + (old,)
    _charge_formers(buf, u, D, G, anc=anc)  # step 7
    _charge_formers(buf, v, D, G, anc=anc)
    du = DV.deriv(u, var, D)  # step 8, on the closed range
    for key, source in du.emissions:
        _emit(buf, key, source, G)
    dv = DV.deriv(v, var, D)
    for key, source in dv.emissions:
        _emit(buf, key, source, G)
    _parts_check(check, it.body, u, v, dv.output, minted, D, G, buf)  # 9
    _emit(buf, with_domain(Reg(u, 1), D), S_PARTS_U, G)  # step 10
    _emit(buf, with_domain(Reg(v, 1), D), S_PARTS_V, G)
    new = _parts_term(var, it.lo, it.hi, u, v, du.output)  # step 11
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, G, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


# ---------------------------------------------------------------- int_improper
#
# p1_expected's section 20 (E76-E80): ftc's premises on a range with an
# infinite end, and at each infinite end the limit of F, computed by the
# trusted limits.py, finite. Convergence is the step's conclusion.

S_IMP_f, S_IMP_F0, S_IMP_F1 = ("int_improper_f_C0", "int_improper_F_C0",
                               "int_improper_F_C1")
S_IMP_D, S_IMP_LIM = "int_improper_D", "int_improper_limit"


def _imp_select(g, k):
    """E76: the goal's lhs Int, or ftc's selector at occurrence k."""
    if k is None:
        if not isinstance(g.lhs, Integral):
            raise Refused("int-improper-no-integral",
                          "int_improper needs an Int as the goal's lhs")
        return None, None, g.lhs, g.dom, ()
    try:
        return _flip_select(g, k)
    except Refused as r:
        raise Refused("int-improper-no-integral", r.message) from None


def _imp_limit(F, x, end, P, G, buf):
    """E77, E78: the finite limit of F as x -> end (oo or -oo), its side
    conditions emitted at P. An infinite limit refuses
    'int-improper-diverges'; none, 'int-improper-limit-unknown'."""
    s = 1 if isinstance(end, PosInf) else -1

    def sign(c):  # a guess that only picks a branch; the side is emitted
        for g, op in ((1, ">"), (-1, "<")):
            try:
                if _settles(with_domain(Rel(op, c, Num(0)), P)):
                    return g
            except Refused:
                pass
        return None
    try:
        value, sides = LM.lim(F, x, s, sign)
    except LM.NoLimit as e:
        raise Refused("int-improper-limit-unknown", f"no limit law gives the "
                      f"limit of {_brief(F)} as {x} -> {'oo' if s > 0 else '-oo'}"
                      f" ({e})") from None
    if value in (LM.POS, LM.NEG):
        raise Refused("int-improper-diverges", f"{_brief(F)} -> {value} as "
                      f"{x} -> {'oo' if s > 0 else '-oo'}, so the integral "
                      "diverges")
    for side in sides:  # E91: a c # 0 side is a divisor, so E25 tests it
        _emit(buf, with_domain(side, P), S_IMP_LIM, G)
    return value


def _imp_open(F, x, end, g, P, G, buf):
    """E226: V at a marked end, the limit of F(a + 1/u) (a+) or F(b - 1/u)
    (b-) as u -> oo, u fresh, by the trusted evaluator (E77)."""
    taken = fv(g) | bv(g) | fv(F)
    u = next(n for n in itertools.chain(
        ("u",), (f"u_{j}" for j in itertools.count(1))) if n not in taken)
    step = Div(Num(1), Var(u))
    step = step if end.side == "+" else Neg(step)
    at = step if end.e == Num(0) else Add(end.e, step)
    return _imp_limit(_whole_normal(_args_normal(subst(F, {x: at}))), u,
                      POS_INF, P, G, buf)


def _too_big(t):
    """E231: a power or a size field's normal form could blow up on."""
    nodes = list(DV._nodes(t))
    return len(nodes) > 400 or any(type(n) is Pow and abs(n.n) > 64
                                   for n in nodes)


def _whole_normal(t):
    """E231: t's field normal form, functions as atoms, where field checks
    the two equal (so 1/(1 + 1/u - 1) reads u), else t."""
    if _too_big(t):
        return t
    try:
        num, den, atoms = FD.field_parts(t)
        new = residual.residual_term(_Parts(num, den, atoms))
        FD.field(t, new)
        return new
    except (FD.NotEqual, Refused, RecursionError):
        return t


def _args_normal(t):
    """t with each function's argument replaced by its field normal form
    where field checks the two equal, so 1 - (1 - 1/u) reads 1/u (E226).
    Equal as rational functions, they agree for all large u, so the limit
    is unchanged; an argument field cannot normalise is kept, and so is
    one past E231's size bound."""
    if _too_big(t):
        return t
    if isinstance(t, (App, Branch)):
        arg = _args_normal(t.arg)
        try:
            num, den, atoms = FD.field_parts(arg)
            new = residual.residual_term(_Parts(num, den, atoms))
            FD.field(arg, new)
            return replace(t, arg=new)
        except (FD.NotEqual, Refused, RecursionError):
            return replace(t, arg=arg)
    kids = {n: _args_normal(c) for n, c in children(t) if isinstance(c, Term)}
    return replace(t, **kids) if kids and not isinstance(t, Call) else t


def _imp_scope(g, anc, x, F):
    """E92: F in scope at the selected Int's position, plus its variable,
    as E84 checks ftc's."""
    try:
        _subst_scope(g, anc, [("F", F, {x})])
    except Refused as r:
        if r.code != "int-subst-scope":
            raise
        raise Refused("int-improper-scope", r.message) from None


def _int_improper(state, args, minted, buf):
    """E76: ftc's premises on the range, then the limits. Returns (new
    goal, None, deriv's trace and output)."""
    g = state.goal[0]
    G, F, check = g.dom, args["F"], args["check"]
    side, path, it, P, anc = _imp_select(g, args.get("occurrence"))
    _imp_scope(g, anc, it.var, F)  # E92
    ends = (it.lo, it.hi)
    if not any(isinstance(e, (PosInf, NegInf, Open)) for e in ends):
        raise Refused("int-improper-finite", "both limits are finite and "
                      "unmarked; ftc is the move")
    _no_trees_in_limits(*(e for e in ends if isinstance(e, Term)))
    if anc:
        _subst_under_D(anc, it, (F,))  # E48, as ftc at an occurrence
    P = _decided(buf, P, anc, G)
    x, f = it.var, it.body
    rng, orient = _range(it, P)
    if orient is not None:
        _emit(buf, orient, "orient", G)
    on_rng = P + (rng,)
    on_open = P + (Interval(x, rng.lo, False, rng.hi, False),)
    _charge_formers(buf, F, on_rng, G)
    _emit(buf, with_domain(Reg(F, 0), on_rng), S_IMP_F0, G)
    d = DV.deriv(F, x, on_open)
    for key, source in d.emissions:
        _emit(buf, key, source, G)
    _check(check, d.output, f, minted, on_open, G, buf,
           "int-improper-check-failed")
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    _emit(buf, with_domain(Reg(F, 1), on_open), S_IMP_F1, G)
    _emit(buf, with_domain(Rel("==", Deriv(x, F), f), on_open), S_IMP_D, G,
          ("deriv+" + check, cites))
    _emit(buf, with_domain(Reg(f, 0), on_rng), S_IMP_f, G)
    va, vb = (_imp_limit(F, x, e, P, G, buf) if isinstance(e, (PosInf, NegInf))
              else _imp_open(F, x, e, g, P, G, buf) if type(e) is Open
              else subst(F, {x: e}) for e in ends)
    new = Add(vb, Neg(va))  # V(b) - V(a)
    if path is None:
        goal = (replace(g, lhs=new),)
        for sd in _sides(goal[0]):
            _charge_formers(buf, sd, G, G)
    else:
        sides = list(_sides(g))
        sides[side] = _put(sides[side], path, new)
        _charge_formers(buf, new, P, G, anc=anc)
        goal = (replace(g, lhs=sides[0],
                        rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {"trace": d.trace, "output": d.output}


# ---------------------------------------------------------------- Taylor
#
# p1_expected section 25: taylor_lagrange (E97, E98) and bound (E99).

S_TAYLOR_ORDER, S_TAYLOR_F_C = "taylor_order", "taylor_f_C"
S_TAYLOR_D_C0, S_TAYLOR_D = "taylor_D_C0", "taylor_D"
S_TAYLOR_MONO = "taylor_monotone"
S_BOUND_SCALE = "bound_scale"
# E97, and E138's strict senses: (the monotone premise's relation, strict)
TAYLOR_SENSES = {"increasing": (">=", False), "decreasing": ("<=", False),
                 "strictly increasing": (">", True),
                 "strictly decreasing": ("<", True)}


def _taylor_scope(g, u, f, derivs, ends):
    """E97: u is neither free nor bound in the goal; f and each D_k mention
    only the goal's variables and u; lo, hi and at only the goal's."""
    names = fv(g)
    if u in names or u in bv(g):
        raise Refused("taylor-scope", f"{u} is a variable of the goal; the "
                      "expansion variable must be new")
    for t in (f, *derivs):
        out = fv(t) - names - {u}
        if out:
            raise Refused("taylor-scope", f"{show(t)} mentions "
                          f"{', '.join(sorted(out))}, not in the goal")
    for t in ends:
        out = fv(t) - names
        if out:
            raise Refused("taylor-scope", f"{show(t)} mentions "
                          f"{', '.join(sorted(out))}, not in the goal")


def _taylor_poly(Ds, u, a, p, n):
    """T = sum over k = 0 .. n of D_k[u := a] (p - a)^k / k!, and W = (p -
    a)^(n+1) / (n+1)! (E97)."""
    h = Add(p, Neg(a))

    def term(coef, k):
        if k == 0:
            return coef
        t = Mul(coef, h if k == 1 else Pow(h, k))
        f = 1
        for i in range(2, k + 1):
            f *= i
        return t if f == 1 else Div(t, Num(f))
    T = subst(Ds[0], {u: a})
    for k in range(1, n + 1):
        T = Add(T, term(subst(Ds[k], {u: a}), k))
    W = term(Num(1), n + 1)
    return T, W


def _taylor(state, args, minted, buf):
    """E97, E98: taylor_lagrange's premises, in E98's order, then the
    minted handle for the chosen side. The goal does not change."""
    g = state.goal[0]
    G, u, f, check = g.dom, args["var"], args["f"], args["check"]
    a, c, p = args["lo"], args["hi"], args["at"]
    derivs = tuple(args["derivs"])
    _taylor_scope(g, u, f, derivs, (a, c, p))
    Ds = (f, *derivs)
    n = len(derivs) - 2
    on_I = G + (Interval(u, a, True, c, False),)
    on_O = G + (Interval(u, a, False, c, False),)
    for t in (a, c, p):  # E107: the ends and the point enter at G first
        _charge_formers(buf, t, G, G)
    mono, strict = TAYLOR_SENSES[args["sense"]]
    _emit(buf, with_domain(Rel("<" if strict else "<=", a, p), G),
          S_TAYLOR_ORDER, G)  # E138: a strict sense needs p past a
    _emit(buf, with_domain(Rel("<", p, c), G), S_TAYLOR_ORDER, G)
    for t in Ds:
        _charge_formers(buf, t, on_I, G)
    _emit(buf, with_domain(Reg(f, n + 2), on_I), S_TAYLOR_F_C, G)
    for k in range(1, n + 2):
        _emit(buf, with_domain(Reg(Ds[k], 0), on_I), S_TAYLOR_D_C0, G)
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    for k in range(n + 2):
        d = DV.deriv(Ds[k], u, on_O)
        for key, source in d.emissions:
            _emit(buf, key, source, G)
        _check(check, d.output, Ds[k + 1], minted, on_O, G, buf,
               "taylor-check-failed")
        _emit(buf, with_domain(Rel("==", Deriv(u, Ds[k]), Ds[k + 1]), on_O),
              S_TAYLOR_D, G, ("deriv+" + check, cites))
    up = mono in (">=", ">")
    _emit(buf, with_domain(Rel(mono, Ds[n + 2], Num(0)), on_O),
          S_TAYLOR_MONO, G)
    T, W = _taylor_poly(Ds, u, a, p, n)
    R = Add(subst(f, {u: p}), Neg(T))
    left, right = (a, p) if up else (p, a)
    op = "<" if strict else "<="
    if args["side"] == "lower":
        conclusion = Rel(op, Mul(subst(Ds[n + 1], {u: left}), W), R)
    else:
        conclusion = Rel(op, R, Mul(subst(Ds[n + 1], {u: right}), W))
    for side in (conclusion.lhs, conclusion.rhs):
        _charge_formers(buf, side, G, G)
    check_goal((conclusion,))
    h = Handle(next(_IDS), state.lineage)
    _MINTED[h.id] = _Minted(h, state.lineage, with_domain(conclusion, G),
                            "taylor_lagrange")
    return state.goal, None, {"handle": h}


def _as_order(j):
    """A Rel of ORDERINGS as (lo, hi, strict): lo < hi or lo <= hi."""
    a, b = j.lhs, j.rhs
    return {"<": (a, b, True), "<=": (a, b, False),
            ">": (b, a, True), ">=": (b, a, False)}[j.op]


def _bound(state, args, minted, buf):
    """E99: close an order goal from exactly one order fact, hi - lo ==
    d' - c' by the check with the equation facts. The fact's hypotheses
    that are not items of the goal's domain are emitted there; one that is
    an interval is refused. Returns (None, the original goal, no extras)."""
    g = state.goal[0]
    G = g.dom
    order = [r for r in minted if isinstance(r.conclusion, Rel)
             and r.conclusion.op in ORDERINGS]
    if len(order) != 1:
        raise Refused("bound-fact-shape", "bound takes exactly one fact that "
                      f"is an order judgement; {len(order)} given")
    rec, = order
    eqs = [r for r in minted if r is not rec]
    if args["check"] == "ring" and eqs:
        raise Refused("bad-args", "ring takes no facts but the order one")
    lo, hi, strict = _as_order(g)
    c, d, fstrict = _as_order(rec.conclusion)
    if strict and not fstrict:
        raise Refused("bound-strictness", "a strict goal needs a strict fact")
    for h in rec.conclusion.dom:
        if h in G:
            continue
        if not isinstance(h, (Rel, NonZero)):
            raise Refused("bound-fact-shape", f"the fact's hypothesis "
                          f"{_brief(h)} is not in the goal's domain")
    diff = Add(d, Neg(c))
    if "scale" in args:  # E139: hi - lo == s*(d' - c'), s > 0 at G
        s = args["scale"]
        _charge_formers(buf, s, G, G)
        diff = Mul(s, diff)
    _check(args["check"], Add(hi, Neg(lo)), diff, eqs, G, G, buf,
           "bound-check-failed")
    if "scale" in args:
        _emit(buf, with_domain(Rel(">", args["scale"], Num(0)), G),
              S_BOUND_SCALE, G)
    for v in rec.inst:
        _charge_formers(buf, v, G, G)
    for h in rec.conclusion.dom:
        if h not in G:
            _emit(buf, with_domain(h, G), "fact_hyp", G)
    theorem = state.original
    check_goal(theorem)
    return None, theorem, {}


# ---------------------------------------------------------------- verify
#
# p1_expected section 26 (E112-E115): §6.5's ode_verify in general form.

def _verify_nodes(side, G):
    """E113: the D nodes of one side, in pre-order, as (path, node). A D node
    inside an Int refuses 'verify-D-under-binder', and one whose body holds
    a D node 'verify-nested-D'. A D node in an Int's limit is outside the
    Int's scope, so it has no Int ancestor and is replaced like any other
    (E128)."""
    found = []
    for path, t, _, anc in _positions(side, G):
        if not isinstance(t, Deriv):
            continue
        if any(isinstance(a, _IntScope) for a in anc):
            raise Refused("verify-D-under-binder", f"{_brief(t)} is inside "
                          "an Int; verify rewrites D nodes at the goal's "
                          "domain only")
        if anc or any(isinstance(n, Deriv) for n in trees(t.body)):
            raise Refused("verify-nested-D", f"{_brief(t)} is a D node "
                          "inside another, or holds one (E124: second "
                          "derivatives are not built)")
        found.append((path, t))
    return found


def _verify(state, args, minted, buf):
    """E112-E114. Every D[x] e of either side is replaced by deriv(e, x, G)'s
    output, its emissions at G under deriv's rule names; the new sides'
    formers are charged at G; then close's _check proves l' == r' at G.
    Returns (None, the original goal, no extras)."""
    g = state.goal[0]
    if isinstance(g.rhs, MVar):
        raise Refused("verify-has-mvar", "verify closes an equation with no "
                      "?A; an unknown is found by close")
    G = g.dom
    sides = [g.lhs, g.rhs]
    for i in (0, 1):
        found = [(path, DV.deriv(node.body, node.var, G))
                 for path, node in _verify_nodes(sides[i], G)]
        for _, d in found:  # emitted in pre-order (E113)
            for key, source in d.emissions:
                _emit(buf, key, source, G)
        # Replaced from the last node back, so earlier paths stay valid:
        # a later pre-order node is never an ancestor of an earlier one,
        # and no node here holds another (E113).
        for path, d in reversed(found):
            sides[i] = _put(sides[i], path, d.output)
    for side in sides:
        _charge_formers(buf, side, G, G)
    _check(args["check"], sides[0], sides[1], minted, G, G, buf,
           "verify-check-failed")
    theorem = state.original
    check_goal(theorem)
    return None, theorem, {}


# ---------------------------------------------------------------- ODE rules
#
# p1_expected section 30 (E147-E155): §6.5's quad_t, sep_autonomous and
# energy_integral, reading Γ's laws on declared functions.

_ODE_MOVES = ("quad_t", "sep_autonomous", "energy_integral")
S_ODE_CONTAIN, S_ODE_RANGE, S_ODE_LAW = "ode_contain", "ode_range", \
    "ode_law"
S_ODE_F_C0, S_ODE_F_C1, S_ODE_D = "ode_F_C0", "ode_F_C1", "ode_D"


def _ode_get(gamma, name, kind):
    """E149: the Assumption named `name`, of that kind, or
    'ode-no-assumption'."""
    for a in gamma:
        if a.name == name:
            if _assume_kind(a.judgement, a.var) == kind:
                return a
            raise Refused("ode-no-assumption", f"{name} is not a {kind} "
                          "assumption")
    raise Refused("ode-no-assumption", f"no assumption is named {name!r}")


def _ode_law(a):
    """E149: a law c*D[s] y(s) == R as (s, c, y, R), c = 1 for a bare D.
    c is free of s and holds no Call or D; otherwise 'ode-law-shape'."""
    j, s = a.judgement, a.var
    lhs, c = j.lhs, Num(1)
    if type(lhs) is Mul and type(lhs.b) is Deriv:
        c, lhs = lhs.a, lhs.b
    if type(lhs) is not Deriv or list(trees(j.rhs)):
        raise Refused("ode-law-shape", f"{a.name}: the law is not c*D[{s}] "
                      f"y({s}) == R with no D in R")
    if s in fv(c) or _has_call(c) or list(trees(c)):
        raise Refused("ode-law-shape", f"{a.name}: its coefficient "
                      f"{_brief(c)} mentions {s}, a Call or a D")
    return s, c, lhs.body.fn, j.rhs


def _ode_matches(a, R, f, var, y):
    """E152, E153 as E156 amends them: R is field-equal to f[var := y(s)],
    f holding no Call; otherwise 'ode-law-mismatch'. Returns field's
    divisors, which the caller owes nonzero at s (E156)."""
    if _has_call(f):
        raise Refused("ode-law-mismatch", f"f = {_brief(f)} holds a Call")
    want = subst(f, {var: y})
    try:
        return FD.field(R, want).divisors
    except FD.NotEqual:
        raise Refused("ode-law-mismatch", f"{a.name}'s rhs {_brief(R)} is "
                      f"not f at {_brief(y)}, {_brief(want)}") from None


def _ode_regs(gamma, names, fns):
    """E149: for each declared function in fns, the first reg in `names`
    of class >= 1 on it; 'ode-no-regularity' when there is none."""
    regs = [_ode_get(gamma, n, "reg") for n in names]
    out = []
    for fn in fns:
        found = [r for r in regs if r.judgement.e.fn == fn]
        if not found:
            raise Refused("ode-no-regularity", f"no reg among "
                          f"{', '.join(names) or 'none'} is on {fn}")
        out.append(found[0])
    return out


def _ode_scope(g, var, law_vars, terms, ends):
    """E149: var is fresh (not free or bound in the goal, not a law's
    variable); F and f mention only the goal's variables and var and hold
    no Call; lo and hi only the goal's variables."""
    names = fv(g)
    if var in names or var in bv(g) or var in law_vars:
        raise Refused("ode-scope", f"{var} is a variable of the goal or of "
                      "the law; the antiderivative's variable must be new")
    for t in terms:
        out = fv(t) - names - {var}
        if out or _has_call(t):
            raise Refused("ode-scope", f"{_brief(t)} mentions "
                          f"{', '.join(sorted(out)) or 'a Call'}, not the "
                          "goal's")
    for t in ends:
        out = fv(t) - names
        if out:
            raise Refused("ode-scope", f"{_brief(t)} mentions "
                          f"{', '.join(sorted(out))}, not in the goal")


def _ode_contain(buf, t0, t1, read, G):
    """E150: t0 <= t1, then each read assumption's finite ends against [t0,
    t1], at G."""
    _emit(buf, with_domain(Rel("<=", t0, t1), G), S_ODE_CONTAIN, G)
    for a in read:
        i = a.interval
        if isinstance(i.lo, Term):
            _emit(buf, with_domain(Rel("<=" if i.lo_closed else "<", i.lo,
                                       t0), G), S_ODE_CONTAIN, G)
        if isinstance(i.hi, Term):
            _emit(buf, with_domain(Rel("<=" if i.hi_closed else "<", t1,
                                       i.hi), G), S_ODE_CONTAIN, G)


def _ode_at(a, point):
    """An order assumption's judgement at `point` (E154)."""
    return subst(a.judgement, {a.var: point})


def _ode_range_items(rng, y):
    """E152: a < y and y < b for rng's finite ends."""
    out = []
    if isinstance(rng.lo, Term):
        out.append(Rel("<", rng.lo, y))
    if isinstance(rng.hi, Term):
        out.append(Rel("<", y, rng.hi))
    return out


def _ode_deriv(buf, F, var, target, on_open, check, minted, G):
    """E149: D[var] F == target on on_open by deriv and the check, with
    Reg(F, 1) there; target's formers charged there first."""
    _charge_formers(buf, target, on_open, G)
    later = {}
    d = DV.deriv(F, var, on_open)
    for key, source in d.emissions:
        _emit(later, key, source, G)
    _check(check, d.output, target, minted, on_open, G, later,
           "ode-check-failed")
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    _emit(buf, with_domain(Reg(F, 1), on_open), S_ODE_F_C1, G)
    _emit(buf, with_domain(Rel("==", Deriv(var, F), target), on_open),
          S_ODE_D, G, ("deriv+" + check, cites))
    for ob in later.values():
        buf[ob.key] = _merged(buf.get(ob.key), ob)


def _ode_mint(state, conclusion, cdom, G, rule, buf):
    """The conclusion's formers at cdom, then the handle (E149)."""
    for side in (conclusion.lhs, conclusion.rhs):
        _charge_formers(buf, side, cdom, G)
    check_goal((conclusion,))
    h = Handle(next(_IDS), state.lineage)
    _MINTED[h.id] = _Minted(h, state.lineage, with_domain(conclusion, G),
                            rule)
    return state.goal, None, {"handle": h}


def _quad_t(state, args, minted, buf):
    """E151: c*y' == R(s), R free of Calls; y(t1) == y(t0) + F(t1) - F(t0)."""
    g = state.goal[0]
    G, gamma, var, F = g.dom, _GAMMA.get(state.lineage, ()), args["var"], \
        args["F"]
    t0, t1 = args["lo"], args["hi"]
    law = _ode_get(gamma, args["law"], "law")
    _ode_scope(g, var, {law.var}, (F,), (t0, t1))
    s, c, y, R = _ode_law(law)
    if _has_call(R):
        raise Refused("ode-law-mismatch", f"{law.name}'s rhs {_brief(R)} "
                      "holds a Call; quad_t integrates a function of the "
                      "time alone")
    reg, = _ode_regs(gamma, args["regs"], (y,))
    for t in (t0, t1):
        _charge_formers(buf, t, G, G)
    _ode_contain(buf, t0, t1, (law, reg), G)
    on_closed = G + (Interval(var, t0, True, t1, True),)
    on_open = G + (Interval(var, t0, False, t1, False),)
    _charge_formers(buf, F, on_closed, G)
    _emit(buf, with_domain(Reg(F, 0), on_closed), S_ODE_F_C0, G)
    target = subst(R, {s: Var(var)})
    target = target if c == Num(1) else Div(target, c)
    _ode_deriv(buf, F, var, target, on_open, args["check"], minted, G)
    Y = lambda t: Call(y, (t,))
    conclusion = Rel("==", Y(t1), Add(Y(t0), Add(subst(F, {var: t1}),
                                                 Neg(subst(F, {var: t0})))))
    return _ode_mint(state, conclusion, G, G, "quad_t", buf)


def _ode_autonomous(state, args, minted, buf, energy):
    """E152 (sep_autonomous) and E153 (energy_integral)."""
    g = state.goal[0]
    G, gamma, var = g.dom, _GAMMA.get(state.lineage, ()), args["var"]
    F, f, rng, t0, t1 = args["F"], args["f"], args["range"], args["lo"], \
        args["hi"]
    law = _ode_get(gamma, args["law"], "law")
    kin = _ode_get(gamma, args["kin"], "law") if energy else None
    law_vars = {law.var} | ({kin.var} if energy else set())
    _ode_scope(g, var, law_vars, (F, f), (t0, t1, *(
        e for e in (rng.lo, rng.hi) if isinstance(e, Term))))
    using = [_ode_get(gamma, n, "order") for n in args["using"]]
    s, c, y, R = _ode_law(law)
    if energy:
        ks, kc, x, kr = _ode_law(kin)
        if not (ks == s and kc == Num(1) and kr == Call(y, (Var(s),))
                and x != y):
            raise Refused("ode-law-shape", f"{kin.name} is not D[{s}] x({s}) "
                          f"== {y}({s}) for a function x other than {y}")
        moving = x
    else:
        moving = y
    Ys = Call(moving, (Var(s),))
    divisors = _ode_matches(law, R, f, var, Ys)
    regs = _ode_regs(gamma, args["regs"], (x, y) if energy else (y,))
    for t in (t0, t1):
        _charge_formers(buf, t, G, G)
    _ode_contain(buf, t0, t1, (law, *([kin] if energy else []), *regs,
                               *using), G)
    at_s = G + (Interval(s, t0, True, t1, True),) + tuple(
        _ode_at(u, Var(s)) for u in using)
    for item in _ode_range_items(rng, Ys):
        _emit(buf, with_domain(item, at_s), S_ODE_RANGE, G)
    for d in divisors:  # E156: the law's match holds where these are nonzero
        _emit(buf, with_domain(NonZero(d), at_s), S_ODE_LAW, G)
    _charge_formers(buf, c, G, G)  # E159: the law's sides owe their formers
    _charge_formers(buf, R, at_s, G)  # where the rule reads it, as quad_t's
    on_rng = G + (rng,)
    _charge_formers(buf, F, on_rng, G)
    target = f if energy else Div(c, f)
    _ode_deriv(buf, F, var, target, on_rng, args["check"], minted, G)
    X = lambda t: Call(moving, (t,))
    dF = Add(subst(F, {var: X(t1)}), Neg(subst(F, {var: X(t0)})))
    if energy:
        V = lambda t: Pow(Call(y, (t,)), 2)
        conclusion = Rel("==", V(t1), Add(V(t0), Mul(Div(Num(2), c), dF)))
    else:
        conclusion = Rel("==", t1, Add(t0, dF))
    cdom = G + tuple(_ode_range_items(rng, X(t0))) + tuple(
        _ode_range_items(rng, X(t1))) + tuple(
        _ode_at(u, t) for t in (t0, t1) for u in using)
    rule = "energy_integral" if energy else "sep_autonomous"
    return _ode_mint(state, conclusion, cdom, G, rule, buf)


def _sep_autonomous(state, args, minted, buf):
    return _ode_autonomous(state, args, minted, buf, False)


def _energy_integral(state, args, minted, buf):
    return _ode_autonomous(state, args, minted, buf, True)


_MOVE = {"rewrite": _rewrite, "fact": _fact, "ftc": _ftc, "close": _close,
         "int_subst": _int_subst, "int_flip": _int_flip,
         "int_parts": _int_parts, "int_improper": _int_improper,
         "taylor_lagrange": _taylor, "bound": _bound, "verify": _verify,
         "quad_t": _quad_t, "sep_autonomous": _sep_autonomous,
         "energy_integral": _energy_integral, "cint_param": _cint_param,
         "residues": _residues, "int_even": _int_even,
         "int_re": _int_re, "int_im": _int_im}
