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
import weakref
from dataclasses import dataclass, replace
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
from entries import ENTRIES
from terms import (NEG_INF, POS_INF, Add, App, Deriv, Div, Integral, Mul,
                   Interval, MVar, Neg, NegInf, NonZero, Num, PosInf, Pow,
                   Refused, Reg, Rel, RPow, Term, Var, _shown, bv, check_goal,
                   check_names, children, fv, instantiate, parse_term,
                   show, show_goal, statable, subst, trees, with_domain)

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
         "int_parts", "int_improper")

# The documented public API. No name here returns a ProofState from a str,
# bytes or dict (FORGERIES json_roundtrip_state, no_loader).
__all__ = ("HANDLES_IN_FORCE", "DISCHARGED", "ADMITTED", "OPEN",
           "REASON_REG", "REASON_NONE", "REASON_REJECTED", "REASON_EMPTY",
           "DECIDED_FALSE", "VERDICT", "MOVES", "Refusal", "Obligation",
           "StepRecord", "Handle", "ProofState", "install", "step", "report",
           "derivative_domain")


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


_MINTED = {}  # handle id -> _Minted
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
        change (E8).
        """
        k = emission.key
        self._entries[k] = _merged(self._entries.get(k), emission)

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

def install(goal):
    """Start a proof of `goal`, a Goal tree (usually from parse_goal).

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
        g = goal[0]
        if not (isinstance(g, Rel) and g.op == "=="):
            raise Refused("goal-shape", "the moves here prove an equation")
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
    except Refused as r:
        return Refusal(r.code, r.message, r.residual)
    tracker = _Tracker()
    for ob in buf.values():
        tracker.add(ob)
    return ProofState(_TOKEN, goal, goal, next(_LINEAGES), tracker,
                      StepRecord("install", tuple(buf.values())))


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
         "int_improper": ("F", "check", "facts")}
_TERM_ARGS = ("at", "F", "value", "sub", "lo", "hi", "f", "u", "v")


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
                                           "int_parts", "int_improper")
                else set())
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
                       "int_improper"):
        facts = args["facts"]
        ok = (type(args["check"]) is str and args["check"] in ("ring", "field")
              and type(facts) in (list, tuple)
              and not (args["check"] == "ring" and facts))
    if ok and move in ("int_flip", "ftc", "int_improper"):  # E51, E73
        ok = args.get("occurrence", 0) >= 0
    if ok and move == "int_parts":  # INT_PARTS_RULE step 1
        ok = args.get("occurrence", 0) >= 0 and _names_variable(args["var"])
    if ok and move == "int_subst":
        ok = (type(args.get("mode", "forward")) is str
              and args.get("mode", "forward") in ("forward", "reverse")
              and args.get("occurrence", 0) >= 0
              and _names_variable(args["var"]) and _names_variable(args["new_var"]))
    if not ok:
        raise Refused("bad-args", f"{move} takes {', '.join(sorted(need))}"
                      if need else f"{move} takes no argument but occurrence")
    given = [args[k] for k in _TERM_ARGS if k in args] + list(inst.values())
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
        if (move in ("int_subst", "int_parts", "int_improper")
                and _holds_infinity(t)):
            raise Refused("bad-args", f"{show(t)} mentions oo")
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
    and E56's planted bugs replace it in a child process."""
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
    inner_dom, inner_anc = dom, anc + ((t,) if isinstance(t, Deriv) else ())
    if isinstance(t, Integral):
        if _symbolic(t.lo, t.hi):
            scope = _IntScope(t, Interval(t.var, t.lo, True, t.hi, True), True)
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
    if said:
        return Obligation(key, sources, DISCHARGED, ("norm_num", used))
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
    near every point of P, so D[x] e denotes there (E64). A seam
    (ARCHITECTURE.md §7)."""
    _emit_at(buf, Reg(dx.body, 1), dom, anc, "former", goal_dom)


S_TRIG = "trig_norm"  # E88: a trig_norm instance's hypotheses
TRIG_MAX = 64  # the most instances a proposal may hold


def _trig_instances(lhs, rhs, facts):
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
    if isinstance(t, (MVar, PosInf, NegInf, Integral, Deriv)):
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
    for t in (*inst.values(), at):
        if any(isinstance(n, Integral) and not statable(n) for n in trees(t)):
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
    e, inst, at = ENTRIES.get(args["entry"]), args["inst"], args["at"]
    if e is None or e.statement.op != "==" or set(inst) != set(e.schema):
        raise Refused("bad-args", "rewrite takes an equation entry and "
                      "exactly its schema's variables")
    st = e.statement  # a Rel (entries._load); pi_pos is not an equation
    lhs, rhs = subst(st.lhs, inst), subst(st.rhs, inst)  # step 1
    hyps = [subst(h, inst) for h in e.hyps]
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


def _fact(state, args, minted, buf):
    """E10: mint and register a Handle for ENTRIES[entry].statement[inst],
    hypotheses kept as its domain, and the inst values beside it. Emits
    nothing: whoever uses the handle inherits the hypotheses and the inst
    values' formers (E6, E26 (a)), charged by _check at that step's domain.
    The statement's own formers are not re-charged: over schema variables
    each is the entry's hypothesis or always true, and the library
    statement is trusted (§6.8)."""
    e, inst = ENTRIES.get(args["entry"]), args["inst"]
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
    return any(isinstance(k, (PosInf, NegInf)) for s in _subterms(t)
               for _, k in children(s))


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
    _no_trees_in_limits(it.lo, it.hi)  # SECOND_REVIEW_RULE
    _flip_under_D(anc, it)  # step 3
    new = _flipped(it)  # step 4
    sides = list(_sides(g))
    sides[side] = _put(sides[side], path, new)
    _charge_formers(buf, new, P, g.dom, anc=anc)
    goal = (replace(g, lhs=sides[0], rhs=sides[1] if len(sides) > 1 else g.rhs),)
    check_goal(goal)
    return goal, None, {}


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
    for side in sides:
        _emit(buf, with_domain(side, P), S_IMP_LIM, G,
              divisor=not isinstance(side, NonZero))
    return value


def _int_improper(state, args, minted, buf):
    """E76: ftc's premises on the range, then the limits. Returns (new
    goal, None, deriv's trace and output)."""
    g = state.goal[0]
    G, F, check = g.dom, args["F"], args["check"]
    side, path, it, P, anc = _imp_select(g, args.get("occurrence"))
    ends = (it.lo, it.hi)
    if not any(isinstance(e, (PosInf, NegInf)) for e in ends):
        raise Refused("int-improper-finite", "both limits are finite; ftc "
                      "is the move")
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


_MOVE = {"rewrite": _rewrite, "fact": _fact, "ftc": _ftc, "close": _close,
         "int_subst": _int_subst, "int_flip": _int_flip,
         "int_parts": _int_parts, "int_improper": _int_improper}
