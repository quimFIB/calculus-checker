"""The kernel: proof states, the rules P1 needs, and `step`.

Trusted (DESIGN.md §15.2 items 2, 3 and 5). This file holds the rules
(`rewrite`, `fact`, `ftc`, `close`, and §6.1's refl/trans/cong inside them,
p1_expected E16), the matcher and instantiator (REWRITE_RULE), the
obligation tracker, and §15.3's handles. kernel/ARCHITECTURE.md §4 is the
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
included (E8), and has one of three statuses. Discharge is stubbed (WHAT.md),
so a side condition that norm_num does not close becomes an admission when
it is emitted. Its reason is ADMISSION_REASON, and its tag comes from the
untrusted tagger. 'open' is a status the tracker knows and this milestone
never produces.

**refl, trans and cong** (§6.1) are not moves (E16). trans is the linear
proof state: each accepted step replaces the goal by one proved equal to it.
cong is the matcher's congruence step (REWRITE_RULE step 5), so it inherits
the D[x] restriction. refl is `close` proving lhs == value by its check.

**Untrusted imports.** There are three, and none of them can yield a
theorem: tagger (tags are relied on for nothing), residual (it renders the
residual of a refused step) and schema (the closed whitelist, which only
sets how strong a statement is, §9).

**Definedness** (p1_expected E6, E26 (a)). A former owes its condition
where its term enters the proof: '/' and negative powers their divisor
d # 0, RPow its base > 0, and each partial builtin its natural domain
(NATURAL_DOMAINS: ln u owes u > 0, sqrt u owes u >= 0, and so on). ring's
identities hold only where every atom is defined, so a builtin that owed
nothing would let ring cancel an undefined atom (0*ln(-1) == ?A would close
as 'Proved.'). Integral and Deriv nodes have no condition the kernel can
state, and field.py refuses to normalise them instead (E26 (b)).

**Seams** (ARCHITECTURE.md §7). `derivative_domain`, `_Tracker.add`,
`NATURAL_DOMAINS`, `_encloses` and `_charge_formers` are ordinary code that
the planted-bug and definedness-mutation runs replace in a child process.
Keep their names and signatures. Call them only as written below, and never
bind them anywhere else.
"""

import itertools
import weakref
from dataclasses import dataclass, replace
from types import MappingProxyType

import deriv as DV
import field as FD
import residual
import schema
import tagger
from entries import ENTRIES
from terms import (NEG_INF, POS_INF, Add, App, Deriv, Div, Integral,
                   Interval, MVar, Neg, NegInf, NonZero, Num, PosInf, Pow,
                   Refused, Reg, Rel, RPow, Term, _shown, bv, check_goal,
                   check_names, children, fv, instantiate, lit, show,
                   show_goal, subst, trees, with_domain)

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
ADMISSION_REASON = "discharge not built"  # WHAT.md, Stubbed
VERDICT = "Proved modulo {n} admissions"
MOVES = ("rewrite", "fact", "ftc", "close")

# The documented public API. No name here returns a ProofState from a str,
# bytes or dict (FORGERIES json_roundtrip_state, no_loader).
__all__ = ("HANDLES_IN_FORCE", "DISCHARGED", "ADMITTED", "OPEN",
           "ADMISSION_REASON", "VERDICT", "MOVES", "Refusal", "Obligation",
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
    reason   ADMISSION_REASON for an admission, else None
    """
    key: object
    sources: frozenset
    status: str
    tag: tuple
    reason: object = None


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
    builds each Integral's E4 range, refusing 'range-same-infinity'. It then
    charges the formers of each goal hypothesis at the hypotheses before it,
    so `@ x > 0, ln x > 0` owes x > 0 @ x > 0, and every former of the
    judgement's sides at its position domain (E6: '/' and negative powers
    give d # 0, RPow bases give b > 0; E26: each partial builtin its
    NATURAL_DOMAINS items; source 'former'), with E25 and E7. The
    orientation of a range is emitted only when some key's domain uses it. Returns the first ProofState, with a
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
         "ftc": ("F", "check", "facts"), "close": ("value", "check", "facts")}


def _check_args(move, args, goal):
    """'bad-args' unless args has exactly the move's keys (rewrite may add
    `occurrence`), each of the right type. A term argument must be a Term
    with no ?A, and check_goal must accept it as a side (its GRAMMAR code
    otherwise), so every term that can enter the goal is well formed. With
    the goal, the terms must pass check_names as one statement."""
    need = set(_ARGS[move])
    ok = type(args) is dict and need <= set(args) <= need | (
        {"occurrence"} if move == "rewrite" else set())
    inst = args.get("inst", {}) if ok else None
    ok = ok and type(inst) is dict and all(type(k) is str for k in inst)
    ok = ok and all(type(args[k]) is str
                    for k in ("entry", "bind") if k in args)
    ok = ok and type(args.get("occurrence", 0)) is int
    if ok and move in ("ftc", "close"):
        facts = args["facts"]
        ok = (type(args["check"]) is str and args["check"] in ("ring", "field")
              and type(facts) in (list, tuple)
              and not (args["check"] == "ring" and facts))
    if not ok:
        raise Refused("bad-args", f"{move} takes {', '.join(sorted(need))}")
    given = [args[k] for k in ("at", "F", "value") if k in args] + list(
        inst.values())
    for t in given:  # check_goal first: it refuses a malformed node unread
        if not isinstance(t, Term):
            raise Refused("bad-args", f"not a term without ?A: {_shown(t)}")
        try:
            check_goal((Rel("==", t, t),))
        except Refused as r:
            if r.code != "mvar-misplaced":
                raise
            raise Refused("bad-args", f"not a term without ?A: "
                          f"{_shown(t)}") from None
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

@dataclass(frozen=True, slots=True)
class _IntScope:
    """An Int enclosing a position through its body: the Int, its range
    Interval, and its orientation key (None when E4 gives none)."""
    integral: Integral
    range: Interval
    orient: object


def _subterms(t):
    """t and every Term below it, pre-order."""
    yield t
    for _, k in children(t):
        if isinstance(k, Term):
            yield from _subterms(k)


def _sides(g):
    """The sides of an equation goal that moves act on: never ?A (§9)."""
    return (g.lhs,) if isinstance(g.rhs, MVar) else (g.lhs, g.rhs)


def _range(integral, pos_dom):
    """E4. The Interval for Integral[v = lo .. hi], plus the orientation
    proposition `lo <= hi` at pos_dom (with E5), or None.

    Literal ends (field.rational_value) are ordered into [min, max], using
    the original end terms, with no orientation. An infinite end is always
    open and on its own side, with no orientation. Equal infinities raise
    'range-same-infinity'. Otherwise the interval is [lo, hi], closed, with
    the orientation. pos_dom is the Int's own position domain.
    """
    v, lo, hi = integral.var, integral.lo, integral.hi
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
    return (Interval(v, lo, True, hi, True),
            with_domain(Rel("<=", lo, hi), pos_dom))


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
    term is checked by E4. rewrite (REWRITE_RULE steps 2, 6, 7, 9) and
    former charging (E6) both use it."""
    yield path, t, dom, anc
    inner_dom, inner_anc = dom, anc + ((t,) if isinstance(t, Deriv) else ())
    if isinstance(t, Integral):
        iv, orient = _range(t, dom)
        inner_dom, inner_anc = dom + (iv,), anc + (_IntScope(t, iv, orient),)
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
    status (ARCHITECTURE.md §5). A key already in the buffer only gains the
    source. Otherwise: a NonZero divisor whose expression ring-normalises
    to zero refuses 'divisor-normalises-to-zero' (E25); `divisor` is False
    only for tan's cos u # 0, a domain and not a divisor (E26), which E25
    does not test. If discharged_by is given, the obligation is DISCHARGED
    with that tag. If field.norm_num says True, it is DISCHARGED with
    ('norm_num', ()), and False refuses 'obligation-refuted' (E7); norm_num
    refuses 'Int-or-D-not-normalisable' a key holding an Int or D node in
    its proposition or its domain (E26 (b)). Otherwise, a Reg included, it
    is ADMITTED with ADMISSION_REASON and tagger.tag(key, gamma). gamma,
    TAG_RULES' Γ, is the goal's own domain when the key kept its domain,
    else ()."""
    if key in buf:
        buf[key] = replace(buf[key], sources=buf[key].sources | {source})
        return
    if divisor and isinstance(key, NonZero) and FD.ring_is_zero(key.e):
        raise Refused("divisor-normalises-to-zero",
                      f"the divisor {show(key.e)} is zero in ring (E25)")
    said = None if discharged_by or isinstance(key, Reg) else FD.norm_num(key)
    if said is False:
        raise Refused("obligation-refuted", f"norm_num: {show(key)} is false")
    if discharged_by or said:
        ob = Obligation(key, frozenset((source,)), DISCHARGED,
                        discharged_by or ("norm_num", ()))
    else:
        ob = Obligation(key, frozenset((source,)), ADMITTED,
                        tagger.tag(key, goal_dom if key.dom else ()),
                        ADMISSION_REASON)
    buf[key] = ob


def _emit_at(buf, prop, dom, anc, source, goal_dom, divisor=True):
    """prop at a position (E5), then E4's orientation of each enclosing Int
    whose range the key's domain now uses."""
    key = with_domain(prop, dom)
    _emit(buf, key, source, goal_dom, divisor=divisor)
    for a in anc:
        if isinstance(a, _IntScope) and a.orient is not None \
                and a.range in key.dom:
            _emit(buf, a.orient, "orient", goal_dom)


# E26 (a): each partial builtin's natural domain, the set on which §6.9
# makes it C^0, as the propositions its former owes, fn -> u -> props. One
# linear item per bound, written `u REL c` (the orientation of §6.3's d_ln
# and d_sqrt, GRAMMAR.md D12), so a two-sided domain is two keys and
# Fourier–Motzkin reads each bound directly (TAG_RULES range, linear). Not
# abs u <= 1: abs u is an opaque atom to every §5.3 method. Closed where the
# builtin is defined at the end (sqrt at 0, asin and acos at ±1, acosh at
# 1), open where it is not (ln at 0, atanh at ±1, tan where cos u = 0),
# which is also REWRITE_RULE 9(a)'s split into open and closed domains.
# sin, cos, atan, exp, abs, sinh, cosh, tanh and asinh are total: no row.
# A seam (ARCHITECTURE.md §7): _owed reads it by this global name at call
# time, and the definedness mutations swap the whole mapping in a child
# process. It is read-only, like deriv.APP_RULES, because a missing or wrong
# row is a false 'Proved.' whose admissions all hold.
NATURAL_DOMAINS = MappingProxyType({
    "ln": lambda u: (Rel(">", u, Num(0)),),
    "sqrt": lambda u: (Rel(">=", u, Num(0)),),
    "tan": lambda u: (NonZero(App("cos", u)),),
    "asin": lambda u: (Rel(">=", u, lit(-1)), Rel("<=", u, Num(1))),
    "acos": lambda u: (Rel(">=", u, lit(-1)), Rel("<=", u, Num(1))),
    "acosh": lambda u: (Rel(">=", u, Num(1)),),
    "atanh": lambda u: (Rel(">", u, lit(-1)), Rel("<", u, Num(1))),
})


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
    if isinstance(s, App) and s.fn in NATURAL_DOMAINS:
        return tuple((p, False) for p in NATURAL_DOMAINS[s.fn](s.arg))
    return ()


def _charge_formers(buf, term, dom, goal_dom, anc=()):
    """E6 and E26 (a) for one term entering the proof at a position with
    domain `dom` and enclosures `anc`: each former's _owed propositions, with
    source 'former'. Positions inside an Integral's body get its range (and
    its orientation, when a key uses that range). Each divisor goes through
    E25 in _emit, and each key through E7.

    A seam (ARCHITECTURE.md §7): rewrite is its only caller that passes
    `anc`, by keyword, and the mutations rewrite_R_former_at_goal_domain and
    rewrite_R_former_on_ranges_only replace it in a child process."""
    for _, s, d, a in _positions(term, dom, anc):
        for prop, divisor in _owed(s):
            _emit_at(buf, prop, d, a, "former", goal_dom, divisor)


def _check(check, lhs, rhs, minted, dom, goal_dom, buf, code):
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
    try:
        done = FD.ring(lhs, rhs) if check == "ring" else FD.field(lhs, rhs,
                                                                  facts)
    except FD.NotEqual as e:
        res = residual.residual_term(e.residual)
        raise Refused(code, f"{check} leaves lhs - rhs = {show(res)}",
                      res) from None
    for d in done.divisors:
        _emit(buf, with_domain(NonZero(d), dom), "field_div", goal_dom)
    for rec in minted:
        for v in rec.inst:
            _charge_formers(buf, v, dom, goal_dom)
        for h in rec.conclusion.dom:
            _emit(buf, with_domain(h, dom), "fact_hyp", goal_dom)


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


def _rewrite(state, args, minted, buf):
    """REWRITE_RULE steps 1–11, then check_goal on the new goal. That last
    check is a backstop: an inst value carrying an Int into a same-named
    Int's body lies in L's argument, which step 3's ring_nf refuses first
    (E26 (b)). The suite reaches it through the field.ring_equal seam
    (ARCHITECTURE.md §7, BACKSTOPS), so call it only as written here.
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
    for _, _, _, a in found:  # step 9, for each D[x] above the occurrence
        for i, dx in enumerate(a):
            if isinstance(dx, _IntScope):
                continue
            x = dx.var
            through = [y.integral for y in a[i + 1:]
                       if isinstance(y, _IntScope)]
            if (any(x in fv(h) and not _open_in(h, x) for h in bounds) or bounds
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
    deriv's trace and output).

    Everything that can refuse runs in the order ARCHITECTURE.md §4 gives:
    the orientation, F's formers, deriv, the check, the new goal's formers,
    then check_goal on the new goal. That last check is the only guard
    against a variable free in F that the goal's rhs binds
    (D11-bound-and-free). An Int inside F, whose binder could be free in
    the rhs, is refused earlier by deriv (E26 (b)).
    The emissions are buffered in §6.4's premise order, so the tracker lists
    the four premises together."""
    g = state.goal[0]
    G, it, F, check = g.dom, g.lhs, args["F"], args["check"]
    if not isinstance(it, Integral):
        raise Refused("ftc-no-integral", "ftc needs an Int as the goal's lhs")
    if any(isinstance(e, (PosInf, NegInf)) for e in (it.lo, it.hi)):
        raise Refused("ftc-infinite-endpoint", "F(oo) is not a term (§5.1); "
                      "an infinite range needs int_improper")
    x, f = it.var, it.body
    closed, orient = _range(it, G)
    on_ab = G + (closed,)  # [a, b]
    on_open = G + (Interval(x, closed.lo, False, closed.hi, False),)  # C¹'s
    on_deriv = G + (derivative_domain(closed),)  # (a, b), through the seam
    if orient is not None:
        _emit(buf, orient, "orient", G)
    _charge_formers(buf, F, on_ab, G)
    later = {}
    d = DV.deriv(F, x, on_deriv)
    for key, source in d.emissions:
        _emit(later, key, source, G)
    _check(check, d.output, f, minted, on_deriv, G, later, "ftc-check-failed")
    cites = tuple(dict.fromkeys(rec.entry for rec in minted))
    _emit(buf, with_domain(Reg(F, 0), on_ab), "ftc_F_C0", G)
    _emit(buf, with_domain(Reg(F, 1), on_open), "ftc_F_C1", G)
    _emit(buf, with_domain(Rel("==", Deriv(x, F), f), on_deriv), "ftc_D", G,
          ("deriv+" + check, cites))
    _emit(buf, with_domain(Reg(f, 0), on_ab), "ftc_f_C0", G)
    for ob in later.values():
        buf[ob.key] = _merged(buf.get(ob.key), ob)
    lhs = Add(subst(F, {x: it.hi}), Neg(subst(F, {x: it.lo})))  # F(b) - F(a)
    goal = (replace(g, lhs=lhs),)
    for side in _sides(goal[0]):
        _charge_formers(buf, side, G, G)
    check_goal(goal)
    return goal, None, {"trace": d.trace, "output": d.output}


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
    if any(isinstance(k, (PosInf, NegInf)) for s in _subterms(v)
           for _, k in children(s)):
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


_MOVE = {"rewrite": _rewrite, "fact": _fact, "ftc": _ftc, "close": _close}
