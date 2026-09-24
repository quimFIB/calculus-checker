"""Terms, judgements and goals (DESIGN.md §5.1–§5.3, §9; kernel/GRAMMAR.md).

Trusted (§15.2 items 1 and 8): the term representation, syntactic equality,
free and bound variables, substitution, the goal checks, the parser and the
plain-text printer. GRAMMAR.md is the specification. Its section and
decision numbers (§7, D17, ...) are used below unless marked DESIGN.

Nodes are frozen dataclasses, so `==` is plain tree identity with bound names
compared literally (GRAMMAR.md §7) and every node is hashable, which is what
obligation keys rely on (p1_expected E8). They are slotted too, so a node has
no `__dict__`: `vars(node)` raises, and only a deliberate `object.__setattr__`
can change one. Four invariants are enforced where a node is built. A `Num`
holds a natural-number int, a negative literal being Neg(Num). A `Pow`
exponent is an int (so no float reaches norm_num). An `RPow` never has a
literal integer exponent (D17). An `Interval`'s infinite ends are open and
on their own side (D18). A node built round its constructor, with
`object.__new__`, skips them, so check_goal runs each constructor's check
again on every node it is given.

Every refusal raises `Refused` with a stable code: GRAMMAR.md §1's table,
`rpow-literal-exponent`, `subst-under-D`, or `close-no-mvar` from
instantiate. The three parse functions raise its subclass `ParseError`, which
also carries the offending character offset.
"""

import itertools
import re
from dataclasses import dataclass, fields, replace
from fractions import Fraction

BUILTINS = frozenset((
    "sin", "cos", "tan", "asin", "acos", "atan", "exp", "ln", "sqrt", "abs",
    "sinh", "cosh", "tanh", "asinh", "acosh", "atanh"))
CONSTANTS = frozenset(("pi", "e_const"))
RELS = ("==", "<=", "<", ">=", ">")


class Refused(Exception):
    """A kernel refusal. `code` is the stable thing tests assert, `message`
    is for people, and `residual` is a Term, set only by a failed check."""

    def __init__(self, code, message, residual=None):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message
        self.residual = residual


class ParseError(Refused):
    """A refusal by parse_term, parse_judgement or parse_goal (GRAMMAR.md §1,
    D16). `offset` is the character index of the offending token, or None
    for a refusal of `sig` itself."""

    def __init__(self, code, message, offset):
        super().__init__(code, message)
        self.offset = offset


# ---------------------------------------------------------------- nodes

class Term:
    """Base of every term node, for isinstance checks only."""
    __slots__ = ()


class Judgement:
    """Base of Rel, NonZero and Reg."""
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Num(Term):
    n: int  # n >= 0; a negative literal is Neg(Num), p/q is Div(Num, Num)

    def __post_init__(self):
        if type(self.n) is not int or self.n < 0:
            raise ValueError(f"Num holds a natural number, not {self.n!r}")


@dataclass(frozen=True, slots=True)
class Const(Term):
    name: str  # "pi" or "e_const"


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str


@dataclass(frozen=True, slots=True)
class MVar(Term):
    name: str  # "A" for ?A; in goals only, the whole rhs of one == (D15)


@dataclass(frozen=True, slots=True)
class Neg(Term):
    a: Term


@dataclass(frozen=True, slots=True)
class Add(Term):
    a: Term
    b: Term


@dataclass(frozen=True, slots=True)
class Mul(Term):
    a: Term
    b: Term


@dataclass(frozen=True, slots=True)
class Div(Term):
    a: Term
    b: Term


@dataclass(frozen=True, slots=True)
class Pow(Term):
    base: Term
    n: int  # any int; n < 0 is a field operation owing base # 0

    def __post_init__(self):
        if type(self.n) is not int:  # not float, Fraction or bool
            raise ValueError(f"Pow takes an int exponent, not {self.n!r}")


@dataclass(frozen=True, slots=True)
class RPow(Term):
    base: Term  # owes base > 0
    exp: Term

    def __post_init__(self):
        e = self.exp
        if isinstance(e, Num) or (isinstance(e, Neg) and isinstance(e.a, Num)):
            raise Refused("rpow-literal-exponent",
                          "a real power with a literal integer exponent is "
                          "Pow, and converting would drop base > 0 (D17)")


@dataclass(frozen=True, slots=True)
class App(Term):
    fn: str  # one of BUILTINS
    arg: Term


@dataclass(frozen=True, slots=True)
class Call(Term):
    fn: str  # a declared symbol
    args: tuple


@dataclass(frozen=True, slots=True)
class Deriv(Term):
    var: str  # D10: binds var inside body, and var is free in the whole term
    body: Term


@dataclass(frozen=True, slots=True)
class PosInf:
    """`oo`: an endpoint only, never a term (DESIGN §5.1 class b)."""


@dataclass(frozen=True, slots=True)
class NegInf:
    """`-oo`."""


POS_INF = PosInf()
NEG_INF = NegInf()


@dataclass(frozen=True, slots=True)
class Integral(Term):
    var: str
    lo: object  # Term, POS_INF or NEG_INF
    hi: object
    body: Term


@dataclass(frozen=True, slots=True)
class Interval:
    """A domain item on `var`. An infinite end is open, with -oo only as the
    lower end and oo only as the upper (D18)."""
    var: str
    lo: object  # Term or NEG_INF
    lo_closed: bool
    hi: object  # Term or POS_INF
    hi_closed: bool

    def __post_init__(self):
        bad = (isinstance(self.lo, PosInf) or isinstance(self.hi, NegInf)
               or (isinstance(self.lo, NegInf) and self.lo_closed)
               or (isinstance(self.hi, PosInf) and self.hi_closed))
        if bad:
            raise Refused("oo-misplaced",
                          "an infinite end must be open and on its own side")


@dataclass(frozen=True, slots=True)
class Rel(Judgement):
    op: str  # one of RELS, kept as written (D12)
    lhs: Term
    rhs: Term
    dom: tuple = ()  # items: Interval, or Rel/NonZero with dom == ()


@dataclass(frozen=True, slots=True)
class NonZero(Judgement):
    e: Term
    dom: tuple = ()


@dataclass(frozen=True, slots=True)
class Reg(Judgement):
    e: Term
    k: object  # int >= 0 or "omega"
    dom: tuple = ()  # the domain inside C^k(...); E5 never applies to it


# A Goal is a plain tuple of judgements (DESIGN §5.2).


# ---------------------------------------------------------------- helpers

def lit(q):
    """The term for the rational q, in exactly GRAMMAR.md §7's shapes: Num n,
    Neg(Num n), Div(Num p, Num q), Neg(Div(Num p, Num q)), in lowest terms
    with q > 1. Accepts int or Fraction."""
    if isinstance(q, bool) or not isinstance(q, (int, Fraction)):
        raise TypeError(f"lit takes an int or a Fraction, not {q!r}")
    q = Fraction(q)
    p = abs(q.numerator)
    t = Num(p) if q.denominator == 1 else Div(Num(p), Num(q.denominator))
    return Neg(t) if q < 0 else t


# The fields of each node that hold children. A tuple field (Call.args, a
# domain) holds several. Names, Pow.n, Reg.k and interval flags are not
# children. Leaves, infinities and anything else have none.
_CHILDREN = {Neg: ("a",), Add: ("a", "b"), Mul: ("a", "b"), Div: ("a", "b"),
             Pow: ("base",), RPow: ("base", "exp"), App: ("arg",),
             Call: ("args",), Deriv: ("body",), Integral: ("lo", "hi", "body"),
             Interval: ("lo", "hi"), Rel: ("lhs", "rhs", "dom"),
             NonZero: ("e", "dom"), Reg: ("e", "dom")}
_TERMS = frozenset((Num, Const, Var, MVar)) | {c for c in _CHILDREN
                                                if issubclass(c, Term)}


def _fields(x):
    return tuple((n, getattr(x, n)) for n in _CHILDREN.get(type(x), ()))


def children(t):
    """(path step, child) pairs of a Term, in GRAMMAR.md §7's field order:
    Call's args by index, every other node by field name. An infinite Int
    limit is a child here, and not a Term. A hand-built Call whose args are
    not a tuple has no children here, and check_goal refuses it 'syntax'.
    The kernel's position walk uses this, so one table says what a node's
    children are."""
    if isinstance(t, Call):  # args that are not a tuple: check_goal refuses
        return tuple(enumerate(t.args)) if type(t.args) is tuple else ()
    return _fields(t)


def trees(x):
    """Every Integral and Deriv node in x, pre-order: a Term, a judgement
    (its sides and domain items), an Interval or a tuple of them.
    p1_expected E26 (b): neither node has a definedness condition the
    kernel can state, so field's normaliser and norm_num refuse a side
    holding one, and deriv refuses to read one as a constant (E12)."""
    if isinstance(x, (Integral, Deriv)):
        yield x
    for k in _kids(x):
        yield from trees(k)


def _kids(x):
    """The children of a node, tuple fields flattened; a goal's judgements."""
    if isinstance(x, tuple):
        return x
    return tuple(k for _, v in _fields(x)
                 for k in (v if isinstance(v, tuple) else (v,)))


def _map(f, x):
    """x rebuilt through its constructor, so every invariant is re-checked,
    with f applied to each child. A tuple is mapped elementwise."""
    if isinstance(x, tuple):
        return tuple(map(f, x))
    new = {n: _map(f, v) if isinstance(v, tuple) else f(v)
           for n, v in _fields(x)}
    return replace(x, **new) if new else x


def _finite(*ends):
    """The ends that are not exactly oo or -oo. A subclass instance is kept,
    so check_goal refuses it as a term."""
    return [e for e in ends if type(e) not in (PosInf, NegInf)]


def fv(x):
    """Free variables, as a frozenset of names, of a Term, an Interval, a
    Judgement or a Goal.

    GRAMMAR.md §5 gives the rules. fv(Int[v = a .. b] e) is
    (fv(e) - {v}) ∪ fv(a) ∪ fv(b), and fv(D[x] e) is fv(e) ∪ {x} (D10).
    Constants, ?A and infinities contribute nothing. For a judgement it is
    fv of its sides and of its domain items, where an Interval contributes
    its variable and its endpoints. `with_domain` does not use this: E5 asks
    only whether the proposition's sides are closed.
    """
    if isinstance(x, Var):
        return frozenset((x.name,))
    if isinstance(x, Integral):
        return (fv(x.body) - {x.var}) | fv(x.lo) | fv(x.hi)
    out = frozenset().union(*map(fv, _kids(x)))
    return out | {x.var} if isinstance(x, (Deriv, Interval)) else out


def bv(x):
    """Bound variables: the names bound by an Integral anywhere in x
    (GRAMMAR.md §5). A Deriv's variable is never in bv."""
    out = frozenset().union(*map(bv, _kids(x)))
    return out | {x.var} if isinstance(x, Integral) else out


def subst(x, mapping):
    """x with each free Var named in `mapping` replaced by its Term.

    x may be a Term, a Judgement (its sides and domain items) or an
    Interval (its endpoints; its var names the constrained variable and is
    left alone).
    Every node is rebuilt through its constructor, so a substitution that
    would make an RPow exponent literal raises Refused
    'rpow-literal-exponent' (D17).

    Under Integral[v = a .. b] e, a and b are substituted, and e is too,
    unless v is itself mapped. If v is free in a replacement, v is renamed
    to the first of v_1, v_2, ... that is free nowhere in play, so the
    substitution is capture-avoiding. P1 never reaches that case.

    Under Deriv[y] e, GRAMMAR.md §5's three cases apply. The term is
    unchanged if it has no mapped name free. It becomes D[y](e[...]) if y is
    not mapped and y is free in no replacement. Anything else raises
    Refused 'subst-under-D'. Deriv is never renamed.
    """
    # Iterative over every node that binds nothing, children before parents,
    # so a term of any depth is substituted without exhausting the stack;
    # each binder is _subst_binder's, which recurses only into binders.
    todo, done = [(x, False)], []
    while todo:
        node, ready = todo.pop()
        if isinstance(node, Var):
            done.append(mapping.get(node.name, node))
            continue
        if isinstance(node, (Deriv, Integral)):
            done.append(_subst_binder(node, mapping))
            continue
        fields = (tuple(enumerate(node)) if isinstance(node, tuple)
                  else _fields(node))
        if not ready:
            todo.append((node, True))
            kids = [k for _, v in fields
                    for k in (v if isinstance(v, tuple) else (v,))]
            todo.extend((k, False) for k in reversed(kids))
            continue
        count = sum(len(v) if isinstance(v, tuple) else 1 for _, v in fields)
        rebuilt = done[len(done) - count:] if count else []
        del done[len(done) - count:]
        new, i = {}, 0
        for n, v in fields:  # _map's rebuild: a tuple field elementwise
            width = len(v) if isinstance(v, tuple) else 1
            new[n] = tuple(rebuilt[i:i + width]) if isinstance(v, tuple) else rebuilt[i]
            i += width
        if isinstance(node, tuple):
            done.append(tuple(new[n] for n, _ in fields))
        else:
            done.append(replace(node, **new) if new else node)
    return done[0]


def _subst_binder(x, mapping):
    """subst at a Deriv or Integral node (GRAMMAR.md §5's rules below)."""
    # A binder. Only the mapped names free in x matter, so only their
    # replacements can be captured.
    live = {k: t for k, t in mapping.items() if k in fv(x)}
    if not live:
        return x
    reps = frozenset().union(*map(fv, live.values()))
    if isinstance(x, Deriv):
        if x.var in live or x.var in reps:
            raise Refused("subst-under-D", f"substituting into D[{x.var}] "
                          f"would change what is differentiated (GRAMMAR §5)")
        return Deriv(x.var, subst(x.body, live))
    v, body = x.var, x.body
    if v in reps:  # rename the binder before going under it
        taken = fv(x) | fv(body) | bv(body) | reps | set(mapping)
        v = next(f"{x.var}_{i}" for i in itertools.count(1)
                 if f"{x.var}_{i}" not in taken)
        body = subst(body, {x.var: Var(v)})
    inner = {k: t for k, t in live.items() if k != x.var}
    return Integral(v, subst(x.lo, live), subst(x.hi, live),
                    subst(body, inner))


def instantiate(goal, value):
    """The goal with its one MVar replaced by `value`: the theorem `close`
    reports (DESIGN §9). A tree edit, not `subst`: ?A is not a variable."""
    hit = [isinstance(j, Rel) and isinstance(j.rhs, MVar) for j in goal]
    if sum(hit) != 1:
        raise Refused("close-no-mvar", "the goal has no single ?A to replace")
    return tuple(replace(j, rhs=value) if h else j for j, h in zip(goal, hit))


def with_domain(prop, dom):
    """`prop` (a Rel or NonZero with dom == (), or a Reg) placed on `dom`.

    E5: a Rel or NonZero whose sides have no free variable gets dom (),
    whatever `dom` is. A Reg gets `dom` as its C^k domain unchanged. This is
    the only way the kernel and deriv build an obligation key.
    """
    if isinstance(prop, Reg):
        return replace(prop, dom=tuple(dom))
    if not isinstance(prop, (Rel, NonZero)) or prop.dom != ():
        raise ValueError(f"not a proposition without a domain: {prop!r}")
    return replace(prop, dom=tuple(dom) if fv(prop) else ())


def check_goal(goal):
    """Raise Refused unless `goal` is a well-formed goal tree, whatever built it.

    The checks: every item is a Judgement; ?A appears only as the whole
    right side of an ==, at most once (mvar-misplaced, D15); no Integral's
    variable is free in its own endpoints (bound-in-endpoint); no Integral
    rebinds an enclosing Integral's name (shadowing); bv ∩ fv = ∅ (D11,
    D11-bound-and-free); and `oo` appears only as an Integral limit
    (oo-misplaced).

    It also checks what the parser alone would guarantee, since a caller may
    build a goal tree by hand (GRAMMAR.md §7's invariants): judgements,
    intervals and domains of their exact types, with a domain a tuple; every
    Var, Int and D name an exact str that §3 classifies as a variable; a
    Const is pi or e_const; an App's function a builtin; a Call's a name §3
    does not reserve, with a tuple of arguments; within the goal, a called
    name has one arity and is never a variable (check_names). Every node's
    constructor check (Num, Pow, RPow, Interval) is run again, since a node
    built with object.__new__ skipped it, and such a node with a slot left
    unset is refused before the slot is read. Infinities are matched by
    exact type, like every other leaf. Without these, show() could print
    a tree as text that parses to another statement, or as another number,
    and a str subclass could make two variables one ring atom. parse_goal
    calls this, and so do kernel.install and the kernel's argument checks.
    """
    if type(goal) is not tuple:
        raise Refused("syntax", "a goal is a tuple of judgements")
    for j in goal:
        _check_judgement(j, top=True)
    if sum(isinstance(j, Rel) and isinstance(j.rhs, MVar) for j in goal) > 1:
        raise Refused("mvar-misplaced", "at most one ?A per goal (D15)")
    clash = bv(goal) & fv(goal)
    if clash:
        raise Refused("D11-bound-and-free", f"{', '.join(sorted(clash))} is "
                      f"both bound and free in the goal (D11)")
    check_names(goal)


def _calls(x):
    """(fn, arity) of every Call in x, domains included."""
    out = {(x.fn, len(x.args))} if isinstance(x, Call) else set()
    for k in _kids(x):
        out |= _calls(k)
    return out


def check_names(*xs):
    """GRAMMAR.md §7's Call invariant without a sig: across xs, one
    statement, a called name has one arity and is never a variable, free,
    Int-bound, D-bound or an Interval's. Otherwise show() prints text that
    parses under no sig, and the kernel reads x(y) as an atom independent of
    a bound x. The kernel also calls it on a goal with a move's terms."""
    calls = set().union(*map(_calls, xs))
    names = {f for f, _ in calls}
    if len(calls) > len(names):
        raise Refused("D5-arity", "a symbol is called with two arities")
    both = names & frozenset().union(*(fv(x) | bv(x) for x in xs))
    if both:
        raise Refused("D5-uncalled", f"{', '.join(sorted(both))} is both "
                      "called and a variable")


def _is_variable(name):
    """An exact str that §3 classifies as a variable. A str subclass could
    compare equal to another name and merge two ring atoms."""
    return (type(name) is str and _VARIABLE.fullmatch(name) is not None
            and name not in _CLASS and name not in _REFUSED)


def _built(x):
    """x's constructor check, run again: a node built with object.__new__
    holds whatever was put in it, such as a Num of an int subclass whose
    str() lies, or of -3, which prints as Neg(Num 3). A slot left unset is
    malformed too: reading it would raise AttributeError, not refuse."""
    if not all(hasattr(x, f.name) for f in fields(x)):
        return False
    post = getattr(type(x), "__post_init__", None)
    if post is not None:
        try:
            post(x)
        except (ValueError, Refused):
            return False
    return True


def _shown(x):
    """repr(x) for a refusal message, or its class name when x cannot be
    shown: a node with a slot left unset, or a subclass whose repr raises."""
    try:
        return repr(x)
    except Exception:  # noqa: BLE001 -- a refusal must not become a crash
        return f"a malformed {type(x).__name__}"


def _leaves_ok(t):
    """GRAMMAR.md §7's leaf invariants for one node, and its constructor's,
    so show(t) is t's own text. A hand-built tree may hold a list, float or
    look-alike str where the parser only ever puts a tuple, an int or a
    name."""
    if not _built(t):
        return False
    if isinstance(t, (Var, Deriv, Integral)):
        return _is_variable(t.name if isinstance(t, Var) else t.var)
    if isinstance(t, (Const, MVar)):
        return type(t.name) is str and (t.name in CONSTANTS if isinstance(
            t, Const) else _NAME.fullmatch(t.name) is not None)
    if isinstance(t, App):
        return type(t.fn) is str and t.fn in BUILTINS
    if isinstance(t, Call):  # install has no sig: its shape only
        return (type(t.fn) is str and _NAME.fullmatch(t.fn) is not None
                and t.fn not in RESERVED and type(t.args) is tuple
                and len(t.args) >= 1)
    return True


def _check_judgement(j, top):
    """A domain item is checked with top=False: an order or # constraint,
    with no domain of its own, and never ?A."""
    fine = type(j) in (NonZero, Rel, Reg) and _built(j) and (
        type(j) is NonZero
        or type(j) is Rel and type(j.op) is str
        and j.op in (RELS if top else RELS[1:])
        or top and type(j) is Reg and (
            type(j.k) is str and j.k == "omega"
            or type(j.k) is int and j.k >= 0))
    if not fine or type(j.dom) is not tuple or not top and j.dom != ():
        raise Refused("syntax", f"not a judgement here: {_shown(j)}")
    sides = (j.lhs, j.rhs) if isinstance(j, Rel) else (j.e,)
    if top and isinstance(j, Rel) and j.op == "==" and isinstance(j.rhs, MVar):
        if type(j.rhs) is not MVar or not _leaves_ok(j.rhs):
            raise Refused("syntax", f"not a metavariable: {_shown(j.rhs)}")
        sides = sides[:1]
    for t in sides:
        _check_term(t, ())
    for it in j.dom:
        if type(it) is Interval:
            if not (_built(it) and _is_variable(it.var)
                    and type(it.lo_closed) is bool
                    and type(it.hi_closed) is bool):
                raise Refused("syntax", f"not an interval: {_shown(it)}")
            for e in _finite(it.lo, it.hi):
                _check_term(e, ())
        else:
            _check_judgement(it, top=False)


def _check_term(t, enclosing):
    """`enclosing` names the Integrals whose body holds t."""
    if isinstance(t, MVar):
        raise Refused("mvar-misplaced", "?A is only the whole right side of "
                      "an == (D15)")
    if type(t) in (PosInf, NegInf):
        raise Refused("oo-misplaced", "oo is only an Int limit (GRAMMAR §5)")
    if type(t) not in _TERMS or not _leaves_ok(t):
        raise Refused("syntax", f"not a term: {_shown(t)}")
    if not isinstance(t, Integral):
        for k in _kids(t):
            _check_term(k, enclosing)
        return
    if t.var in enclosing:
        raise Refused("shadowing", f"Int rebinds {t.var} (GRAMMAR §5)")
    if t.var in fv(t.lo) | fv(t.hi):
        raise Refused("bound-in-endpoint", f"{t.var} is in its own limits")
    for e in _finite(t.lo, t.hi):
        _check_term(e, enclosing)
    _check_term(t.body, enclosing + (t.var,))


# ---------------------------------------------------------------- lexer
#
# A token is (kind, value, offset): "nat" (an int), "id" (a str, classified
# by the parser per §3), "mvar" (the name after ?), "regk" (the k of C⁰ or
# Cω), "op" (its text) or "end". [0-9], never \d: \d matches non-ASCII digits.

_TOKEN = re.compile(r"""
    (?P<ws>[ \t\n]+) | (?P<decimal>[0-9]+\.[0-9]) | (?P<juxt>[0-9]+[A-Za-z])
  | (?P<nat>[0-9]+) | (?P<regk>C(?:[⁰¹²³⁴-⁹]+|ω))
  | (?P<id>[A-Za-z][A-Za-z0-9_]*)
  | (?P<mvar>\?[A-Za-z][A-Za-z0-9_]*) | (?P<syn>[≐≤≥∈∧⊤])
  | (?P<op>\.\.|==|<=|>=|/\\|->|[-+*/^()\[\],=<>\#@])""", re.X)
_SYNONYMS = {"≐": ("op", "=="), "≤": ("op", "<="), "≥": ("op", ">="),
             "∈": ("id", "in"), "∧": ("op", "/\\"), "⊤": ("id", "true")}
_ASCII_HINTS = {"−": "-", "·": "*", "π": "pi", "√": "sqrt", "∞": "oo",
                "≠": "a - b # 0"}
_SUPERSCRIPTS = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")


def _lex(s):
    toks, i = [], 0
    while i < len(s):
        m = _TOKEN.match(s, i)
        if m is None and s[i].isascii():
            raise ParseError("syntax", f"unexpected character {s[i]!r}", i)
        if m is None:
            hint = _ASCII_HINTS.get(s[i])
            raise ParseError("non-ascii", f"{s[i]!r} is not ASCII" + (
                f": write {hint}" if hint else ""), i)
        kind, text = m.lastgroup, m.group()
        if kind == "decimal":
            raise ParseError("D1-decimal", "no decimals: write 1/2 (D1)", i)
        if kind == "juxt":
            raise ParseError("implicit-mul", "write 2*x, not 2x (§2)",
                             m.end() - 1)
        if kind == "nat":
            toks.append(("nat", int(text), i))
        elif kind == "regk":
            k = text[1:]
            toks.append(("regk", "omega" if k == "ω" else
                         int(k.translate(_SUPERSCRIPTS)), i))
        elif kind == "mvar":
            toks.append(("mvar", text[1:], i))
        elif kind == "syn":
            toks.append(_SYNONYMS[text] + (i,))
        elif kind != "ws":
            toks.append((kind, text, i))
        i = m.end()
    return toks + [("end", None, len(s))]


# ---------------------------------------------------------------- names (§3)

KEYWORDS = frozenset(("D", "Int", "in", "oo", "true"))
_CLASS = {**dict.fromkeys(CONSTANTS, "const"),
          **dict.fromkeys(BUILTINS, "builtin"),
          **dict.fromkeys(KEYWORDS, "kw")}
_HINTS = {"log": "ln", "sec": "1/cos u", "csc": "1/sin u",
          "cot": "cos u/sin u", "sech": "1/cosh u", "arcsin": "asin",
          "arccos": "acos", "arctan": "atan", "arsinh": "asinh",
          "arcosh": "acosh", "artanh": "atanh", "inf": "oo", "infinity": "oo"}
_REFUSED = {
    **{w: ("D2-deferred", f"{w} is not supported in this kernel yet (D2)")
       for w in ("Sum", "lim", "conv", "absconv", "diverges", "exists",
                 "dim")},
    **{w: ("reserved-hint", f"{w} is not a name here: write {h}")
       for w, h in _HINTS.items()},
    "e": ("D3-bare-e", "write exp(u) for e^u, e_const for the number e (D3)")}
# A sig entry may not be any name §3 classifies before declared functions,
# nor C or omega, which are keywords after `in` (D5).
RESERVED = frozenset(_CLASS) | frozenset(_REFUSED) | {"C", "omega"}
_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_]*")  # an IDENT (§3)
_VARIABLE = re.compile(r"(?:[A-Za-z]|%s)[0-9]*(?:_[A-Za-z0-9]+)*" % "|".join(
    "alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi "
    "omicron rho sigma tau upsilon phi chi psi omega".split()))


def _check_sig(sig):
    sig = dict(sig or {})
    for f, n in sig.items():
        if type(f) is not str or not _NAME.fullmatch(f):
            raise ParseError("syntax", f"sig: {f!r} is not a name", None)
        if f in RESERVED:
            raise ParseError("D5-sig-collision", f"sig: {f} is reserved", None)
        if type(n) is not int or n < 1:
            raise ParseError("D5-sig-arity0", f"sig: {f} needs arity >= 1; "
                             f"declare a constant as a variable", None)
    return sig


def _is(tok, *vals):
    return tok[0] in ("op", "id") and tok[1] in vals


# ---------------------------------------------------------------- parser

class _Parser:
    """Recursive descent, one method per GRAMMAR.md §4 rule. `goal` allows
    ?A as the whole right side of an == (D15). `binders` holds the names of
    the enclosing Ints, for the shadowing check; `bound` every Int's variable
    token, for D11; `mvar` whether a ?A was already taken, for D15."""

    def __init__(self, s, sig, goal):
        self.toks, self.i, self.sig, self.goal = _lex(s), 0, sig, goal
        self.binders, self.bound, self.mvar = [], [], False

    def peek(self, k=0):
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def take(self):
        tok = self.peek()
        self.i = min(self.i + 1, len(self.toks) - 1)
        return tok

    def at(self, *vals):
        return _is(self.peek(), *vals)

    def fail(self, code, message, tok=None):
        raise ParseError(code, message, (tok or self.peek())[2])

    def syntax(self, what):
        got = self.peek()[1]
        self.fail("syntax", f"expected {what}, got "
                  f"{'end of input' if got is None else repr(got)}")

    def expect(self, *vals):
        if not self.at(*vals):
            self.syntax(" or ".join(vals))
        return self.take()

    def kind(self):
        """The §3 class of the IDENT at the cursor, which is not taken:
        const, builtin, kw, declared or var. Every other class refuses."""
        w = self.peek()[1]
        if w in _CLASS:
            return _CLASS[w]
        if w in _REFUSED:
            self.fail(*_REFUSED[w])
        if w in self.sig:
            return "declared"
        if _is(self.peek(1), "("):
            self.fail("D5-undeclared", f"{w} is not a declared function "
                      f"symbol; write {w}*(...) (D5)")
        if not _VARIABLE.fullmatch(w):
            self.fail("D4-not-a-name", f"{w} is not a name: write sin x, or "
                      f"x*y (D4)")
        return "var"

    def is_kind(self, *kinds):
        return self.peek()[0] == "id" and self.kind() in kinds

    def var(self):
        if not self.is_kind("var"):
            self.syntax("a variable")
        return self.take()

    # terms

    def expr(self):
        return self.binder() if self.at("Int") else self.sum()

    def binder(self):
        self.take()
        self.expect("[")
        v = self.var()
        self.expect("=")
        lo = self.endpoint()
        self.expect("..")
        hi = self.endpoint()
        self.expect("]")
        if v[1] in fv(lo) | fv(hi):
            self.fail("bound-in-endpoint", f"{v[1]} is in its own limits", v)
        if v[1] in self.binders:
            self.fail("shadowing", f"Int rebinds {v[1]}; rename it", v)
        self.binders.append(v[1])
        self.bound.append(v)
        body = self.expr()
        self.binders.pop()
        return Integral(v[1], lo, hi, body)

    def endpoint(self):
        """oo, -oo or a sum. An oo that does not end the endpoint is left
        to atom, which refuses it."""
        ends = ("..", "]", ",", ")")
        if self.at("oo") and _is(self.peek(1), *ends):
            self.take()
            return POS_INF
        if (self.at("-") and _is(self.peek(1), "oo")
                and _is(self.peek(2), *ends)):
            self.take()
            self.take()
            return NEG_INF
        return self.sum()

    def sum(self):
        t = self.product()
        while self.at("+", "-"):
            op = self.take()[1]
            r = self.product()
            t = Add(t, r if op == "+" else Neg(r))
        return t

    def product(self):
        t = self.unary()
        while self.at("*", "/"):
            op = self.take()[1]
            t = (Mul if op == "*" else Div)(t, self.unary())
        return t

    def unary(self):
        if self.at("-"):
            self.take()
            return Neg(self.unary())
        t = self.power()
        tok = self.peek()  # D9: nothing that starts an atom may follow
        if tok[0] in ("nat", "mvar", "id") and tok[1] != "in" or _is(tok, "("):
            self.fail("implicit-mul", "no implicit multiplication: write a*b")
        return t

    def power(self):
        if not (self.at("D") or self.is_kind("builtin")):
            base = self.atom()
            return self.raise_to(base) if self.at("^") else base
        t = self.app()
        if self.at("^"):
            self.fail("D6-app-as-base", "an application is not a power base: "
                      "write (sin x)^2 (D6)")
        return t

    def app(self):
        tok = self.take()
        if tok[1] != "D":
            return App(tok[1], self.operand())
        self.expect("[")
        v = self.var()[1]
        self.expect("]")
        return Deriv(v, self.operand())

    def operand(self):
        """D6: an app, a literal or name with an optional ^, a group, or a
        call. A group then ^ is ambiguous. A call takes no ^ here, so power
        refuses one."""
        if self.at("-"):
            self.fail("D6-neg-operand", "write sin(-x), not sin -x (D6)")
        if self.at("D") or self.is_kind("builtin"):
            return self.app()
        if self.is_kind("declared"):
            return self.call()
        grouped = self.at("(")
        t = self.atom()
        if self.at("^") and grouped:
            self.fail("D6-ambiguous-app-power", "ambiguous: write sin(x^2) "
                      "or (sin x)^2 (D6)")
        return self.raise_to(t) if self.at("^") else t

    def raise_to(self, base):
        """`^` and its exponent (D8). The node follows from what the exponent
        parses to."""
        self.take()
        if self.at("-"):
            self.fail("D8-neg-exponent", "write x^(-1), not x^-1 (D8)")
        if self.at("D") or self.is_kind("builtin", "declared"):
            self.syntax("an exponent: a number, a name or (...)")
        e = self.atom()
        if self.at("^"):
            self.fail("D8-pow-chain", "write (x^2)^3 or x^(2^3) (D8)")
        if isinstance(e, Num):
            return Pow(base, e.n)
        if isinstance(e, Neg) and isinstance(e.a, Num):
            return Pow(base, -e.a.n)
        return RPow(base, e)

    def atom(self):
        tok = self.peek()
        if tok[0] == "nat":
            return Num(self.take()[1])
        if tok[0] == "mvar":
            self.fail("mvar-misplaced", "?A is only the whole right side of "
                      "an == in a goal (D15)")
        if _is(tok, "("):
            self.take()
            t = self.expr()
            self.expect(")")
            return t
        k = self.kind() if tok[0] == "id" else None
        if k in ("const", "var"):
            return (Const if k == "const" else Var)(self.take()[1])
        if k == "declared":
            return self.call()
        if _is(tok, "Int"):
            self.fail("D7-int-in-arith", "write 2*(Int[...] f) (D7)")
        if _is(tok, "oo"):
            self.fail("oo-misplaced", "oo is only an Int limit or an open "
                      "interval end (§5)")
        self.syntax("a term")

    def call(self):
        f = self.take()
        if not self.at("("):
            self.fail("D5-uncalled", f"apply the declared {f[1]}(...) (D5)", f)
        self.take()
        args = [self.expr()]
        while self.at(","):
            self.take()
            args.append(self.expr())
        self.expect(")")
        if len(args) != self.sig[f[1]]:
            self.fail("D5-arity", f"{f[1]} takes {self.sig[f[1]]} arguments "
                      f"(D5)", f)
        return Call(f[1], tuple(args))

    # judgements and domains

    def judgement(self):
        lhs = self.expr()
        if self.at("in"):
            self.take()
            k = self.regclass()
            self.expect("(")
            items = self.domain()
            self.expect(")")
            return Reg(lhs, k, self.resolve((lhs,), items))
        j = self.relation(lhs, top=True)
        items = []
        if self.at("@"):
            self.take()
            items = self.domain()
        return replace(j, dom=self.resolve(_kids(j), items))

    def relation(self, lhs, top):
        """`lhs op rhs` or `lhs # 0`, after lhs, with no domain. A domain
        item (top False) takes no == and sums for sides. A goal's == may
        take ?A as its whole right side (D15)."""
        if self.at("#"):
            tok = self.take()
            start = self.i  # "0" is the one NAT token 0, not (0) (§4)
            if self.sum() != Num(0) or self.i != start + 1:
                self.fail("hash-nonzero", "write a - b # 0 (D12)", tok)
            return NonZero(lhs)
        op = self.expect(*(RELS if top else RELS[1:]))[1]
        nxt = self.peek(1)
        if (op == "==" and self.goal and self.peek()[0] == "mvar"
                and (nxt[0] == "end" or _is(nxt, "@", "/\\"))):
            if self.mvar:
                self.fail("mvar-misplaced", "at most one ?A per goal (D15)")
            self.mvar = True
            rhs = MVar(self.take()[1])
        else:
            rhs = self.expr() if top else self.sum()
        if self.at(*RELS):
            self.fail("chained-cmp", "write a < x, x < b (D12)")
        return Rel(op, lhs, rhs)

    def regclass(self):
        tok = self.take()
        if tok[0] == "regk":
            return tok[1]
        if _is(tok, "C") and self.at("^"):
            self.take()
            k = self.take()
            if k[0] == "nat" or _is(k, "omega"):
                return k[1]
        self.fail("syntax", "expected C^k, k a number or omega", tok)

    def domain(self):
        """A list of items, where a bare interval is a raw tuple until
        resolve names its variable (D13)."""
        if self.at("true"):
            self.take()
            return []
        items = [self.item()]
        while self.at(","):
            self.take()
            items.append(self.item())
        return items

    def item(self):
        if self.peek()[0] == "id" and _is(self.peek(1), "in"):
            v = self.var()[1]
            self.take()
            return _interval(v, *self.interval())
        if self.at("[") or self.at("(") and self.opens_interval():
            return self.interval()
        return self.relation(self.sum(), top=False)

    def opens_interval(self):
        """D13: the ( at the cursor opens an interval exactly when a , occurs
        at depth 1 before it closes, with ( [ as openers and ) ] as closers."""
        depth = 0
        for tok in self.toks[self.i:]:
            depth += _is(tok, "(", "[") - _is(tok, ")", "]")
            if depth == 0 or _is(tok, ",") and depth == 1:
                return depth == 1
        return False

    def interval(self):
        opener = self.expect("[", "(")
        lo = self.endpoint()
        self.expect(",")
        hi = self.endpoint()
        closer = self.expect("]", ")")
        raw = (opener, lo, opener[1] == "[", hi, closer[1] == "]")
        _interval("", *raw)  # D18 now, so the offset is this interval's
        return raw

    def resolve(self, sides, items):
        """Name each bare interval with the judgement's one free variable
        (D13), counted as _d13_free counts it."""
        free = _d13_free(sides, items)
        if len(free) != 1 and any(type(it) is tuple for it in items):
            self.fail("D13-unnamed-interval", "name the interval's variable: "
                      "x in [a, b] (D13)",
                      next(it for it in items if type(it) is tuple)[0])
        return tuple(_interval(*free, *it) if type(it) is tuple else it
                     for it in items)


def _d13_free(sides, items):
    """The free variables D13 and R4 mean: fv of the sides, the constraint
    items and every interval's endpoints, never an interval's own variable,
    named or bare. The parser sees exactly this set whether or not a variable
    is printed, so the printer's R4 and the parser's D13 agree on it. An item
    is an Interval, a bare interval's raw tuple, or a constraint."""
    return frozenset().union(*map(fv, sides), *(
        fv(it[1]) | fv(it[3]) if type(it) is tuple else
        fv(it.lo) | fv(it.hi) if isinstance(it, Interval) else fv(it)
        for it in items))


def _interval(var, opener, lo, lo_closed, hi, hi_closed):
    try:
        return Interval(var, lo, lo_closed, hi, hi_closed)
    except Refused as r:
        raise ParseError(r.code, r.message, opener[2]) from None


def _parse(s, sig, goal, rule):
    if type(s) is not str:
        raise TypeError(f"parse takes a str, not {type(s).__name__}")
    p = _Parser(s, _check_sig(sig), goal)
    x = rule(p)
    if p.peek()[0] != "end":
        p.syntax("end of input")
    return x


def parse_term(s, sig=None):
    """Parse one term (GRAMMAR.md §2–§5, §7). `sig` maps each declared
    function symbol to its arity, and is empty when None. `?A` is refused
    (mvar-misplaced). Raises ParseError with a GRAMMAR.md §1 code."""
    return _parse(s, sig, False, _Parser.expr)


def parse_judgement(s, sig=None):
    """Parse one judgement (GRAMMAR.md §4, §6): `l op r [@ D]`, `e # 0 [@ D]`
    or `e in C^k(D)`. A bare interval is given the judgement's one free
    variable (D13). `@ true` and no `@` both give dom == ()."""
    return _parse(s, sig, False, _Parser.judgement)


def parse_goal(s, sig=None):
    """Parse `j /\\ j /\\ ...` into a Goal tuple, allowing ?A per D15, and
    then run check_goal. The parser refuses a second ?A and a D11 clash at
    their tokens, so parser output passes check_goal: re-raising its
    Refused as a ParseError with offset None is only a backstop."""
    def goal(p):
        js = [p.judgement()]
        while p.at("/\\"):
            p.take()
            js.append(p.judgement())
        g = tuple(js)
        clash = bv(g) & fv(g)
        for v in p.bound:
            if v[1] in clash:
                p.fail("D11-bound-and-free", f"{v[1]} is both bound and "
                       f"free in the goal (D11)", v)
        return g
    g = _parse(s, sig, True, goal)
    try:
        check_goal(g)
    except Refused as r:
        raise ParseError(r.code, r.message, None) from None
    return g


# ---------------------------------------------------------------- printer
#
# _show(t, need, left) gives (text, tail). `need` is the §4 level the
# position requires, `left` says whether t starts its context (R1), and
# `tail` whether the text ends in a bare application (R3).

_LEVEL = {Integral: 0, Add: 1, Mul: 2, Div: 2, Neg: 3, App: 4, Deriv: 4,
          Pow: 5, RPow: 5}


def _show(t, need, left):
    """(text, tail) for t, driving _show_steps with an explicit stack
    instead of Python recursion, so a deeply nested term (500 Negs) prints
    rather than raising RecursionError. Each `yield (t, need, left)` in
    _show_steps is a recursive _show call, answered with its result."""
    stack, result = [_show_steps(t, need, left)], None
    while stack:
        try:
            call = stack[-1].send(result)
        except StopIteration as done:
            stack.pop()
            result = done.value
        else:
            stack.append(_show_steps(*call))
            result = None
    return result


def _show_steps(t, need, left):
    if _LEVEL.get(type(t), 6) < need or isinstance(t, Neg) and not left:
        inner = (yield t, 0, True)[0]
        return f"({inner})", False
    if isinstance(t, Num):
        return str(t.n), False
    if isinstance(t, (Var, Const, MVar)):
        return ("?" if isinstance(t, MVar) else "") + t.name, False
    if isinstance(t, Call):
        args = []
        for a in t.args:
            args.append((yield a, 0, True)[0])
        return f"{t.fn}({', '.join(args)})", False
    if isinstance(t, Add):  # a - b is Add(a, Neg b)
        sub = isinstance(t.b, Neg)
        b, tail = yield t.b.a if sub else t.b, 2, False
        a = (yield t.a, 1, left)[0]
        return f"{a} {'-' if sub else '+'} {b}", tail
    if isinstance(t, (Mul, Div)):
        # R2: a Div left operand is parenthesised, which ends no application
        a, spaced = yield t.a, 3 if isinstance(t.a, Div) else 2, left
        b, tail = yield t.b, 4, False
        op = "*" if isinstance(t, Mul) else "/"
        return a + (f" {op} " if spaced else op) + b, tail
    if isinstance(t, Neg):
        a, tail = yield t.a, 4, False
        return "-" + a, tail
    if isinstance(t, (Pow, RPow)):
        base = (yield t.base, 6, False)[0]
        if isinstance(t, Pow):
            return base + (f"^{t.n}" if t.n >= 0 else f"^({t.n})"), False
        if isinstance(t.exp, (Var, Const)):
            return base + "^" + t.exp.name, False
        exp = (yield t.exp, 0, True)[0]
        return base + "^" + f"({exp})", False
    if isinstance(t, (App, Deriv)):
        head, arg = (t.fn, t.arg) if isinstance(t, App) else (
            f"D[{t.var}]", t.body)
        if isinstance(arg, (Num, Var, Const)):
            a = (yield arg, 6, True)[0]
            return f"{head} {a}", True
        a = (yield arg, 0, True)[0]
        return f"{head}({a})", False
    if isinstance(t, Integral):
        body = (yield t.body, 0, True)[0]
        return f"Int[{t.var} = {_end(t.lo)} .. {_end(t.hi)}] {body}", False
    raise TypeError(f"not a term: {t!r}")


def _end(e):
    if isinstance(e, (PosInf, NegInf)):
        return "oo" if isinstance(e, PosInf) else "-oo"
    return _show(e, 1, True)[0]


def _show_interval(iv, named):
    text = (f"{'[' if iv.lo_closed else '('}{_end(iv.lo)}, {_end(iv.hi)}"
            f"{']' if iv.hi_closed else ')'}")
    return f"{iv.var} in {text}" if named else text


def _show_judgement(j, top=True):
    if not isinstance(j, Judgement):
        raise TypeError(f"not a judgement: {j!r}")
    sides = (j.lhs, j.rhs) if isinstance(j, Rel) else (j.e,)
    # a relation side is an expr, a domain constraint's side a sum
    text = [_show(t, 0 if top else 1, True)[0] for t in sides]
    head = (f"{text[0]} {j.op} {text[1]}" if isinstance(j, Rel) else
            text[0] + (" # 0" if isinstance(j, NonZero) else f" in C^{j.k}"))
    # R4: an interval prints bare iff the judgement's free variables are {v}
    # and v is its variable, with "free variables" read as D13 reads them.
    free = _d13_free(sides, j.dom)
    items = ", ".join(
        _show_interval(it, free != {it.var})
        if isinstance(it, Interval) else _show_judgement(it, top=False)
        for it in j.dom)
    if isinstance(j, Reg):
        return f"{head}({items or 'true'})"
    return f"{head} @ {items}" if items else head


def show(x):
    """Print a Term, Interval, Judgement or Goal as ASCII, per GRAMMAR.md §8:
    the fewest parentheses that round-trip, plus rules R1–R4. It never
    renames, and it always satisfies parse(show(t)) == t. A lone Interval
    prints named, `v in [a, b]`."""
    if isinstance(x, Term):
        return _show(x, 0, True)[0]
    if isinstance(x, Interval):
        return _show_interval(x, named=True)
    if isinstance(x, Judgement):
        return _show_judgement(x)
    if isinstance(x, tuple):
        return show_goal(x)
    raise TypeError(f"cannot show {x!r}")


def show_goal(goal):
    """show() for a Goal tuple: the judgements joined by ` /\\ `. This is the
    echo printed before a goal is proved (DESIGN §15.6)."""
    return " /\\ ".join(_show_judgement(j) for j in goal)
