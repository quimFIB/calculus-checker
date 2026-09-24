# Kernel architecture: the proof-of-life

How `kernel/` is cut into modules for `WHAT.md`'s proof-of-life, and the
contracts between them. The specification is `GRAMMAR.md` (syntax, D1–D18)
and `p1_expected.py` (behaviour, E1–E26). Both are frozen: the code is tested
against them. Each skeleton file's docstrings carry the per-function detail;
this file carries what crosses module lines. `§n` is `DESIGN.md` unless it
says otherwise.

**Running.** From the project root, with Python 3.10 or later and nothing
installed, one command:

    python3 kernel/proof_of_life.py

It is the done script: WHAT.md's Done-when items 1–6 against
p1_expected.py, plus the suite's own cases for what P1's data cannot see
(§8), exit 1 on any failure; its last line, `PASS: n of n checks passed`,
gives the current count. Its header prints the protection in force,
`handles for facts, sentinel for proof states`, with the reason the
sentinel is enough for states (§2). It also runs the unit tests in a
child process, as one check shown beside items 1–6: `test_field.py`'s ring,
field and norm_num worked cases, property tests against exact rational
evaluation and five planted bugs, and `test_grammar.py`'s D13, R4 and `# 0`
cases, and subst's refusal under D and capture-avoiding Int rename.
That matters because they are what covers `field`, whose bug would
be a false `Proved`: field's planted bugs `neg_power_wrong_divisor` and
`reduce_drops_q` pass items 1–6 and are caught only there. To run the unit
tests alone: `python3 -m unittest discover -s kernel`.

## 1. Modules

| File | Tier | §15.2 item | Imports |
|---|---|---|---|
| `terms.py` | trusted | 1, 8: nodes, fv/bv, substitution, goal checks, parser, printer | stdlib |
| `entries.py` | trusted | 7: the ten §6.8 entries, pinned | terms |
| `poly.py` | trusted | 4: copied from `spike/ring/poly.py` | stdlib |
| `field.py` | trusted | 4: `ring`, `field`, `norm_num` | poly, terms |
| `deriv.py` | trusted | 2: §6.3's entries, applied | terms |
| `kernel.py` | trusted | 2, 3, 5: rules, E6 and E26's formers, matcher, tracker, handles, `step` | terms, entries, field, deriv, tagger, residual, schema (poly only through field) |
| `tagger.py` | untrusted | none (§7, E24): computes admission tags | terms, poly, field, residual, entries |
| `residual.py` | untrusted | none (§8.7): residual normal form to a term | poly, terms |
| `schema.py` | untrusted | none (§9): the `closed` whitelist | terms |
| `proof_of_life.py` | script | none | everything, p1_expected |

**Keeping the trusted base auditable.** The trusted files are the ones
whose mistakes are false theorems: they build terms and goals, decide
equalities, state the rule table and record what is owed. They are kept
small by keeping out of them everything whose mistakes cannot produce a
theorem, never by a size target. Three kinds of code are moved out by that
argument, each named below: what only proposes (the tagger), what only
renders (residuals), and what only sets a statement's strength (the
`closed` whitelist). What stays in is kept readable by stating each rule
once, as data where it is a table: ENTRIES, `deriv.APP_RULES` and
`kernel.NATURAL_DOMAINS` are read-only mappings, a definedness condition is
one row, and the one child table (`terms.children`) says what every walk
visits. The parser is trusted because a misparse is a different theorem
(§15.2 item 8). Its diagnostic-only branches (hint tables, the D6/D7/D8
relabelling) could move to an untrusted relabeller that runs after a
generic trusted refusal; that is an audit choice for the owner, not done
here.

Standard library only, Python 3.10+. Modules import each other flat, spike
style (`import poly as P`, `from terms import Num`), since the script's
directory is on `sys.path` when `python3 kernel/proof_of_life.py` runs.

**Four changes to the task's layout, each to keep the trusted base small.**
`tagger.py` takes the TAG_RULES machinery (Fourier–Motzkin, sign certificates,
a rational-root factoriser) out of `kernel.py`, because E24 says the tagger is
untrusted. `schema.py` holds the whitelist because §9 says the schema checker
is not trusted. `entries.py` is §15.2 item 7's own file, which both the kernel
and the tagger read. The fourth runs the other way: **`deriv.py` is trusted in
this milestone.** §6.3 calls `deriv` an untrusted tactic that emits one kernel
step per rule. Here `ftc` accepts deriv's output directly, and records the
derivative premise as discharged by `deriv+ring` or `deriv+field`, so
deriv's output forms and side conditions *are* the rule table (§15.2 item 2).
The planted bug `d_ln_emits_nothing` is the proof. Emitting per-rule steps
is later work.

**Trusted code imports untrusted code in three places, and none can
produce a theorem.** `tagger.tag` names the method expected to close an
admission, and nothing relies on it (E24). `residual.residual_term` renders
the residual on a refusal, and a refused step changes nothing (E13).
`schema.closed_ok` filters on statement strength (§9). Neither `field.py`
nor `poly.py` formats anything: the spike's `to_str`, `divide_exact` and
`_Normaliser.residual` now live in `residual.py`.

## 2. Data types

- **Terms** (`terms.py`, GRAMMAR.md §7) are frozen, slotted dataclasses
  under a base `Term`: `Num(n)`, `Const(name)`, `Var(name)`, `MVar(name)`, `Neg(a)`,
  `Add(a, b)`, `Mul(a, b)`, `Div(a, b)`, `Pow(base, n)`, `RPow(base, exp)`,
  `App(fn, arg)`, `Call(fn, args)`, `Deriv(var, body)` and
  `Integral(var, lo, hi, body)`. Binder variables are `str`. An endpoint is a
  `Term`, `POS_INF` or `NEG_INF`. `==` is tree identity with no alpha
  equivalence, and every node is hashable. Slotted means no `__dict__`, so
  `vars(node)` raises. Four invariants are checked where a node is built:
  `Num` holds a natural int, `Pow` an int exponent, `RPow` no literal
  exponent (D17), and an `Interval`'s infinite ends are open (D18).
  `check_goal` runs each constructor's check again on every node it is
  given, so a node built with `object.__new__` is refused `syntax` too,
  including one with a slot left unset, which is refused before the slot is
  read. `oo` and `-oo` are matched by exact type, like every other leaf, so
  a `PosInf` or `NegInf` subclass instance is refused `syntax` as a term.
  The parser refuses a second `?A` (D15) and a D11 clash at their tokens, so
  a goal-level ParseError carries an offset as D16 says; `parse_goal`'s own
  `check_goal` call is then only a backstop.
- **Judgements**, under a base `Judgement`: `Rel(op, lhs, rhs, dom)` with op
  one of `== <= < >= >`, `NonZero(e, dom)` and `Reg(e, k, dom)` with k an
  int or `"omega"`. A **domain** is a tuple of items: `Interval(var, lo,
  lo_closed, hi, hi_closed)`, or a `Rel` or `NonZero` with `dom == ()`.
  `()` is ⊤. A **Goal** is a tuple of judgements.
- **Obligation key** = the `Judgement` itself, domain included. It is exactly
  the tree that `parse_judgement(judgement_string(prop, dom))` builds (E8). A
  `Reg`'s domain is inside it, and E5 never touches it. Every other key is
  built through `terms.with_domain(prop, dom)`, which gives `dom = ()` when
  the proposition has no free variable (E5). A **position domain** is the
  goal's own domain items, then the E4 range interval of each `Integral` whose
  *body* holds the position, outermost first.
- **`Obligation`** (`kernel.py`, frozen and slotted): `key`, `sources`
  (frozenset of p1_expected SOURCES codes, or the kernel-local source codes
  listed in §6), `status` (`"discharged"`, `"admitted"`, or
  `"open"`, which is never produced here), `tag` (`(method, cites)`) and
  `reason` (`"discharge not built"` for an admission, otherwise None). The
  tracker's entries and each step's emission list use this one class. In a
  step's list, `sources` holds only that step's sources.
- **`StepRecord`** (frozen and slotted) is what produced a state. It holds `move`
  (`"install"` or a move name) and `emitted`: one `Obligation` per key this
  step emitted, with all of the step's sources for it, whether or not the
  tracker already had the key. It also holds `occurrences` (rewrite),
  `trace` and `output` (ftc: deriv's), and `handle` (fact). There is no
  `new` flag. The script derives it from the previous state's tracker.
- **`Handle`** (E17) is a module-level `@dataclass(frozen=True, eq=False)`
  with fields `id` (an int, unique across the kernel) and `lineage` (an int).
  It does not define `__copy__`, `__deepcopy__` or `__reduce__`. The private
  registry `kernel._MINTED` maps each id to `_Minted(handle, lineage,
  conclusion, entry)`. A fact slot accepts an object only when
  `type(obj) is Handle`, `_MINTED[obj.id].handle is obj`, and the lineages
  match. It never raises, whatever the object is.
- **`ProofState`** is immutable. It holds `goal` (a Goal, or None once
  closed), `original` (the installed goal), `lineage`, `last` (a StepRecord)
  and `theorem` (the original goal with `?A := value`, after `close`). Its
  accessors are `obligations()` (a tuple of Obligation, in insertion order)
  and `conclusion(handle)`. Its `__init__` demands a private token. Every
  state the kernel makes goes into a private `WeakSet`, and `step` and
  `report` refuse anything else, so neither a forged state nor a copied
  one gets in. Nothing loads a state from `str`, `bytes` or a `dict`.
  **In force: handles for facts, sentinel for proof states**
  (`HANDLES_IN_FORCE`, §15.3's "say which is in force"). Fact slots take
  handles, so a theorem cannot be built, copied, pickled or faked from
  outside the kernel. Proof states take the sentinel: the private `_TOKEN`
  is §15.3's fallback applied to states. That is enough for states, for
  three reasons. A verdict-carrying ProofState, a finished one, is only
  ever produced by step(): install() makes the first state, open, and every
  later one is step()'s output, so no caller assembles one. §15.3's
  realistic threat is a buggy tactic that builds a result object instead of
  calling the kernel, and a state built without the token, or copied, is
  refused. And §16.3's API boundary, not built in this milestone, will
  replace in-process states with ids, so that no state crosses it. What
  neither model stops is a deliberate write through private names, which
  §15.3 says Python cannot prevent: `_TOKEN`, `object.__setattr__`, `gc`,
  `state._tracker._entries.clear()` (a finished state then reports
  'Proved.'), or rebinding `_MINTED[h.id]` (a genuine handle then stands
  for any conclusion). Nobody does these by accident.
- **`Refusal`** (frozen) holds `code`, `message` and `residual` (a Term or
  None). `step` and `install` return one. Inside the kernel every refusal is
  the exception `terms.Refused(code, message, residual=None)`, and `step`
  converts that exception, and only that one, into a returned `Refusal`.
  Any other exception is a kernel bug, and it propagates (E21: a crash, not
  a refusal).

## 3. Public signatures

```python
# terms.py
parse_term(s, sig=None) -> Term            # raise ParseError(code, message, offset)
parse_judgement(s, sig=None) -> Judgement
parse_goal(s, sig=None) -> Goal
show(x) -> str                             # Term | Judgement | Goal | Interval
show_goal(goal) -> str
lit(q) -> Term                             # Fraction/int -> Num | Neg | Div shapes
fv(x) -> frozenset[str];  bv(x) -> frozenset[str]   # GRAMMAR.md §5, D10
subst(x, mapping: dict[str, Term]) -> Term | Judgement   # Refused on D, RPow
instantiate(goal, value) -> Goal           # ?A := value
with_domain(prop, dom) -> Judgement        # E5
check_goal(goal) -> None                   # D11, D15, shadowing, endpoints, §7 leaves,
                                           # constructor checks, check_names; Refused
check_names(*xs) -> None                   # one arity per called name, never a variable
children(t) -> ((step, child), ...)        # the one child table; Call args by index
trees(x) -> iterator[Integral | Deriv]     # E26 (b)'s nodes, prop and domain alike
# entries.py
ENTRIES: Mapping[str, Entry]               # read-only; Entry(name, statement, schema); .hyps
# field.py
ring(lhs, rhs) -> Checked                  # raise NotEqual(residual) | Refused
field(lhs, rhs, facts=()) -> Checked       # facts: ((a_k, r), ...) equations
ring_equal(a, b) -> bool;  ring_is_zero(t) -> bool
ring_polys(terms) -> (list[poly], tuple[Term, ...])   # shared atom table (tagger)
rational_value(t) -> Fraction | None;  norm_num(j) -> bool | None
hypothesis_tree(node) -> None             # always raises; install's gate (E26 (b)); a seam (§7)
# ring, field, ring_equal, ring_is_zero, ring_polys and norm_num raise
# Refused 'Int-or-D-not-normalisable' on an Integral or Deriv node
# (E26 (b)): the normaliser's `_Normaliser.tree`, and norm_num's
# `norm_num_tree(node, in_domain)`, both seams (§7). rational_value
# returns None there instead (an Int or D is never a literal), and
# kernel._range relies on that None.
# deriv.py
APP_RULES: Mapping[str, rule]              # read-only; rule(u, du) -> (output, side_props)
deriv(F, x, dom) -> Derived                # .output .trace .emissions; Refused
const_guard(t) -> None                     # E12's d_const guard; a seam (§7)
# tagger.py / residual.py / schema.py
SIGN_FACTS: dict[str, (str, Judgement)];  tag(key, gamma=()) -> (method, cites)
residual_term(r: Residual) -> Term;  poly_term(p, atoms) -> Term
closed_ok(value) -> bool
# kernel.py
NATURAL_DOMAINS: Mapping[str, u -> props]  # read-only; E26 (a)'s table; a seam (§7)
install(goal) -> ProofState | Refusal
step(state, move, args) -> ProofState | Refusal
report(state) -> str
derivative_domain(closed: Interval) -> Interval
```

## 4. The `step()` contract

`step(state, move, args)` has the shape of §16.3's `/step`. It returns a new
`ProofState`, or a `Refusal` with the input state untouched (E13). The
common checks come first, in this order: the state is one the kernel minted
(`state-not-minted`); the goal is still open (`proof-finished`); the move is
one of the four (`bad-move`); `args` has exactly the move's keys, each of
the right type (`bad-args`). Fact slots are resolved next, before any rule
runs (`fact-not-minted-handle`, `fact-foreign-state-handle`). Each move then
proceeds as follows, with refusals given in the order they are tested:

- **`install(goal)`** checks that the goal has exactly one judgement
  (`goal-shape`), then runs `check_goal` (the GRAMMAR codes). A goal
  hypothesis holding an Int or D node is refused
  `Int-or-D-not-normalisable` (E26 (b)) by `field.hypothesis_tree`, a
  seam of its own apart from E7's `norm_num_tree`, whether or not any key
  carries it: a hypothesis about such a value presupposes that it exists, and
  ftc's Reg premises and its discharged `ftc_D` premise, which carry the
  goal's domain but skip norm_num, would otherwise pass it on. It builds
  the E4 range of every `Integral` (`range-same-infinity`), then charges
  the formers of each goal hypothesis (an Interval's finite ends, a
  relation's two sides, a NonZero's expression) at the hypotheses before
  it, so `@ x > 0, ln x > 0` owes `x > 0 @ x > 0` and not a false
  `x > 0`; then every former of both sides at its position domain (E6 and
  E26 (a), source `former` throughout; E25 then E7, where a false literal
  condition such as ln(-1)'s -1 > 0 refuses `obligation-refuted`, and a
  key holding an Int or D node refuses `Int-or-D-not-normalisable`). It
  returns a state whose `last.move == "install"`.
- **`rewrite`** takes `{"entry": str, "inst": {var: Term}, "at": Term}` and
  optionally `"occurrence": int`. It follows REWRITE_RULE steps 1–11. The
  refusals, in order: an unknown or non-equation entry, or inst keys that are
  not the schema (`bad-args`); instantiation (`rpow-literal-exponent`); step 2
  (`rewrite-target-not-found`); step 3 (`Int-or-D-not-normalisable` when
  either argument holds an Int or D node, E26 (b); else
  `rewrite-lhs-mismatch`); step 6 per occurrence (`rewrite-scope`); step 9
  per occurrence (`rewrite-under-D-needs-open-domain`); then E25/E7 on the
  emissions; then `check_goal` on the new goal. Step 9 tests H and
  every proposition step 10 would charge from R (`kernel._owed` over R's
  subterms, formers nested in a divisor included), both halves: (a) asks
  each for openness in x, so its subterm clause (no x-mentioning
  sqrt/asin/acos/acosh, D or Int) is reached from a move (BAD_MOVES
  rewrite_under_D_R_divisor), and the suite also tests `kernel._open_in`
  directly; (b) refuses a range mentioning x between D[x] and the
  occurrence whenever any of them is owed there, since each would be
  emitted on that closed, x-dependent range, whether it came from H
  (BAD_MOVES rewrite_under_D_through_Int) or from R alone
  (SUITE_BAD_MOVES rewrite_under_D_through_Int_R_former and its ln
  twin). The closing `check_goal` is now a backstop no move reaches: an
  inst value that would carry an Int into a same-named Int's body lies
  in L's argument, which step 3 refuses first. The suite reaches it
  through a seam instead, with step 3 made lax (BACKSTOPS
  rewrite_closing_check_goal, `shadowing`). It emits H at P
  (`rewrite_hyp`) and R's formers at P (`former`). For each `Integral`
  whose interval sits in some emitted key's domain, it also emits E4's
  `lo <= hi` (`orient`) at that Int's own position domain. The orientation
  is emitted only when the interval is used: P1.1's goal owes it at
  installation because sqrt(t^2) in the body owes t^2 >= 0 on the range,
  and MATCH_ACCEPTS limit_former_at_outer_domain owes none, its body t
  owing nothing.
- **`fact`** takes `{"entry": str, "inst": {var: Term}, "bind": str}`
  (`bad-args`). It mints a Handle whose conclusion is `statement[inst]`, with
  the hypotheses kept in the conclusion's domain, and keeps the inst
  values beside it. It emits nothing (E10), and `new_state.last.handle` is
  the handle. A step that uses the fact (ftc's or close's check) inherits
  its hypotheses and its inst values' formers (E6, E26 (a)), at that
  step's domain: an instance built from ln(-1), sqrt(-1) or tan(pi/2) is
  refused or owes its condition there, as it would be anywhere else it
  entered, even when ring cancels it (u := 3 + 0*ln(-1)). The statement's
  own formers are not charged: over schema variables each is the entry's
  hypothesis or always true, and the library statement is trusted.
- **`ftc`** takes `{"F": Term, "check": "ring" | "field", "facts": [obj,
  ...]}`. `ring` with facts is `bad-args`. The goal's lhs must be an
  `Integral` (`ftc-no-integral`), and neither limit may be infinite
  (`ftc-infinite-endpoint`). With G the goal's domain, `I = [a, b]` from E4,
  and `J = derivative_domain(I)`, it emits:
  - the orientation;
  - F's formers at G+I, its partial builtins' domains included (E26 (a));
  - `Reg(F, 0, G+I)`, `Reg(F, 1, G+(a, b))` and `Reg(f, 0, G+I)`, sources
    `ftc_F_C0`, `ftc_F_C1` and `ftc_f_C0`. The C¹ premise builds its open
    interval itself, not through the seam;
  - `deriv(F, x, G+J)`'s emissions. deriv refuses `deriv-no-rule`, and
    `Int-or-D-not-normalisable` where d_const would fire on an x-free
    subterm holding an Int or D node (E12's guard), so no F holding one
    gets past this point. Every divisor it owes is one of F's formers,
    already E25-tested at G+I, and `_emit` tests each emitted NonZero
    again;
  - the check `deriv(F).output == f`, whose divisors are emitted at G+J
    (`field_div`), and whose facts' inst formers (`former`) and
    hypotheses (`fact_hyp`) are emitted at G+J. A side holding an Int or D node refuses
    `Int-or-D-not-normalisable` (ftc consumes only its own top-level Int,
    so one nested in f reaches the check). A failed check refuses
    `ftc-check-failed` with the residual;
  - `Rel("==", Deriv(x, F), f, G+J)`, DISCHARGED with tag `("deriv+" +
    check, fact entry names)`, source `ftc_D`.

  The goal becomes `Add(F[x:=b], Neg(F[x:=a])) == rhs`, and that whole new
  goal's formers are charged too. Last, `check_goal` runs on the new goal.
  It is the only guard against a variable free in F that the goal's rhs
  binds (`D11-bound-and-free`), which a plain move reaches (SUITE_BAD_MOVES
  ftc_F_binder_free_in_rhs: F := x^2 + y - y against an rhs binding y). The
  other direction, an Int in F whose binder is free in the rhs, is refused
  earlier by deriv since E26 (b), and the suite reaches the closing check
  for it through a seam, with deriv's d_const guard off (BACKSTOPS
  ftc_closing_check_goal_Int_in_F).
- **`close`** takes `{"value": Term, "check": "ring" | "field", "facts":
  [...]}`. The goal's rhs must be an `MVar` (`close-no-mvar`). The refusals,
  in order: the value contains an MVar or oo (`bad-args`); E19, fv(value) ∩
  bv(`state.original`) ≠ ∅ (`close-scope-bound-variable`); E23 via
  `schema.closed_ok` (`close-schema-not-closed`). It then charges the
  value's formers at G, E26's included (`obligation-refuted` for 0*ln(-1)).
  It checks `lhs == value`, emitting divisors, the facts' inst formers and
  the facts' hypotheses at G; a side holding an Int or D node refuses
  `Int-or-D-not-normalisable`, and a failed check refuses
  `close-check-failed` with the residual. Last, `check_goal` runs on the
  theorem (`D5-uncalled` when the value names, as a variable, a symbol the
  original goal calls). On success `goal` is None and `theorem` is
  `instantiate(original, value)`. The oo refusal is redundant with E23 today
  (oo is only an Int limit, and the whitelist refuses every Int), and is
  kept on purpose: it is trusted, and no obligation charges an improper
  integral's convergence, so a lax untrusted whitelist must not be the only
  guard.

A check that fails raises `field.NotEqual(residual)`. The kernel turns it
into a Refusal carrying `residual.residual_term(r)`, which is lhs − rhs
(E14). The kernel runs no norm_num, refl, trans or cong move: norm_num runs
at emission (E7), and E16 puts the other three inside the moves above.

**Mapping p1_expected to calls.** The script parses every term string with
`parse_term(s, SIG)` and every goal string with `parse_goal`. Each
`("handle", name)` becomes the Handle from the earlier `fact` step whose
`bind` was name, each `("raw", s)` becomes `parse_judgement(s)`, and
`"FORGED"` becomes the forged object. Everything else passes through
unchanged.

| p1_expected | Call |
|---|---|
| a proof's `"goal"`, MATCH_ACCEPTS or BAD_MOVES `goal` | `install(parse_goal(g))` |
| `("rewrite", {entry, inst, at[, occurrence]})` | `step(st, "rewrite", {"entry": e, "inst": {v: T}, "at": T[, "occurrence": i]})` |
| `("fact", {entry, inst, bind})` | `step(st, "fact", {"entry": e, "inst": {v: T}, "bind": b})`, then `h = st2.last.handle` |
| `("ftc", {F, check, facts})` | `step(st, "ftc", {"F": T, "check": c, "facts": [objs]})` |
| `("close", {value, check, facts})` | `step(st, "close", {"value": T, "check": c, "facts": [objs]})` |
| BAD_MOVES `("install", {})` | `install(parse_goal(g))`, which must return the Refusal |
| a `"state": (proof, sid)` | replay that proof through the step `sid`, and use the resulting state |

## 5. Emission, the tracker and tags

Every obligation goes through
`kernel._emit(buf, key, source, gamma, discharged_by=None, divisor=True)`
into a per-step
buffer, and nothing reaches the tracker until the step has
succeeded. Status is decided in this order:
1. `discharged_by` is given (only ftc's premise), so the status is DISCHARGED
   with that tag.
2. The key is a `Reg`, so it is ADMITTED with `tagger.tag(key)`, which gives
   `("reg", ())`.
3. `field.norm_num(key)` returns True, so the status is DISCHARGED with
   `("norm_num", ())`. If it returns False, the step is refused with
   `obligation-refuted`. A key holding an Int or D node in its proposition
   or its domain is refused `Int-or-D-not-normalisable` here, never
   admitted (E7, E26 (b)). A Reg or a discharged key skips norm_num, so
   this holds for them because every key's domain either comes from a goal
   domain that install already checked for Int and D nodes, or is extended
   by an Int's range whose orientation (or, in ftc, whose F's formers and
   check) passes through norm_num or field first.
4. Otherwise the key is ADMITTED, with reason `"discharge not built"` and tag
   `tagger.tag(key, gamma)`.

`gamma` is the goal-domain part of the key's domain, which is what TAG_RULES
calls Γ. Every divisor goes through E25 (`field.ring_is_zero`) before it is
emitted; `divisor=False` marks tan's cos u # 0, a domain that E25 does not
test (E26). On success the state's `_Tracker` is copied and each buffered
emission goes through **`_Tracker.add(self, emission)`**, the only way into
a tracker. `add` merges an existing key's sources and keeps its status, and
inserts a new key. The step's `emitted` list comes from the buffer and not
from the tracker, so a tracker bug leaves it unchanged (PLANTED_BUGS says
so). A finished state reports `VERDICT.format(n=N)`, where N counts the
ADMITTED entries. Any status other than DISCHARGED or ADMITTED counts as
open and reports `Stuck`, so the count fails closed. It reports `Proved.`
only when every obligation is DISCHARGED, which no PROOFS run reaches (a
goal that owes nothing, e.g. `1 + 1 == ?A` closed with 2, does report it).
An open state reports `Open: <goal>`. `report(state)` takes no other
argument.

**Definedness formers (E6, E26).** `kernel._owed(s)` says what the former
at node s owes: `/` and negative powers their divisor d # 0, RPow its base
> 0, and each partial builtin its `NATURAL_DOMAINS` row. The table is one
linear item per bound, `u REL c` (GRAMMAR.md D12): ln u owes u > 0, sqrt u
owes u >= 0, tan u owes cos u # 0, asin u and acos u owe u >= -1 and u <= 1,
acosh u owes u >= 1, atanh u owes u > -1 and u < 1. Closed where the
builtin is defined at the end, open where it is not. It is not written
abs u <= 1, because abs u is an opaque atom to every §5.3 method and no
entry concludes it, so it could only be tagged none; and not 1 - u^2 >= 0,
because sign product never closes a non-strict goal and the polynomial
hides the two linear bounds that range reads directly. `_charge_formers`
emits them wherever a term enters (the goal's hypotheses at the hypotheses
before each, and both sides at install; ftc's F and new goal; a rewrite's R;
close's value; and a used fact's inst values at the using step's domain,
E10), at the position domain, so the same
E4, E5, E7, E8 and E24 apply as to a divisor. field is unchanged: it emits
its divisors and nothing for the partial builtins in its input, whose
atoms were charged where they entered. Integral and Deriv nodes owe no
condition, because none can be stated until regularity and `diverges`
exist, so they are refused instead (E26 (b)): field's normaliser refuses a
side holding one (every entry point normalises through it), norm_num
refuses an obligation holding one in its proposition or domain, and deriv
refuses to read an x-free one as a constant. **No P1 step is affected**:
ftc consumes the goal's top-level Int, and decides its derivative premise
on deriv's output, which holds no Int or D; no P1 F holds one; every
other ring, field and norm_num input in P1 holds none; and no P1 goal has
a domain at all, so none holds a former or an Int or D node for install's
hypothesis charge to find. The script checks that by running every proof
unchanged.

## 6. Refusal codes

p1_expected's REFUSAL_CODES are used verbatim, E26's
`Int-or-D-not-normalisable` among them (raised by field's normaliser,
norm_num and deriv's d_const guard; none of those modules formats it
differently). `install` also returns the
GRAMMAR.md §1 codes that `check_goal` raises, and constructors can raise
`rpow-literal-exponent` and `oo-misplaced`. Beyond those, there are
**kernel-local codes, none reachable in any P1 run**: `state-not-minted`,
`proof-finished`, `bad-move`, `bad-args`, `goal-shape`, `ftc-no-integral`,
`close-no-mvar` and `field-fact-shape`. The last is for a fact that is not
`a^k == r`, such as `fact pi_pos` passed to field. The suite's
`KERNEL_LOCAL_CODES` lists these eight, and a case must assert each one.

**Kernel-local source codes, none reachable in any P1 run**: `d_inv` (u =
1/v with x free in v, owing v # 0) and `d_pow_int` (a negative literal n,
owing base # 0). deriv reports a firing's rule name as the source, so any
APP_RULES entry added later with a side condition reports `d_<fn>`. P1's
only such rules, d_ln and d_sqrt, are already in SOURCES.

## 7. Planted bugs and definedness mutations: seams patched in a child process

The trusted code carries no bug switch: no flag, env var or global it reads.
Instead it has **seams**, ordinary code that the implementation must keep
exactly as named, looked up at call time and never copied at import. Four
serve PLANTED_BUGS:

| PLANTED_BUGS key | Seam | The child's patch |
|---|---|---|
| `d_ln_emits_nothing` | the `deriv.APP_RULES` mapping, read by its global name at call time | `patch.object(deriv, "APP_RULES", MappingProxyType({**deriv.APP_RULES, "ln": lambda u, du: (orig(u, du)[0], ())}))` |
| `ftc_derivative_premise_on_closed` | `kernel.derivative_domain`, called by its global name in `ftc` only | `patch.object(kernel, "derivative_domain", lambda iv: iv)` |
| `tracker_drops_one` | `kernel._Tracker.add` | a wrapper that drops emissions whose key is in `drop_keys`, then calls the original |
| `tracker_drops_reemitted` | `kernel._Tracker.add` | a wrapper that drops that one key the first time only |
| `pi_pos_not_in_constraint_set` | `tagger.SIGN_FACTS`, read at call time | `patch.dict(tagger.SIGN_FACTS, clear=True)` |

Seven more, in six rows, serve p1_expected's DEFINEDNESS_MUTATIONS,
which the data allows to be planted wherever this file names a seam.
Each patch is the mutation's own text, written in `proof_of_life.py`:

| DEFINEDNESS_MUTATIONS keys | Seam | The child's patch |
|---|---|---|
| the 19 table mutations (`no_ln_former` … `atanh_closed`) | `kernel.NATURAL_DOMAINS`, read by `_owed` at call time | `patch.object(kernel, "NATURAL_DOMAINS", ...)` with the builtin's row removed or replaced |
| `ring_reads_Int_as_atom`, `ring_reads_D_as_atom`, `field_reads_Int_as_atom`, `field_reads_D_as_atom` | `field._Normaliser.tree`, which `norm` calls for each Integral or Deriv node | a method that returns the spike's tree atom for that node kind in ring's (or field's) normaliser, and calls the original otherwise |
| `norm_num_admits_Int`, `norm_num_admits_D`, `norm_num_ignores_domain` | `field.norm_num_tree(node, in_domain)`, which only norm_num calls, and `field.hypothesis_tree(node)`, install's gate on the goal's hypotheses | a wrapper on each that returns instead of raising for that node kind, or for any node in the domain (a hypothesis counts as one); both, because the data's caught_by names install cases the gate refuses first |
| `deriv_d_const_on_Int_or_D` | `deriv.const_guard` | `lambda t: None` |
| `rewrite_R_former_at_goal_domain`, `rewrite_R_former_on_ranges_only` | `kernel._charge_formers`, which only rewrite calls with `anc=` | a wrapper that charges R at the goal's domain, or at the position domain less the goal's items |
| `limit_former_on_own_range` | `kernel._encloses(slot)`, which `_positions` asks whether an Int's child is in its scope | `lambda slot: True` |

`proof_of_life.py` runs each bug as `[sys.executable, __file__, "--plant",
name]`, and each mutation with `--mutate` in place of `--plant`. The
child first asserts that its seam exists: `patch.dict` would add a
missing key without complaint. It then applies the patch with
`unittest.mock` and runs every proof in PROOFS, collecting mismatches in PLANTED_BUGS's
`caught_by` shapes. It prints one JSON object, `{"mismatches": [...],
"admissions": {proof: N}}`, and exits 0, or 2 on any exception that is not
the suite's own `Mismatch`. The parent requires exit 0, requires every
`caught_by` entry to appear among the mismatches, and requires `admissions`
to equal the bug's. A mutation child also runs every BAD_MOVES,
DEFINEDNESS_CASES and MATCH_ACCEPTS case and adds `[table, id]` for each
that fails, which is the shape DEFINEDNESS_MUTATIONS' caught_by names; the
parent requires every caught_by entry, and `admissions` where the data
gives it (`sqrt_open_at_0` gives none, since it refuses the fallback's
ftc). The mutation children run a few at a time. The control child runs
the proofs and the cases unpatched and must find nothing. The patch lives
and dies with a process that runs nothing else.

Two more cases, the suite's own **BACKSTOPS**, use two of these seams for a
different end: to reach a closing `check_goal` along a path that an earlier
refusal stops first (all of rewrite's; for ftc, an Int in F). Each child
(`--backstop NAME`) weakens that earlier refusal, replays one
SUITE_BAD_MOVES move and prints `{"result": code}`; the parent requires the
closing check's code, so deleting the check fails the case.

| BACKSTOPS key | Seam | The child's patch | Expected |
|---|---|---|---|
| `rewrite_closing_check_goal` | `field.ring_equal`, called by its module name in rewrite's step 3 | `lambda a, b: True` | `shadowing` on rewrite_inst_shadows |
| `ftc_closing_check_goal_Int_in_F` | `deriv.const_guard` | `lambda t: None` | `D11-bound-and-free` on ftc_F_holds_Int_binder |

Two more, the suite's own **ISOLATED_SEAMS**, weaken each of E26 (b)'s
two checks alone, since the data's three norm_num mutations weaken both.
Each child (`--isolate NAME`) replays several suite and data bad moves and
prints `{"results": {id: code or "accepted"}}`; the parent requires the
move only that seam guards to be accepted, and the moves the other check
still stops to keep their refusal.

| ISOLATED_SEAMS key | Seam | The child's patch | Accepted | Still refused |
|---|---|---|---|---|
| `norm_num_ignores_domain_only` | `field.norm_num_tree` | skip when `in_domain` | norm_num_refuses_Int_in_range_domain and its 1/x twin | norm_num_refuses_Int_in_domain, goal_hyp_holds_Int (the gate) |
| `install_admits_hypothesis_trees` | `field.hypothesis_tree` | `lambda node: None` | goal_hyp_holds_Int, goal_hyp_holds_D | norm_num_refuses_Int_in_domain, norm_num_refuses_D_in_domain, norm_num_refuses_Int_in_range_domain (E7) |

The kernel has no module-level cache a patched run could leave
behind, and the unpatched run never imports `unittest.mock`.

## 8. What `proof_of_life.py` asserts (Done-when 1–6)

The header prints the kernel's `HANDLES_IN_FORCE`, `handles for facts,
sentinel for proof states`, and a line giving the reason the sentinel is
enough for states (§2). For each proof in PROOFS, the script
echoes `show_goal` of the installed tree before s1, checks ECHO and
`ECHO_NONCANONICAL`, and asserts:
- each step's `goal_after` as a tree;
- `last.emitted` against EXPECTED_OBLIGATIONS as a set of keys, with per-key
  sources, status and tag, and with `new` computed from the previous
  state's keys;
- `occurrences`, and the fact step's `conclusion(h)`;
- for ftc, `last.trace` as a multiset of `(rule, subterm)`, and `last.output`
  and the emissions, against DERIV;
- the final `obligations()` against FINAL_TRACKER, and N against ADMISSIONS;
- `report(st) == VERDICTS[p]`, and `theorem`;
- that no admission is tagged `none`.

The alternative form of P1.2 is `P1.2-alt`. Every refusal the script checks,
from WRONG_ANSWERS, BAD_MOVES and PARSE_REFUSALS, is asserted by its code.
For each wrong answer it also asserts two things with `field.ring`/`field.field`:
that the residual is equal under `compare`, and that the residual is not
zero. The script then runs MATCH_ACCEPTS (installation's list as well as
the move's), DEFINEDNESS_CASES (installation's and the close's lists, the
final tracker, the exact report and the theorem, with no no-none
assertion, since two of their admissions are false and tagged none on
purpose), OCCURRENCE_CASE, FORGERIES (per
E21's accept and post rules, at FORGERY_STATE), the parser round trip over
ROUND_TRIP with ROUND_TRIP_SIGS (trees checked by a script-side S-expression
printer in GRAMMAR.md §9's notation), PRINT_EXACT, the planted bugs and the
30 definedness mutations as in §7 (under item 3), and a `math`-module check
of NUMERIC.

It also runs **the suite's own cases**, for rules P1's data cannot see. They
are not p1_expected data and do not carry its "(added)" label; each cites
the decision its expected value comes from, and each was confirmed to fail
on the mutation it guards against. Under item 2: field's divisors inside
atom arguments, ftc's charge of F's formers on [a, b], ftc on a reversed
literal range, occurrence 1, emission placements (both sides at install, a
goal hypothesis's formers at the hypotheses before it, an Interval
hypothesis's ends included, orientation only when a key uses the range, a
fact hypothesis on the check's domain, a fact's inst formers on the using
step's domain (ln and tan), negative-power and RPow formers, -oo ends,
reversed literal ends, nested Ints' orientations, and an orientation keeping
the goal's domain, and the n = -1 power), and TAG_RULES read both ways, with
a non-empty gamma in some rows and the kernel's gamma-is-() rule for a
closed key. Under item 6: the suite's own rows for the GRAMMAR.md §1 codes
no p1_expected parse case names, and the offsets of goal-level parse
refusals (D16). Under item 4: deriv's d_inv and negative d_pow_int sides,
and d_const on an x-free App. Under item 5: bad moves for the REFUSAL_CODES
and kernel-local codes no p1_expected case reaches and for rule clauses it
does not exercise (REWRITE_RULE's same head, its non-App tree match and the
occurrence range both ways, ring with facts, fact's exact schema, E23 for D
and for a Call, install's one-judgement rule, install's charge of the goal's
hypotheses (ln(-1) > 0 refuted, an Int or D in a hypothesis refused), E7's
domain check reached with nothing in front of it (an Int in a range end
whose other end is infinite), a fact's inst former refuted at close and at
ftc (ln(-1) and sqrt(-1) cancelled by ring), REWRITE_RULE 9(b) on R's
formers alone, `range-same-infinity`, close's oo refusal, and the closing
`check_goal` of close and of ftc, the latter reached by F := x^2 + y - y
against an rhs binding y; the case that reached rewrite's closing
`check_goal` before E26 now pins the earlier `Int-or-D-not-normalisable`, as
does an Int inside ftc's F); two BACKSTOPS cases, each in a child process,
that weaken the earlier refusal through its seam (field.ring_equal for
rewrite's step 3, deriv.const_guard for ftc) and assert the closing
`check_goal` then refuses the move (`shadowing`, `D11-bound-and-free`), so
deleting either check fails a case; two ISOLATED_SEAMS cases (§7); refusals
called directly where no move reaches (subst under D and into RPow, and
`check_goal`'s D11, D15, shadowing and endpoint guards on hand-built goals);
a coverage check that spans every REFUSAL_CODES code (p1_expected's
"unreachable in P1" notes excuse none), the kernel-local codes and
GRAMMAR.md §1's 27 parse codes; hand-built trees refused `syntax` (forged
Num, Pow, RPow and Interval, and oo look-alike subclasses, among them),
nodes and a Handle with unset slots refused rather than raised, a handle
whose lineage field was rewritten, non-tuple Call args in every step slot,
the sig-free Call name check, a vars() write attempt on every record an
accessor returns, a report that fails closed on an unknown status, a
read-only ENTRIES and APP_RULES, rewrite refusing a non-equation entry, and
REWRITE_RULE 9(a)'s subterm clause called directly. The unit tests run last,
in a child process, as their own check; since E26 (b) they assert that ring,
field, their helpers and norm_num refuse Int and D nodes, and the property
tests fail if either procedure decides a random pair holding a Deriv.

It does not stop at the first failure. It exits non-zero if any case
failed, and prints the verdict of each proof last.
