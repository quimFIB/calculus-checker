# Concrete grammar: terms, judgements, goals

The syntax the kernel's parser reads and its plain-text printer writes. It is
`WHAT.md`'s "Before any code" item 1, and it makes `DESIGN.md` §5.1 (terms),
§5.2 (judgements), §5.3 (domains) and §9 (`?A`) concrete. The parser is in
the trusted base (§15.6), so every choice below takes a refusal over a guess.
**Dn** marks a decision the design left open; each one gives its reason and
the § it interprets.

**In scope:** terms, endpoints, atomic judgements, domains and goals.
**Out of scope:** the problem-file and proof-script layer. In this milestone
moves and their arguments are Python data passed to `step(state, move, args)`:
`close`'s value and `rewrite`'s instantiation `u := pi/2` are `Term`s from
`parse_term`, and rule names are strings.

## 1. Entry points

| Function | Returns | `?A` allowed |
|---|---|---|
| `parse_term(s, sig)` | `Term` | no |
| `parse_judgement(s, sig)` | `Judgement` | no |
| `parse_goal(s, sig)` | `Goal`, a tuple of judgements | yes, see §6 |
| `show(x)` | `str`, for any of the three | n/a |

`sig` maps each declared function symbol to its arity (≥ 1) and is empty by
default. Every refusal raises `ParseError(code, message, offset)`. `code` is
a stable string from the table below and is what tests assert. The message
wording is the kernel's. `offset` is the character index of the offending
token, or None for a refusal of `sig` itself.

**D16: parse refusals carry a stable code** (§15.6). This mirrors
`p1_expected.py`'s REFUSAL_CODES for moves, so the trusted parser's tests
check *why* it refused, not only that it refused. Without a code, a parser
that refused `f(x, y)` with `{'f': 1}` for the wrong reason, or refused
`x^-1` in the lexer, would pass. (D16 to D18 are numbered in the order they
were added, not by section.)

| Code | Refusal |
|---|---|
| `D1-decimal` | a decimal literal such as `0.5` (D1) |
| `implicit-mul` | digit then letter, `2x` (§2), and D9's "write a*b" after a complete `unary` |
| `non-ascii` | a non-ASCII character that is not one of §2's synonyms |
| `D2-deferred` | a deferred name (D2) |
| `D3-bare-e` | bare `e` (D3) |
| `reserved-hint` | `log`, `sec` and the other names §3 refuses with a hint |
| `D4-not-a-name` | an IDENT that is no class of §3, `sinx`, `xy` |
| `D5-undeclared` | an undeclared name called, `f(x)`, `x(x+1)` |
| `D5-arity` | a declared function called with the wrong number of arguments |
| `D5-uncalled` | a declared function used without `(` |
| `D5-sig-collision` | a `sig` entry that is a reserved word, builtin, constant or keyword |
| `D5-sig-arity0` | a `sig` entry with arity 0 |
| `D6-ambiguous-app-power` | `sin(x)^2`, `sqrt(3)^2` |
| `D6-neg-operand` | a juxtaposed operand beginning with `-`, `sin -x` |
| `D6-app-as-base` | an application used as a power base |
| `D7-int-in-arith` | an unparenthesised `Int` inside arithmetic |
| `D8-pow-chain` | `x^2^3` |
| `D8-neg-exponent` | `x^-1` |
| `bound-in-endpoint` | an `Int`'s variable in its own endpoints (§5) |
| `shadowing` | an `Int` rebinding the name of an enclosing `Int` (§5) |
| `D11-bound-and-free` | a goal with bv ∩ fv ≠ ∅ (D11) |
| `D13-unnamed-interval` | a bare interval on a judgement without exactly one free variable |
| `oo-misplaced` | `oo` anywhere but an `Int` limit or the open end on its own side of an interval (D18) |
| `nesting-too-deep` | a term nested too deeply for the parser, e.g. 200 parenthesised `sin(…)`. The parser converts its own stack overflow into this refusal, so no input crashes it (2026-09-25) |
| `chained-cmp` | `a < x < b` (D12) |
| `hash-nonzero` | `a # b` with b not the literal 0 (D12) |
| `mvar-misplaced` | `?A` anywhere but the whole right side of one `==` in a goal (D15) |
| `syntax` | anything else malformed: an unexpected token, an unbalanced bracket, a missing operand |

Every refusal this file names has a code, including `shadowing`,
`D11-bound-and-free`, `D13-unnamed-interval` and the catch-all `syntax`.
`rpow-literal-exponent` (§7) is not a parse code: the parser never builds
such a node, and the refusal comes from the constructor. `oo-misplaced` is
both: the parser raises it, and so does the `Interval` constructor (§7, D18),
so intervals the kernel builds are held to the same rule.

## 2. Lexical structure

Whitespace (space, tab, newline) only separates tokens. There are no comments.
`--` is two minus tokens, and the printer never emits it (§8).

| Token | Form | Notes |
|---|---|---|
| NAT | `[0-9]+` | **D1:** there are no decimal literals. `0.5` is refused with "write 1/2". Every literal in §6.3, §6.8, §11 and S1–S3 is an integer or a quotient. Decimals appear only in §11.2's `approx`, which is stage 2 and will need its own literal syntax outside terms. Without decimals `Num` holds a natural number, and the integer-exponent test stays lexical (§4). |
| digit then letter | `2x`, `5e-6` | refused: "no implicit multiplication: write 2*x" |
| IDENT | `[A-Za-z][A-Za-z0-9_]*` | classified in §3 |
| MVAR | `?` IDENT, no space | `?A` |
| REGK | `C` followed directly by superscript digits, or `Cω` | `C⁰`, `C¹`, `Cω`, the same as `C^0`, `C^1`, `C^omega` |
| operators | `..` `==` `<=` `>=` `/\` `->` `+ - * / ^ ( ) [ ] , = < > # @` | lexed longest match first |

Some Unicode is accepted as a synonym, so goals can be pasted from `DESIGN.md`:
`≐`→`==`, `≤`→`<=`, `≥`→`>=`, `∈`→`in`, `∧`→`/\`, `⊤`→`true`.
Any other non-ASCII character is refused. The common cases get a hint:
`−` (U+2212), `·`, `π`, `√`, `∞`, `≠`.

## 3. Names

An IDENT is classified in this order:

| Class | Members | Behaviour |
|---|---|---|
| constant | `pi`, `e_const` | `Const` node (§5.1) |
| builtin function | `sin cos tan asin acos atan exp ln sqrt abs sinh cosh tanh asinh acosh atanh` | a prefix taking one operand (§4). Exactly §5.1's sixteen. |
| keyword | `D`, `Int`, `in`, `oo`, `true` | syntax only. `C` and `omega` are keywords only straight after `in`. Elsewhere they are ordinary names. |
| deferred | `Sum`, `lim`, `conv`, `absconv`, `diverges`, `exists`, `dim` | **D2:** refused with "not supported in this kernel yet". No proof-of-life goal needs them. Their syntax is fixed now so that adding them later is additive: `Sum[n = b .. b] e` has `Int`'s shape, and `lim[x -> b] e` takes an optional `^+` or `^-` just before `]`. |
| refused, with a hint | `e` ("write `exp(u)` for eᵘ, `e_const` for the number e"), `log`→`ln`, `sec csc cot sech`→`1/cos u` and so on, `arcsin arccos arctan`→`asin acos atan`, `arsinh arcosh artanh`→`asinh acosh atanh`, `inf infinity`→`oo` | see D3 |
| declared function | the keys of `sig` | must be applied: `f(e, …, e)` with the declared arity |
| undeclared call | any IDENT not matched above and directly followed by `(` (the next token, whitespace allowed) | refused per D5: "x is not a declared function symbol; write x*(…)" |
| variable | matches `L[0-9]*(_[A-Za-z0-9]+)*`, where L is one ASCII letter or a spelled Greek letter (`alpha` … `omega`, but not `pi`) | `Var` node |
| anything else | `sinx`, `xy`, `cost` | refused: "not a name: write sin x, or x*y" |

**Partial builtins parse like the rest.** Seven of the sixteen are partial:
`ln`, `sqrt`, `tan`, `asin`, `acos`, `acosh` and `atanh`. The grammar
accepts any operand, so `ln(-1)` and `0*acos 2` parse and print.
Definedness is a proof obligation, not syntax. `p1_expected.py` E26 charges
each one's domain condition when its term enters the proof. A false literal
condition refuses the installation or the move with `obligation-refuted`,
which is a kernel code, not a parse code. `Int` and `D[x]` terms likewise
parse wherever §4 allows them; E26 (b) is what refuses to normalise them,
or to differentiate an x-free one as a constant (E12's `d_const`).
The parser stays out of this because a domain is a fact about values, which
it cannot decide (`ln(x - y)` depends on x and y), and a refusal that fired
on literals only would be a second, weaker copy of the kernel's rule.

**D3: bare `e` is refused, not read as a variable.** Read as a variable,
`e^x` is a real power `(rpow e x)` that owes `e > 0` and differentiates by
`d_pow_real`. That is a different theorem from `exp x`, and it is exactly the
misparse §15.6 warns about. The spike's `terms.py` read it that way. A refusal
costs the learner one retyping.

**D4: variables are single letters, with an optional digit or `_` suffix, or
spelled Greek letters.** So the classic slips `sinx`, `lnx` and `xy` are
refused rather than becoming fresh variables. `v0`, `x_1`, `v_inf` and
`theta` still work. Declared functions may have longer names (`erf`).

**D5: only declared symbols may be called** (§5.1, `f(e, …, e)`). A name that
is neither declared nor builtin, followed by `(`, is refused with "x is not a
declared function symbol; write x*(…)". That covers `x(x+1)`, and `f(x)` with
`f` undeclared. A declared name used without `(` is refused. So is an arity
mismatch, and so is a `sig` entry that collides with a reserved word or has
arity 0 (a constant should be declared as a variable). The undeclared-call
check is §3's "undeclared call" row, so it comes before the variable pattern
test and the "anything else" row: `erf(1)`, `foo(x)` and `x(x+1)` all get
D5, while `erf`, `sinx` and `xy` with no following `(` still get "not a
name". Because the row sits after the deferred, hint and declared rows,
`log(x)` keeps its `ln` hint, `e(x)` stays D3, and `Sum(` and `lim(` stay
D2.

## 4. EBNF, precedence and `^`

```
goal      = judgement { "/\" judgement } ;
judgement = expr REL expr [ "@" domain ]
          | expr "#" "0" [ "@" domain ]              (* "0" is the NAT 0 itself *)
          | expr "in" regclass "(" domain ")" ;      (* no trailing @ *)
REL       = "==" | "<=" | "<" | ">=" | ">" ;
regclass  = REGK | "C" "^" ( NAT | "omega" ) ;
domain    = "true" | item { "," item } ;
item      = [ VAR "in" ] interval | sum CMP sum | sum "#" "0" ;
CMP       = "<=" | "<" | ">=" | ">" ;
interval  = ( "[" | "(" ) endpoint "," endpoint ( "]" | ")" ) ;
expr      = binder | sum ;
binder    = "Int" "[" VAR "=" endpoint ".." endpoint "]" expr ;
sum       = product { ( "+" | "-" ) product } ;       (* left-assoc *)
product   = unary { ( "*" | "/" ) unary } ;          (* left-assoc *)
unary     = "-" unary | power ;
power     = atom [ "^" exponent ] | app ;            (* no second "^" *)
app       = prefix operand ;
prefix    = BUILTIN | "D" "[" VAR "]" ;
operand   = app | ( NAT | VAR | CONST ) [ "^" exponent ] | "(" expr ")" | call ;
exponent  = NAT | VAR | CONST | "(" expr ")" ;
atom      = NAT | VAR | CONST | MVAR | call | "(" expr ")" ;
call      = DECLARED "(" expr { "," expr } ")" ;
endpoint  = "oo" | "-" "oo" | sum ;
```

| Level | Forms | Associativity |
|---|---|---|
| 0, loosest | `Int[x = a .. b] body` | the body is an `expr` and extends as far right as it can |
| 1 | `a + b`, `a - b` | left |
| 2 | `a * b`, `a / b` | left |
| 3 | `-a` | prefix |
| 4 | application by juxtaposition, `sin u` and `D[x] u` | prefix, nests to the right |
| 5 | `a ^ n` | none |
| 6 | atoms: literal, name, `?A`, `f(…)`, `( … )` | none |

**D6: juxtaposed application takes a power as its operand, and never a
parenthesised group raised to a power.** So `sin x^2` is `sin(x^2)`, as a
textbook reads sin x², and `sin x * y` is `(sin x)*y`. `sin(x)^2` and
`sqrt(3)^2` are refused with "ambiguous: write sin(x^2) or (sin x)^2". Reading
them as sin(x²) is the famous trap, and reading them as (sin x)² contradicts
`sin x^2`. The operand cannot begin with `-` either: write `sin(-x)`. An
application can never be a power base; write `(sin x)^2`. The printer never
emits the textbook form `f a^n` (§8), so the echo always shows which reading
was taken. `D[x]` is a prefix at the same level, which is how §6.3 writes it:
`D[x]u * v` is `(D[x] u)*v`.

**D7: `Int` is a loose binder, and must be parenthesised inside arithmetic.**
§11 writes `Int[t = 0 .. pi/2] sin t * (2*t)` for the integral of the whole
product, and `a + Int[…] f` is refused. Write `2*(Int[…] f)`.

**D8: `^` is not associative, and its exponent is restricted.** It takes a NAT,
a name, or a parenthesised expression. `x^2^3` is refused with "write (x^2)^3
or x^(2^3)"; the spike silently read it as the real power x^(2^3), which owes
`x > 0`. `x^-1` is refused: write `x^(-1)`. The parser decides which kind of
power it has from the parsed exponent (parentheses make no node):

| Exponent parses to | Node | Meaning (§5.1) |
|---|---|---|
| `Num n` | `Pow(a, n)` | ring operation (n ≥ 0) |
| `Neg(Num n)` | `Pow(a, -n)` | field operation, owes `a # 0` |
| anything else, including `x^n` with n a variable, `x^(1/2)` and `x^(2^3)` | `RPow(a, e)` | real power, owes `a > 0` |

This table is also a constructor invariant (§7, D17): no `RPow` with a
literal integer exponent can be built by any path, so the parser's choice
cannot be undone later by substitution.

**`Pow(a, 0)` is 1 for every `a`, including 0** (E58, 2026-09-24). This is
`ring`'s convention: an integer power is repeated multiplication, and the
empty product is 1. So `0^0` is 1 and owes nothing. `RPow` is unaffected and
still owes `a > 0`, and a limit of the form 0⁰ is §6.7's business, not a
term's value.

**D9: unary minus binds tighter than `*` and `/`, and looser than application
and `^`.** So `-x^2` is `-(x^2)`, `-t*sin t` is `(-t)*(sin t)`, and `a*-b`
parses. This agrees with the spike and with how §6.3 writes `-(sin u) * D[x]u`.
There is no unary plus, and there is no subtraction node: `a - b` is
`Add(a, Neg b)`, the same tree as `a + -b` (§5.1 has no subtraction former).
There is no implicit multiplication. After a complete `unary`, a token that
could start an atom is refused with "write a*b": `x y`, `2 (x+1)`,
`sin t x`.

## 5. Binders, endpoints and variables

- **`Int[x = a .. b] e`** binds x in e. a and b are endpoints: a `sum`, `oo`
  or `-oo` (§5.1's class b). Reversed limits are legal syntax, and their
  meaning is §5.1's. The bound variable may not occur in its own endpoints
  (`Int[x = 0 .. x]` is refused), and parsed input never shadows an enclosing
  binder of the same name.
- **`oo` is admissible only as an endpoint:** as an `Int` limit, or as an
  open interval end on its own side (D18). `[0, oo]`, `(oo, 0)` and
  `oo + 1` are refused.
- **D18: an infinite end is admissible in a domain interval only in its
  orientation: `-oo` only as the open lower end, `oo` only as the open upper
  end** (interprets §5.1 and §5.3).
  - §5.1 admits `oo` only as an `Int`/`Sum` limit and a `lim` target.
    Domains are an extension. It is needed because `p1_expected.py` E4
    builds and prints `[0, oo)`, and printed output must parse back (§15.6).
  - A §5.3 domain is a conjunction of constraints, and an interval is
    shorthand for one: `v in (c, oo)` / `[c, oo)` is `v > c` / `v >= c`;
    `(-oo, c)` / `(-oo, c]` is `v < c` / `v <= c`; `(-oo, oo)` is ⊤.
  - An infinite end contributes no constraint, and that is faithful only
    when it is on its own side. `oo` as a lower end has no reading, because
    `oo < v` is not a term (§5.1).
  - So `(oo, c)`, `(c, -oo)`, `(oo, oo)` and `(-oo, -oo)` are refused with
    `oo-misplaced`, and closed infinite ends stay refused as before.
  - This matches E4's convention for `Int` ranges ("PosInf is always the
    open upper end and NegInf always the open lower end").
  - An empty finite interval such as `[1, 0]` stays legal syntax. The
    reason for D18 is that the translation to constraints must exist, not
    that the interval is empty.
- **D10: `D[x] e` binds x in e and evaluates at x, so x is free in the whole
  term.** §5.1 lists `D[x]` among its binders, and inside e x is the
  variable of differentiation (that is the reading §6.3 `d_const`'s "x not
  free in e" uses). But the term denotes the derivative *evaluated at x*, and
  §6.4's `D[x] F ≐ f @ (a, b)` needs x free, because the domain constrains
  it. So fv(`D[x] e`) = fv(e) ∪ {x}. `D[x] x^2` and `D[y] y^2` are different
  functions, so D is not alpha-convertible. If x counted as bound in the
  whole term, §9's scope check would refuse `?A := 2*x` for a goal
  `D[x] x^2 == ?A`. `p1_expected.py` lists the §5.1 wording in
  DESIGN_DEFECTS. **D is not a binder for D11, for the §9/E19 close scope
  check, for the endpoint rule, or for the no-shadowing rule.** It binds
  only in the sense above: x is the differentiation variable inside e and
  free in the whole term.
- **bv, the bound variables.** Every check in this file or in
  `p1_expected.py` that says "bound" means bv(t), the set of variables bound
  by an `Int` node in t:
  bv(`Int[x = a .. b] e`) = {x} ∪ bv(a) ∪ bv(b) ∪ bv(e), bv(`D[x] e`) =
  bv(e), and bv of any other node is the union over its children. D's own
  variable is never in bv, because D10 puts it in fv.
- **Substitution into `D[x] e`.** §15.2 item 1 puts substitution in the
  trusted base. By D10, x is the differentiation variable in e and free in
  the whole term, so the ordinary rule for binders does not apply. The
  kernel's rule, which refuses every case this milestone never needs:
  - if y ∉ fv(`D[x] e`), then (`D[x] e`)[y := s] = `D[x] e`, unchanged;
  - if y ≠ x and x ∉ fv(s), then (`D[x] e`)[y := s] = `D[x]`(e[y := s]);
  - otherwise, including every y = x case, refuse with `subst-under-D`.

  Renaming is not allowed even when s is a variable z. Checked with SymPy:
  (`D[x] x^2`)[x := 1] is 2, while the naive `D[x](1^2)` is 0;
  (`D[x](x*y)`)[y := x] is x, while the naive `D[x](x*x)` is 2x; and
  (`D[x](x*z)`)[x := z] is z, while the renamed `D[z](z*z)` is 2z. In this
  milestone deriv refuses any `Deriv` subterm with x free (no §6.3 rule
  applies), so ftc's F[x := b] only ever reaches the unchanged case.
- **Substitution and `RPow`.** Ordinary substitution rebuilds each node
  through its constructor, so a substitution that would turn an `RPow`
  exponent into a literal, as in (`2^x`)[x := 1], is refused with
  `rpow-literal-exponent` (§7, D17). It is never silently turned into a
  `Pow`: `RPow(u, n)` is defined only where u > 0 and `Pow(u, n)`
  everywhere, so the conversion would drop the `u > 0` obligation (§5.1).
- fv(`Int[x = a .. b] e`) = (fv(e) − {x}) ∪ fv(a) ∪ fv(b). Constants and `?A`
  are not variables.
- **D11: within one goal, bv(goal) ∩ fv(goal) = ∅,** with bv as defined
  above. `D[x] x^2 == ?A` satisfies it (x is free, and bv is empty), while
  `D[x] x^2 + (Int[x = 0 .. 1] x) == ?A` does not. §9's
  "`?A` may not mention a bound variable" then becomes a plain name check.
  The WHAT must-refuse `close ?A := t` with t bound fails it. The check is
  made against the original goal, the one the reported theorem
  instantiates, even after ftc has removed the binder from the current goal
  (`p1_expected.py` E19).

## 6. Judgements, domains and `?A`

| Form (§5.2) | Syntax | Node |
|---|---|---|
| equality | `l == r @ D` | `Rel('==', l, r, D)` |
| order | `l <= r`, `l < r`, `l >= r`, `l > r`, each with an optional `@ D` | `Rel(op, l, r, D)` |
| nonvanishing | `e # 0 @ D` | `NonZero(e, D)` |
| regularity | `e in C^k(D)`, where k is a NAT or `omega` | `Reg(e, k, D)` |

- **D12: all four order relations are separate tags, kept as written.**
  `t >= 0` and `0 <= t` are different trees. Obligation keys are not
  canonicalised either: the tracker keys each obligation in the orientation
  its rule states (`p1_expected.py` E8; see §10). Chains such as `a < x < b` are refused: write `a < x, x < b`.
  `a # b` is refused with "write a - b # 0", because §5.2 has only `e # 0`.
  The definedness conditions of `p1_expected.py` E26 are minted in one
  orientation, `u REL c`: `u > 0`, `u >= 0`, `u >= 1`, and a two-sided
  domain as two items, never a chain (`u >= -1` and `u <= 1`, or
  `u > -1` and `u < 1`). `tan`'s is `cos u # 0`.
- **Domains** (§5.3) are an ordered tuple of items: intervals, and atomic
  order or `# 0` constraints. `@` is omitted for ⊤, and `@ true` is ⊤ written
  out. The four intervals `[a,b]`, `(a,b)`, `[a,b)` and `(a,b]` are distinct
  trees; open and closed are never merged. **D13:** a bare interval names no
  variable, so it constrains the judgement's unique free variable. If there
  is not exactly one, the interval must be named, as in `@ x in [0, 1]`.
  After `@` or `C^k(`, an item that begins with `(` is an interval exactly
  when a `,` occurs at bracket depth 1 before that bracket closes. Both `(`
  and `[` count as openers and `)` and `]` as closers, so `(0, 1]` is an
  interval and `(x + 1) > 0` is a constraint.
- **D14: §6.8's sequent entries are written with `@`.** `sqrt_pos : a > 0 ⊢
  sqrt a > 0` becomes `sqrt a > 0 @ a > 0`. A pointwise hypothesis on the free
  variable is exactly what a domain is (§5.3), so the grammar has no `⊢`.
- **`?A`** (§5.1, §9) is accepted only by `parse_goal`, only as the whole
  right-hand side of an `==`, and at most once per goal. **D15:** that is
  every use in §9, §11 and S1–S3, and it makes `close` a replacement of one
  leaf. `?A` inside arithmetic or a domain is refused.

## 7. Abstract syntax

These are frozen dataclasses. `≡` in `parse(show(t)) ≡ t` is Python `==` on
them: plain tree identity, with bound names compared literally and no alpha
equivalence. The printer never renames.

| Node | Fields | Invariant |
|---|---|---|
| `Num` | `n: int` | n ≥ 0. Negatives are `Neg(Num)`; a fraction p/q is `Div(Num p, Num q)`. The kernel builds literals through `lit(q)`, which produces exactly these shapes. |
| `Const` | `name` | `pi` or `e_const` |
| `Var` | `name` | a variable name (§3) |
| `MVar` | `name` | in goals only (§6) |
| `Neg`, `Add`, `Mul`, `Div` | operands | none |
| `Pow` | `base, n: int` | any int |
| `RPow` | `base, exp: Term` | `exp` is never `Num` or `Neg(Num)`. Constructing one that is raises the refusal `rpow-literal-exponent` (a `__post_init__` check on the frozen dataclass; D17). |
| `App` | `fn, arg` | fn is one of the 16 builtins |
| `Call` | `fn, args: tuple` | fn is declared with `len(args)` arguments |
| `Deriv` | `var, body` | none |
| `Integral` | `var, lo, hi, body` | lo and hi are a `Term`, `PosInf` or `NegInf` |
| `Interval` | `var, lo, lo_closed, hi, hi_closed` | lo is a `Term` or `NegInf`, hi is a `Term` or `PosInf`, and an infinite end is open (D18). Constructing one that is not raises `oo-misplaced` (a `__post_init__` check, as D17 does for `RPow`). |
| `Rel`, `NonZero`, `Reg` | as §6 | the domain is a `tuple` of items; a constraint item is a `Rel`/`NonZero` with an empty domain |

**D17: the `RPow` invariant is enforced where the node is built.** An
`RPow(2, Num 1)` would print as `2^(1)` (§8: an `RPow` exponent other than a
name is parenthesised), which re-parses as `Pow(2, 1)`, a ring operation
with no `2 > 0` obligation. Then parse(show(t)) ≢ t and the echo shows a
different theorem, the misprint class §15.6 exists to catch. Checking in the
constructor covers every path at once: the parser, ordinary substitution
(§5), `ftc`'s F[x := b], rewrite instantiation `lhs[inst]` and `rhs[inst]`,
and `close`. A refusal, not a silent `Pow`, because `RPow(u, n)` owes
u > 0 and `Pow(u, n)` does not (§5.1), so the conversion drops an
obligation. This milestone needs no literal-exponent
`RPow`. The cost is that `ftc` refuses an F containing `a^x` at literal
endpoints until a later step adds a printed form that keeps the node (and
changes D8's table to match).

## 8. Printer

The printer writes ASCII only. It uses the fewest parentheses that round-trip,
except for four readability rules, each marked R. Parentheses never create a
node, so extra ones cannot break a round trip.

- **Levels:** a child is parenthesised when its level (§4 table) is below
  what its position requires. The positions are:
  - the right operand of `+` or `-` needs level 2;
  - the right operand of `*` or `/` needs level 4, and so does the operand of
    unary `-` (R1 below then excludes a `Neg`);
  - a left operand needs its parent's own level;
  - a `Pow` or `RPow` base needs level 6;
  - an `RPow` exponent other than a name is parenthesised.
- **Integrals** print bare only as a whole term, a relation side, a call
  argument, a body or a parenthesised exponent. Anywhere else they are
  parenthesised.
- **Application** prints `sin u` when u is a `Num`, `Var` or `Const`, and
  `sin(u)` otherwise: `sin(x^2)`, `sin(sqrt x)`, `atan(-u)`. The same holds
  for `D[x] u` against `D[x](sqrt(x^2))`. Exponents print as `x^2`,
  `x^(-1)`, `x^n`, `x^(1/2)`.
- **Subtraction:** `Add(a, Neg b)` prints `a - b`.
- **R1:** a `Neg` prints bare only in leftmost position. `a*(-b)`, `a - (-b)`
  and `-(-a)` keep their parentheses, so the output never contains `--`,
  which the problem-file layer uses for comments (see S3 in `WHAT.md`).
  **The base of a `Pow` or `RPow` is never a leftmost position for R1**,
  even though it is printed first. A `Neg` base is always parenthesised by
  the level rule, because the base needs level 6 and `Neg` is level 3. So
  `(pow (neg x) 2)` prints `(-x)^2`, never `-x^2`, which is the misprint
  §15.6 names. `-x^2` is `(neg (pow x 2))`, where the `Neg` is outside the
  power.
- **R2:** a `Div` as the left operand of `*` or `/` is parenthesised:
  `(1/3)*ln 2`, `(1/sqrt 3)*x`, `(a/b)/c`. This is the `a/b*c` ambiguity
  §15.6 worries about.
- **R3:** spacing. There is one space around binary `+` and `-`, relations,
  `#`, `@`, `..`, `=`, `in` and `/\`, and one after `,`. There is none around
  `*`, `/` or `^`, or after unary `-`. The exception is when the left operand
  ends in a bare application: then `*` and `/` get spaces too, as in
  `sin t * (2*t)` and `2*sqrt x * cos(sqrt x)`.
- **R4:** a bare interval is printed without a variable exactly when the
  judgement's free variables are {v} and v is the interval's variable (D13).
  Otherwise it prints as `v in [a, b]`.

## 9. Parses

Trees are S-expressions. `(pow x 2)` has the integer 2 as a field. Apps are
`(sin t)`. Judgements are `(op l r [domain])`, `(# e [domain])` and
`(reg e k [domain])`, and an empty domain is left out. `(iv[] t a b)` is a
closed interval; `(iv())`, `(iv[))` and `(iv(])` are the others. Every row was checked by round-tripping through a
prototype of this grammar.

| Input | Tree | Printed |
|---|---|---|
| `-x^2` | `(neg (pow x 2))` | `-x^2` |
| `sin x^2` | `(sin (pow x 2))` | `sin(x^2)` |
| `1/sqrt 3*x` | `(mul (div 1 (sqrt 3)) x)` | `(1/sqrt 3)*x` |
| `pi^2/4` | `(div (pow pi 2) 4)` | `pi^2/4` |
| `x^2^3` | refused (D8); `(x^2)^3` is `(pow (pow x 2) 3)`; `x^(2^3)` is `(rpow x (pow 2 3))` | none |
| `2*t*cos t` | `(mul (mul 2 t) (cos t))` | `2*t*cos t` |
| `(-x)^2` | `(pow (neg x) 2)` | `(-x)^2` |
| `(-x)^(-1)` | `(pow (neg x) -1)` | `(-x)^(-1)` |
| `a - (-b)` | `(add a (neg (neg b)))` | `a - (-b)` |
| `-(-x)` | `(neg (neg x))` | `-(-x)` |
| `a*(-b)` | `(mul a (neg b))` | `a*(-b)` |
| `e^x`, `x(x+1)`, `f(x)` (f undeclared), `sin(x)^2`, `2x`, `0.5` | refused (D3, D5, D5, D6, §2, D1) | none |

**§11.1** (the substitution step's own obligations included):

| Term | Tree |
|---|---|
| `Int[x = 0 .. pi^2/4] sin(sqrt x) == ?A` | `(== (Int x 0 (div (pow pi 2) 4) (sin (sqrt x))) ?A)` |
| `t^2 in C^1([0, pi/2])` | `(reg (pow t 2) 1 [(iv[] t 0 (div pi 2))])` |
| `0^2 == 0 /\ (pi/2)^2 == pi^2/4` | `(== (pow 0 2) 0)`, `(== (pow (div pi 2) 2) (div (pow pi 2) 4))` |
| `sin(sqrt(t^2)) in C^0([0, pi/2])`; `t^2 >= 0` | `(reg (sin (sqrt (pow t 2))) 0 [(iv[] t 0 (div pi 2))])`; `(>= (pow t 2) 0)` |
| `Int[t = 0 .. pi/2] sin(sqrt(t^2))*(2*t) == ?A` | `(== (Int t 0 (div pi 2) (mul (sin (sqrt (pow t 2))) (mul 2 t))) ?A)` |
| `sqrt(t^2) == t @ t >= 0`; `0 <= t @ [0, pi/2]` (§11.1's display; the tracker's key is `t >= 0 @ [0, pi/2]`, E8) | `(== (sqrt (pow t 2)) t [(>= t 0)])`; `(<= 0 t [(iv[] t 0 (div pi 2))])` |
| `Int[t = 0 .. pi/2] sin t * (2*t) == ?A` | `(== (Int t 0 (div pi 2) (mul (sin t) (mul 2 t))) ?A)` |
| F: `2*sin t - 2*t*cos t` | `(add (mul 2 (sin t)) (neg (mul (mul 2 t) (cos t))))` |
| `F in C^0([0, pi/2]) /\ F in C^1((0, pi/2))` | `(reg F 0 [(iv[] t 0 (div pi 2))])`, `(reg F 1 [(iv() t 0 (div pi 2))])` |
| `D[t] F == sin t * (2*t) @ (0, pi/2)` | `(== (D t F) (mul (sin t) (mul 2 t)) [(iv() t 0 (div pi 2))])` |
| `sin t * (2*t) in C^0([0, pi/2])` | `(reg (mul (sin t) (mul 2 t)) 0 [(iv[] t 0 (div pi 2))])` |
| `2*sin(pi/2) - 2*(pi/2)*cos(pi/2) - (2*sin 0 - 2*0*cos 0) == ?A` | `(== (add (add (mul 2 (sin (div pi 2))) (neg (mul (mul 2 (div pi 2)) (cos (div pi 2))))) (neg (add (mul 2 (sin 0)) (neg (mul (mul 2 0) (cos 0)))))) ?A)`. §11.1's leading parentheses are redundant under left associativity. |
| close value `2`; wrong F `sin t - t*cos t`; its residual `-t*sin t` | `2`; `(add (sin t) (neg (mul t (cos t))))`; `(mul (neg t) (sin t))` |
| fallback F `2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)`, `2*sqrt x # 0 @ (0, pi^2/4)`, `sqrt(pi^2/4)` | `(add (mul 2 (sin (sqrt x))) (neg (mul (mul 2 (sqrt x)) (cos (sqrt x)))))`, `(# (mul 2 (sqrt x)) [(iv() x 0 (div (pow pi 2) 4))])`, `(sqrt (div (pow pi 2) 4))` |

**§11.2:**

| Term | Tree |
|---|---|
| `Int[x = 0 .. 1] 1/(1 + x^3) == ?A` | `(== (Int x 0 1 (div 1 (add 1 (pow x 3)))) ?A)` |
| F: `(1/3)*ln(1 + x) - (1/6)*ln(x^2 - x + 1) + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)` | `(add (add (mul (div 1 3) (ln (add 1 x))) (neg (mul (div 1 6) (ln (add (add (pow x 2) (neg x)) 1))))) (mul (div 1 (sqrt 3)) (atan (div (add (mul 2 x) (neg 1)) (sqrt 3)))))` |
| `1 + x > 0 @ [0, 1]`; `x^2 - x + 1 > 0`; `sqrt 3 # 0` | `(> (add 1 x) 0 [(iv[] x 0 1)])`; `(> (add (add (pow x 2) (neg x)) 1) 0)`; `(# (sqrt 3))` |
| `D[x] F == 1/(1 + x^3) @ (0, 1)` | `(== (D x F) (div 1 (add 1 (pow x 3))) [(iv() x 0 1)])` |
| `1 + ((2*x - 1)/sqrt 3)^2 # 0` | `(# (add 1 (pow (div (add (mul 2 x) (neg 1)) (sqrt 3)) 2)))` |
| `1 + x^3 # 0 @ [0, 1]`; certificate `(x - 1/2)^2 + 3/4`; factorisation `(1 + x)*(x^2 - x + 1)` | `(# (add 1 (pow x 3)) [(iv[] x 0 1)])`; `(add (pow (add x (neg (div 1 2))) 2) (div 3 4))`; `(mul (add 1 x) (add (add (pow x 2) (neg x)) 1))` |
| `F in C^0([0, 1]) /\ F in C^1((0, 1))`; `1/(1 + x^3) in C^0([0, 1])` | `(reg F 0 [(iv[] x 0 1)])`, `(reg F 1 [(iv() x 0 1)])`; `(reg (div 1 (add 1 (pow x 3))) 0 [(iv[] x 0 1)])` |
| fact `sqrt_sq_val 3`: `(sqrt 3)^2 == 3 @ 3 >= 0` | `(== (pow (sqrt 3) 2) 3 [(>= 3 0)])` |
| endpoint subterms (Q21): `ln(1 + 0)`, `atan((2*1 - 1)/sqrt 3)` | `(ln (add 1 0))`, `(atan (div (add (mul 2 1) (neg 1)) (sqrt 3)))` |
| close `(1/3)*ln 2 + pi/(3*sqrt 3)`; accepted alternative `(1/3)*ln 2 + pi*sqrt 3 / 9`; `3*sqrt 3 # 0` | `(add (mul (div 1 3) (ln 2)) (div pi (mul 3 (sqrt 3))))`; `(add (mul (div 1 3) (ln 2)) (div (mul pi (sqrt 3)) 9))`; `(# (mul 3 (sqrt 3)))` |
| `approx ?A ≈ 0.83565 ± 5e-6` | not a term (stage 2, D1) |

**§6.8 entries P1 uses, pinned** (u and a are ordinary variables that the
rule instantiates):
`sqrt(u^2) == u @ u >= 0`, `pi > 0`, `sin(pi/2) == 1`,
`cos(pi/2) == 0`, `sin 0 == 0`, `ln 1 == 0`,
`atan(1/sqrt 3) == pi/6`, `atan(-u) == -atan u`
(`(== (atan (neg u)) (neg (atan u)))`), `(sqrt a)^2 == a @ a >= 0`, and
`sqrt a > 0 @ a > 0`. Each parses to the obvious tree and round-trips.

**STAGE0 S1–S3:**
`Int[x = 0 .. 1] 3*x^2 + 2*x == ?A` is
`(Int x 0 1 (add (mul 3 (pow x 2)) (mul 2 x)))`.
`Int[x = 0 .. 1] x*exp(x^2) == ?A` is `(Int x 0 1 (mul x (exp (pow x 2))))`.
`Int[x = 1 .. e_const] (ln x)/x == ?A` is `(Int x 1 e_const (div (ln x) x))`,
and prints as `ln x / x`. S3's F `(ln x)^2 / 2` is `(div (pow (ln x) 2) 2)`.
`x > 0 @ [1, e_const]` and `x # 0 @ (1, e_const)` differ in closedness.
S3's §6.8 entries `e_gt_one` (`e_const > 1`, the sign fact that lets the
range [1, e_const] be oriented) and `ln_e` (`ln e_const == 1`, needed to
close F(e_const) = 1/2) parse to `(> e_const 1)` and `(== (ln e_const) 1)`.
P1 uses neither.

**Must-refuse moves** still have to parse. `D[x] sqrt(x^2) == 1 @ x >= 0`
is `(== (D x (sqrt (pow x 2))) 1 [(>= x 0)])` and prints as
`D[x](sqrt(x^2))`. `Int[x = 0 .. 1] 1/(1 + x^3)` is a well-formed close
value; §9's whitelist is what refuses it.

## 10. Notes for the next items

- Obligation orientation: settled by `p1_expected.py` E8 (KEYING). The
  tracker does not canonicalise. Each rule mints its obligation in the
  orientation its own statement uses, so §6.8's `sqrt_sq` gives `t >= 0` and
  the key the tracker uses is `t >= 0 @ [0, pi/2]`. §11.1's `0 <= t` is
  display text only. Under D12 it is a different key, and nothing emits it.
  `sqrt`'s own definedness former (E26) owes another key again for §11.1's
  `sqrt(t^2)`: `t^2 >= 0 @ [0, pi/2]`, on its argument, charged when the
  goal is installed.
- `d_pow_int`'s literal `n` and `d_chain`'s `f'` are schema notation with no
  term syntax. They are built in code, not parsed.
- Must-refuse constructions (D17), unreachable in P1:
  (`2^x`)[x := 1], which would build `RPow(2, Num 1)`, and
  (`x^(-y)`)[y := 1], which would build `RPow(x, Neg(Num 1))`. Both are
  refused with `rpow-literal-exponent`.
