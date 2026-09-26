# Classify a force: F(t), F(v), F(x) or none (DESIGN.md §12.1)

UNIT00.md G5, written before the code. Unit 00's first habit is "classify
the force before starting" (P1, and the sheet's preamble). §12.1 names
`classify`, decided by the free variables of the right-hand side, and §5.2
makes it a tactic report, not a judgement: nothing the kernel proves
depends on it. So it is untrusted, in `app/assist/classify.py`, like the
recognizer.

## What it reads

A force term F (GRAMMAR.md syntax, parsed by the kernel's parser, which
only reads) and the names of the three state variables, by default `t`
(time), `v` (velocity, ẋ) and `x` (position). Every other free variable is
a parameter. Declared functions may be given, as elsewhere.

## What it answers

- **F(t)**, **F(v)** or **F(x)** when exactly one state variable is free
  in F, with the first reduction the unit's rung 3 names: integrate once
  (F(t)); separate, t = ∫ m dw/F(w) (F(v)); multiply by ẋ, ½mẋ² + U(x) = E
  with U′ = −F (F(x)).
- **none** when two or three are free, naming them. For each parameter p,
  it tries p := 0 and reports the parameters whose zeroing leaves exactly
  one state variable, with the case that results: (d)'s "b = 0 restores
  F(x); κ = 0 gives F(v)", (e)'s "ε = 0". A variable counts as gone when
  F with it shifted by 1 minus F is `ring`-zero (the kernel's `ring`,
  used as a normaliser only).
- **constant** when none is free: every case applies, and F(t) is the
  shortest.

## Where it shows

`POST /classify {force, t?, v?, x?, functions?}` returns `{case,
free, reduction, why, repairs}`; a malformed term is refused
`bad-term` with the parser's message. The page has a **Classify** scratch
box beside the evaluate box. The server answers the route itself, outside
the worker, as it does `/untex` (nothing in it touches a session).

## Tests

`app/assist/test_classify.py`: unit 00 P1's five equations give F(v),
F(x), F(t), none (b, κ repair) and none (ε repair); a constant; custom
variable names; a refusal. The route through the server.
