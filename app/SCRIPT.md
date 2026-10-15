# The tactic script — the page's text syntax for moves

The owner asked for the page to work like rocq-mode (Proof General): the
learner types a script of tactics in the centre, steps through it, and a
status pane on the right shows the goal. This file is the script's syntax.
Written before the code.

`app/script.py` parses one tactic into the kernel's `(move, args)`, exactly
the problem-file shapes (ARCHITECTURE.md §9), and prints `(move, args)` back
as a tactic. It is untrusted, like the rest of `app/`: a parsing bug sends
the kernel the wrong move, which the kernel checks like any other.

## Sentences

A script is a sequence of **sentences**, each ended by a `.` that is
followed by whitespace or the end of the text (so `..` and `1.5` never end
one). Everything between `(*` and `*)` is a comment, as in Rocq. Blank text
between sentences is ignored.

## Tactics

One per sentence. `T` is a GRAMMAR.md term, `N` a natural number, `h` a
fact name, `E` an entry name. `[...]` is optional.

```
ftc T [occurrence N] [by C] [using h, ...].
int_improper T [occurrence N] [by C] [using h, ...].
close T [by C] [using h, ...].
simpl [by C] [using h, ...].
rewrite E [with x := T; ...] at T [occurrence N].
fact h := E [with x := T; ...].
int_subst x := T as y from T to T [reverse T] [occurrence N] [by C] [using h, ...].
int_flip [occurrence N].
cint_param [occurrence N].
residues [in C, ...] [occurrence N].
int_parts in x with u := T; v := T [occurrence N] [by C] [using h, ...].
taylor_lagrange h := lower|upper of T in u from T to T at T derivs T; T; ... [strictly] increasing|decreasing [by C] [using h, ...].
bound [scale T] [by C] using h, ....
verify [by C] [using h, ...].
quad_t h := L from T to T in u antiderivative T [regs r, ...] [by C] [using h, ...].
sep_autonomous h := L from T to T in u rate T antiderivative T range I [regs r, ...] [given a, ...] [by C] [using h, ...].
energy_integral h := L kinematic k from T to T in u rate T antiderivative T range I [regs r, ...] [given a, ...] [by C] [using h, ...].
Set Auto Simpl.
Unset Auto Simpl.
```

- `Set Auto Simpl.` and `Unset Auto Simpl.` (p1_expected E162,
  AUTOSIMPL.md) turn auto-simpl on and off from that point of the
  script. They parse to the move `set` with args `{"auto_simpl": true}`
  or `false`. That is not a kernel move: the session records a node with
  its parent's state and the new setting. It is on when a goal is
  installed. While it is on, a move that leaves a goal of constants with
  `?A` is followed by the chain AUTOSIMPL.md specifies (the evaluation
  rewrites E27 would name, then `simpl`'s close), each step checked by
  the kernel, and `simpl.` runs that same chain. The words are matched
  exactly, capitals included, as Rocq's `Set`/`Unset` options are.

- The three ODE rules (p1_expected E149–E153) read Γ, the assumptions
  the goal was installed under (DX.md's `assuming`). `L` names the law,
  `kinematic k` energy's x' = v, `regs` the C^1 assumptions, `given` the
  order assumptions that keep y(s) in `range` (an open interval `(a, b)`,
  either end `oo`). `rate` is f in u, `antiderivative` F with F' = c/f
  (sep), f (energy) or R/c (quad_t). Each mints the handle `h`; `verify
  ... using h` then closes the goal.

- `taylor_lagrange` (p1_expected E97) mints the handle `h` for the lower or
  upper bound of the Taylor remainder of `of T` in the new variable `u`,
  expanded at `from`, on [from, to), read at the point `at`; `derivs` lists
  the derivatives D_1 .. D_m, `;`-separated, and exactly one of
  `increasing` or `decreasing` says the sign of the last; `strictly`
  before it (E138) asks the sign strictly and mints a strict bound. `bound`
  (E99) closes an order goal from the one order fact among `using`;
  `scale T` (E139) multiplies the fact by T, which it owes positive.
  Inside these two moves `strictly` and `scale` are clause words, so a
  handle or variable cannot be named either (E141).

- `verify` (p1_expected E112–E114, §6.5's `ode_verify`) closes an
  equation with no `?A`: each `D[x] e` is differentiated by the rule
  table, then `by C` checks the two sides agree. A candidate solution is
  checked against its equation of motion this way, and an initial
  condition is the same move on a goal with no `D`.

- `simpl` is `close T` with T computed (app/fill.py, untrusted;
  p1_expected E161): when the goal's left side is only constants (no
  integral, derivative, variable or declared function), T is that side
  in field's normal form, which does the literal arithmetic, inside a
  function's argument too (`sqrt(1 + 1)` becomes `sqrt 2`), and collects
  like terms and nothing else, and `by C` becomes `by field` when a
  denominator stays, at the top or inside an argument. The kernel then checks it as a typed `close T`, so
  E27 still refuses a value with an entry left to apply (`exp 1`) and
  names the entry. On anything else the sentence is `bad-tactic`. It is
  not a kernel move: the node records `close` with the computed T.
  Unlike Rocq's `simpl` it finishes the goal, since naming ?A is the
  only thing left to do once the goal is constants. This is `simpl`
  with auto-simpl off. With it on (the default), `simpl.` is the move
  `simpl` and runs AUTOSIMPL.md's chain, which also makes the
  evaluation rewrites; the node records `simpl`, not `close`.
- `by C` is `by ring` or `by field`. Omitted, it is `by ring`.
- `using h, ...` lists fact names bound earlier on the path; omitted, none.
- `with` lists an entry's schema instantiation, `;`-separated; omitted, it
  is empty. int_parts' `with` names exactly `u` and `v`.
- int_subst's `reverse T` is reverse mode with `f := T`; without it the
  mode is left out (forward).
- The words `by`, `using`, `with`, `at`, `occurrence`, `as`, `from`, `to`,
  `reverse`, `in`, `derivs`, `increasing`, `decreasing`, `strictly`, `scale`,
  `kinematic`, `rate`, `antiderivative`, `range`, `regs` and `given` are split on only at bracket depth 0 and only where
  the tactic's form has that clause, so `sin(at)` stays a term; a variable
  named like a clause word cannot follow that clause's position unbracketed.

A sentence that does not fit its form is refused `bad-tactic`, with a
message naming what was expected; an unknown first word is `bad-tactic`
naming the moves.

## Printing

`show(move, args)` prints the canonical form above: every clause the args
carry, `by C` always, `using` only when there are facts, `with` only when
the instantiation is non-empty. `parse(show(m, a)) == (m, a)` for every
step of every problem file (with `check` and `facts` always present, as
the files have them).

## The route

```
POST /tactic  {session, node, text}   -> the new node | refusal
```

Parses `text` as one sentence (the trailing `.` optional) and feeds it as
`/step` does. A parse failure is a refusal `bad-tactic` and adds no node.
