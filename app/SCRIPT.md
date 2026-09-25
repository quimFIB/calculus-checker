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
rewrite E [with x := T; ...] at T [occurrence N].
fact h := E [with x := T; ...].
int_subst x := T as y from T to T [reverse T] [occurrence N] [by C] [using h, ...].
int_flip [occurrence N].
int_parts in x with u := T; v := T [occurrence N] [by C] [using h, ...].
taylor_lagrange h := lower|upper of T in u from T to T at T derivs T; T; ... increasing|decreasing [by C] [using h, ...].
bound [by C] using h, ....
```

- `taylor_lagrange` (p1_expected E97) mints the handle `h` for the lower or
  upper bound of the Taylor remainder of `of T` in the new variable `u`,
  expanded at `from`, on [from, to), read at the point `at`; `derivs` lists
  the derivatives D_1 .. D_m, `;`-separated, and exactly one of
  `increasing` or `decreasing` says the sign of the last. `bound` (E99)
  closes an order goal from the one order fact among `using`.

- `by C` is `by ring` or `by field`. Omitted, it is `by ring`.
- `using h, ...` lists fact names bound earlier on the path; omitted, none.
- `with` lists an entry's schema instantiation, `;`-separated; omitted, it
  is empty. int_parts' `with` names exactly `u` and `v`.
- int_subst's `reverse T` is reverse mode with `f := T`; without it the
  mode is left out (forward).
- The words `by`, `using`, `with`, `at`, `occurrence`, `as`, `from`, `to`,
  `reverse`, `in`, `derivs`, `increasing` and `decreasing` are split on only at bracket depth 0 and only where
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
