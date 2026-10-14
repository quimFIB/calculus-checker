# Auto-simpl: the app finishes a constant goal (E162)

Written before the code (2026-10-14). The owner asked to "allow the kernel
to simpl, but make it easily toggleable, so a user wanting to actually see
all the steps can turn it off, but a more experienced user can just let the
kernel take care of automatic things". Settled the same day:

- **Scope:** arithmetic and the evaluation entries, never a technique.
- **Trigger:** a move that leaves a constants-only goal with `?A`.
- **Toggle:** a script sentence, on by default.

It is DESIGN.md §2's *auto* mode, applied to the last step of a
computation. Like everything §2 describes, **it is not the kernel**.
`app/autosimpl.py` is untrusted and proposes ordinary kernel moves
(`rewrite`, `fact`, `close`), and the kernel checks each one exactly as it
checks a typed move. A bug here can propose a wrong move, which the kernel
refuses, or stop early. It cannot produce a theorem the kernel did not
check, and it cannot add an admission (see "All or nothing" below).

**It makes the moves E27 would name, in E27's order.** With the setting
off, a learner who keeps closing sees exactly these moves named, one
refusal at a time. So turning it off shows the same steps. It does not
show different ones.

## The setting

- **Sentences.** `Set Auto Simpl.` and `Unset Auto Simpl.` (SCRIPT.md).
  Each parses to the move `set` with args `{"auto_simpl": true|false}`.
- **Not a kernel move.** The session records a node whose state is its
  parent's, with no kernel call. The node carries the setting, and every
  node inherits its parent's. Retracting the sentence retracts the node,
  so the setting reverts with it. Setting the value already in force is
  accepted and changes nothing.
- **Defaults.** The installed goal's node (`n0`) has the setting **on**.
- **Not a rule.** The status line's rule count (`steps`) does not count
  `set` nodes.
- **Work documents (PERSIST.md).** A document saves `"auto_simpl"` at its
  top level: the setting at `n0`, which is `true` for every session made
  since E162. A document **without** the field predates E162 and replays
  with the setting off at `n0`. So every saved proof replays exactly as it
  was made, including one with a typed `simpl.` after `ftc`. The format
  version stays 1: fields beyond the format's were always ignored.

## When it runs

**After a move.** After the kernel accepts a move from a node where the
setting is on, the chain runs from the new state when all of these hold:

1. the move changed the goal, so a `fact` (which leaves the goal alone)
   never triggers it;
2. the new goal is open, and its right side is `?A`;
3. its left side holds no `Integral`, `Deriv`, variable or declared
   function. This is `simpl`'s own test (`fill.py`).

**Never** at install, never after a `set` node, and never on a goal
without `?A` (order goals, `verify`).

**A typed `simpl.`** With the setting **on**, it runs the same chain from
its own node, with no move before it, and the node records the move
`simpl` (not `close`). Facts it names with `using h` are added to the
chain's `close`, which is then `by field`. If the chain cannot close, the
sentence is refused `simpl-stopped` with the reason, and adds nothing.
With the setting **off**, `simpl.` is E161's, unchanged: the arithmetic,
then a typed `close` that E27 checks.

**For clients.** `POST /session` takes `auto_simpl: false` to install
with the setting off at `n0`, for clients that replay moves by hand (the
test suites, the gate's replays). It is the same setting a pre-E162
document gets. **EVAL's Insert** (EVAL.md) leaves out the moves after the
one whose chain closes the goal at that node, since with the setting on
they would be refused `proof-finished`.

## The chain

The chain is three phases, each made of kernel steps fed exactly as typed
steps are (`loader.step_args`, then `kernel.step`).

**1. Rewrites, on the goal.** Repeat: take the first redex in the goal's
left side that E27 (a) counts and that a rewrite can take. The order is
E27's: pre-order, and at each node the entries in ENTRIES order, then
`rpow_int`. Rewrite it at that subterm, with:

| Entry | Inst |
|---|---|
| an exact value (no schema) | none |
| `sqrt_sq` at `sqrt b` | u := c, the square root of b's ring normal form, then u := −c if c is refused or adds an admission |
| `atan_odd`, `sin_odd`, `cos_even` at `f(b)` | u := the normal form of −b |
| `rpow_int` at `RPow(b, e)` | u := b, n := the integer e normalises to (E163) |
| any other schema entry | the structural match's bindings (`pyth`, `exp_ln`, `exp_neg`, `sqrt_sq_val` at exactly `(sqrt b)^2`) |

A redex E27 counts with no row here, such as `(sqrt 2)^3`, is skipped by
this phase and left for phase 2.

**2. Facts, on the value.** Let v be the goal's left side as `simpl`
computes it, reduced by the facts minted so far (field's fact reduction).
Repeat while E27 (a) names a redex in v that field can use as a fact:

| E27 names | Fact minted |
|---|---|
| `sqrt_sq_val` at `(sqrt b)^n` | `fact autoK := sqrt_sq_val with a := b` |
| `pyth` at `(sin b)^2 + (cos b)^2` | `fact autoK := pyth_cos with u := b` |

These are the redexes that appear only once the arithmetic is done.
`sqrt 2 * sqrt 2` becomes `(sqrt 2)^2`, and a `pyth` sum split across a
longer sum comes together, but the goal has no such subterm for a rewrite
to target. `autoK` is `auto1`, `auto2`, and so on, each the first such
name not already bound on the path.

**3. Close.** `close v by ring`. It is `by field` instead when facts were
minted, `using` them, or when a denominator stays, as for `simpl`.

**Bounds.** At most 32 rewrites and 8 facts. Past either, the chain stops
with "gave up". Any exception inside the chain (the normaliser's
`power-too-large`, say) stops it too, so the move before it stands (E164).

### All or nothing

The chain **stops** on:
- a refused step (the kernel's code and message);
- a step that leaves the state with more admitted obligations than the
  state it started from;
- an E27 (a) redex in v that phase 2 cannot turn into a fact;
- E27 (b).

Then nothing from the chain is kept: the node is the move's own, with
`auto_stopped` saying why. The goal is exactly where the move left it, and
the learner carries on by hand. The admission guard is not decoration.
`sqrt((pi - 4)^2)` with u := pi − 4 is *accepted* by the kernel modulo the
admitted, and false, `pi - 4 >= 0`. The chain must never take an
admission the learner did not choose, so it tries the other sign and then
stops.

## Record and display

- **Node.** A node gains `auto_simpl` (the setting after it), `auto` (the
  chain's steps as `(move, args)` in problem-file shapes, or none) and
  `auto_stopped` (a message, or none). Its state is the state after the
  chain. Its `move` and `args` stay the learner's, so `checked_prefix`
  still matches the script sentence by sentence.
- **Work document.** Each node saves `"auto": [{"move", "args"}, ...]` and
  `"auto_stopped"` when they are set. Replay applies the recorded steps
  after the move, **never recomputing them**, and holds them to the rules
  a live chain keeps (E164): only `rewrite`, `fact` and `close`; no
  admission added; the goal closed at the end; a chain only where the
  setting is on and the trigger holds; a `simpl` node never without one.
  A chain that breaks any of these, or no longer replays, drops its node
  with code `auto-replay`, as a refused move is dropped. So a work file
  cannot put a chain on the page that auto-simpl would not have run.
- **API.** `render` adds:
  - `auto_simpl`: true or false;
  - `auto`: the steps as script sentences (`script.show`);
  - `auto_stopped`: a message or null.
- **Page.** Under the goal or theorem, an "Auto-simpl" label lists the
  sentences in monospace, or shows "Auto-simpl stopped: …". The status
  line shows `auto-simpl on` or `auto-simpl off` after `assisted`.
- **Emacs.** The goals buffer shows the same lines (`dx-mode.el`), and
  `Set` and `Unset` are highlighted as moves.
- **A sentence after the goal was closed.** The kernel refuses it
  `proof-finished`, as before; so is a `Set`, `Unset` or `simpl`
  sentence there (E164). When auto-simpl closed the goal after a move
  (not a typed `simpl`), the message adds: "auto-simpl closed this goal after the previous move; put
  `Unset Auto Simpl.` before that move to make these moves yourself".

## Limits, stated

- **Relative to the entries in force,** as E27 is: `ln 2 + ln 3`,
  `sqrt 8` and `sqrt 2 * sqrt 3 * sqrt 6` close as they stand, because no
  entry reduces them.
- **Phase 2 knows two facts.** A value-side redex of any other entry
  stops the chain.
- **Never a technique.** It never runs `ftc`, a substitution or a hint.
  The hint ladder (§2) and the gate's rung measure (GATE.md) are untouched.

## Cases

`test_autosimpl.py` encodes these, sentence for sentence. Each starts from
the goal with the setting on, unless the script says otherwise.

| # | Goal | Script | `auto` | Outcome |
|---|---|---|---|---|
| 1 | `Int[x = 0 .. 1] x*exp(x^2) == ?A` (S2) | `ftc exp(x^2)/2 by ring.` | `rewrite exp_one at exp(1^2).` `rewrite exp_zero at exp(0^2).` `close (1/2)*e_const - 1/2 by ring.` | Proved. |
| 2 | `Int[x = 0 .. 1] 3*x^2 + 2*x == ?A` (S1) | `ftc x^3 + x^2 by ring.` | `close 2 by ring.` | Proved. |
| 3 | `Int[x = 1 .. e_const] (ln x)/x == ?A` (S3) | `ftc (ln x)^2/2 by ring.` | `rewrite ln_e at ln e_const.` `rewrite ln_one at ln 1.` `close 1/2 by ring.` | Proved. |
| 4 | `sqrt(2 + 2) + sqrt(0 + 1) + atan(-1/2) == ?A` | `simpl.` | `rewrite sqrt_sq with u := 2 at sqrt(2 + 2).` `rewrite sqrt_sq with u := 1 at sqrt(0 + 1).` `rewrite atan_odd with u := 1/2 at atan(-1/2).` `close -atan(1/2) + 3 by ring.` | Proved. |
| 5 | `exp(ln 2) + (sqrt 3)^2 + (sin 1)^2 + (cos 1)^2 == ?A` | `simpl.` | `rewrite exp_ln with u := 2 at exp(ln 2).` `rewrite sqrt_sq_val with a := 3 at (sqrt 3)^2.` `fact auto1 := pyth_cos with u := 1.` `close 6 by field using auto1.` | Proved. |
| 6 | `sqrt 2 * sqrt 2 == ?A` | `simpl.` | `fact auto1 := sqrt_sq_val with a := 2.` `close 2 by field using auto1.` | Proved. |
| 7 | `2^(1/2 + 1/2) == ?A` | `simpl.` | `rewrite rpow_int with u := 2; n := 1 at 2^(1/2 + 1/2).` `close 2 by ring.` | Proved. |
| 8 | `sqrt((pi - 4)^2) == ?A` | `simpl.` | none | stopped, both signs adding an admission; the goal is unchanged |
| 9 | S2 | `Unset Auto Simpl.` `ftc exp(x^2)/2 by ring.` | none | goal `exp(1^2)/2 - exp(0^2)/2 == ?A` |
| 10 | S2 | case 9, then `simpl.` | none | refused `close-not-evaluated`, naming `exp_one` (E161) |
| 11 | S2 | case 1, then `simpl.` | none | refused `proof-finished`, with the hint above |
| 12 | S2 | `Unset Auto Simpl.` `Set Auto Simpl.` `ftc exp(x^2)/2 by ring.` | as case 1 | Proved. |
| 13 | lesson 6's goal | `fact h := sqrt_sq_val with a := x + 1.` `ftc (2/3)*(x + 1)*sqrt(x + 1) by field using h.` | `rewrite sqrt_sq with u := 1 at sqrt(0 + 1).` `close (4/3)*sqrt 2 - 2/3 by ring.` | Proved; the `fact` triggers nothing |
| 14 | S2, as a work document saved before E162 (no `auto_simpl` field) | lesson 2's script: `ftc`, two rewrites, `simpl.` | none | replays with the setting off, every node under its own id, to Proved. |
