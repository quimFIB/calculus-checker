# The gate report — DESIGN.md §17

Written before the code (2026-09-26, the owner's "go ahead" on the gate
plan; UNIT00.md). §17's gate is the project's falsifier:

> After stage 1, work readiness P1–P5 and unit 00's quadrature cases in
> order, and plot the maximum rung reached per problem against time.
> *If the average rung over the last third of the corpus is not below the
> average over the first third, the tool is a crutch rather than a
> trainer and §1's central claim has failed.*

and two riders: **which rung gets used most**, and **the recognizer must
fire**: "problems where no row fired are reported separately rather than
averaged in". This file fixes the corpus, its order and the arithmetic
before any of it is read, so the reading cannot be tuned to the result.

## The corpus, in order

The order is the sheet's order, then the unit's, lettered part by
lettered part. It is the order to work them in, and "time" in the plot
is this order (the work file's `saved` stamp is shown beside it, as
information only: a problem revisited later would otherwise move).

| # | Problem | Part |
|---|---|---|
| 1 | `parts.P1_PARTS` | readiness P1(1) |
| 2 | `readiness.P1_2` | readiness P1(2) |
| 3 | `improper.P2` | readiness P2 |
| 4 | `taylor.P3_LOWER` | readiness P3 part 1, lower |
| 5 | `taylor.P3_UPPER` | readiness P3 part 1, upper |
| 6 | `improper.P5` | readiness P5 |
| 7 | `unit00.P1C_REDUCE` | unit 00 P1(c) |
| 8 | `unit00.P3A_SEPARATE` | unit 00 P3(a) |
| 9 | `unit00.P3A_V_ODE` | |
| 10 | `unit00.P3A_V_INIT` | |
| 11 | `unit00.P3A_TOP` | |
| 12 | `unit00.P3A_HEIGHT` | |
| 13 | `unit00.P4A_SEPARATE` | unit 00 P4(a) |
| 14 | `unit00.P4A_V_ODE` | |
| 15 | `unit00.P4A_V_INIT` | |
| 16 | `unit00.P4A_X` | |
| 17 | `unit00.P9A_V` | unit 00 P9(a) |

**Listed, not in the reading:** readiness P4 (series, §6.7, stage 2),
P3 parts 2–3 (stage 2), unit 00 P1(a), (b), (d), (e) (a classification,
worked in the Classify box, which records no rung; CLASSIFY.md), and the
unit 00 parts UNIT00.md marks out.

## Per problem

- **worked**: a work file `DIR/<id>.json` exists (PERSIST.md), else "not
  worked".
- **max rung**: the file's `max_rung`, 0 to 3.
- **proved**: the file replays (`work.replay`) and the last node of its
  checked path reads `Proved.` or `Proved modulo N admissions`; else
  "open".
- **fires**: the recognizer's `ladder` on the goal's first Int (as `GET
  /hint` reads it) names a row; the row is shown. A goal with no Int (an
  order goal, a verify goal) does not fire.

## The recognizer on the gate's own corpus

§17: "the recognizer's held-out score on the gate's own corpus is measured
before the gate is read". `app/assist/gate_labels.json` labels each
firing problem's first integral with the technique the course's own hints
and worked solution use, one family from RECOGNIZER.md's vocabulary,
written by a separate agent that did not read the recognizer, and
committed before the gate is read. The report scores it as `score.py`
does: **strict** when the first row's family is the label, **lenient**
when it is the label or one of `also`, **wrong** or **silent** otherwise.
It is never used to write or tune a row.

## The reading

Over the problems that are worked **and** fire, in corpus order, with n
of them: first third = the first ⌊n/3⌋, last third = the last ⌊n/3⌋.
The verdict is

- **not enough data** when n < 6 (two per third at least);
- **passes** when the last third's mean max rung is strictly below the
  first third's;
- **fails** otherwise, and the report quotes §17's sentence.

Then the rung histogram (how many worked problems stopped at 0, 1, 2, 3),
and the worked problems that do not fire, listed with their max rung and
never averaged in. Nothing here judges a proof: every "proved" is the
kernel's report on replay.

## Where

`python3 app/gate.py [DIR]` (DIR defaults to `calc-work`, as `./calc`'s)
prints the report; `--json` prints it as one object. `app/test_gate.py`
builds work files in a temporary directory: a passing run, a failing run,
too little data, a problem with no row kept out of the mean, and a file
that does not replay.
