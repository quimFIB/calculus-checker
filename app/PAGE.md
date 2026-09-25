# The check-mode page — DESIGN.md §16.4, first cut

WHAT.md's next step: a thin page over the JSON API (`API.md`) that gives a
usable tool before the assistance layer exists. Written before the code.

**Check mode** is §16.4's client with the assistance taken out: the learner
chooses every move and types its arguments, and the kernel checks it. There
is no palette, no hint ladder, no progress pane and no probe, because nothing
behind them is built. Absent, not greyed out (§16.4: a greyed-out button is
an invitation to want it).

## Where it sits

```
app/page/index.html   the page: HTML, CSS and JS in one file, no framework,
                      no build step, no network beyond its own server.
app/server.py         serves it at GET / (and nothing else static).
app/api.py            gains GET /moves.
```

Untrusted, and holds nothing: every goal, report and obligation on screen is
a string from a route. The page never builds a verdict. "Proved." is shown
only as the `report` of a node.

Standard library only on the server; the page loads nothing from outside
(no CDN; KaTeX and its fonts are vendored and served by `./calc`,
UI.md), so `./calc` works offline (§16.1).

## The new route

```
GET /moves   -> {moves: [{name, args: [{name, type, term, optional}]}]}
```

The kernel's `MOVES` in order, each with its argument names as `kernel`
lists them and the loader's type for each (`str`, `dict`, `list`, `int`),
`term` true when the loader parses it as a term, and `optional` true for
`occurrence` (rewrite, int_flip, ftc, int_parts, int_improper) and for
int_subst's `mode`, `occurrence` and `f` (`f` is required once `mode` is
`reverse`, which the kernel checks). The page builds its move form from this, so a new move needs no
page change.

## The page (revision 2: rocq-mode)

*Revision 2, owner's ask (2026-09-25): "a central part where the user
inputs the tactics and then to the right some kind of status window,
similar to rocq-mode". The first cut's move form is replaced by a script
(`SCRIPT.md`); the three panes stay, reweighted.*

- **Problem** (left, narrow). The problem picker and "Your own goal" as
  before, the statement and formal goal, the parse echo, and below them
  the **attempts** tree from `/tree` (the attempt tree stays the state
  model, §16.4; retracted branches kept and struck through).
- **Script** (centre, the widest pane). A text editor holding the tactic
  script. The **checked region**, every sentence the kernel accepted, is
  shaded green and read as locked: an edit inside it first retracts back
  to the sentence being edited, as Proof General does. A sentence the
  kernel refused is underlined red until it is edited.
- **Goals** (right). The node at the end of the checked region: its
  `report`, its goal, its theorem when closed, the facts bound on its
  path, and the obligation table as before. Below it a **response** box:
  the last refusal (code, message, residual) or the last success.
- **Status line.** The report, `check mode`, and `0 machine-checked`.

Stepping, as Proof General's keys:

```
Alt+Down     check the next sentence          (button: Next)
Alt+Up       retract the last checked one      (button: Undo)
Ctrl+Enter   check or retract to the cursor    (button: To cursor)
```

Each step sends the sentence to `POST /tactic` from the node at the end of
the checked region; checked sentence k is node k of the path from n0.
Undo sends `POST /retract` on the last node. Stepping after an undo forks
the attempt tree, as the API does. Clicking a node in the attempts tree
only shows it in the goals pane; the script is the path.

The first cut's move form and `GET /moves` stay: `/moves` is still served
(the tactic syntax covers the same moves), and the form is gone from the
page.

## Revision 3: hint buttons

The recognizer (`assist/RECOGNIZER.md`) is built, so the page gains `?`,
`??` and `???` in the script toolbar: `GET /hint` rungs 1–3 on the node
at the end of the checked region, shown in the response box with the
row's cost, or its refusal (`no-integral`, `no-row`). A hint is advice,
never a step, so the status line still reads `0 machine-checked`.

## Deliberately not in this cut

KaTeX (`API.md`: no renderer yet, a wrong one is worse than none);
palette, progress, probe; persistence and export; a corpus path argument to
`./calc` (§16.1, §18 Q6); the per-step timeout.

## Done when

1. `python3.12 -m unittest discover -s app` passes, with `/moves` covered
   (every MOVES name, in order, every arg typed) and `GET /` returning the
   page as `text/html`.
2. A headless-browser test (`app/test_page.py`, Playwright against a server
   on a free port, skipped when Playwright is not installed) proves S1
   through the page by typing `ftc x^3 + x^2 by ring. close 2 by ring.` and
   stepping, and the status line reads `Proved.`; a wrong F shows
   `ftc-check-failed` in the response box and checks nothing; Undo marks
   the node `✗` in the attempts tree and keeps it; editing inside the
   checked region retracts to that sentence; and COS_SQ proves by "To
   cursor" from a script with a `rewrite ... at` sentence.
4. `app/test_script.py`: every step of every problem file round-trips
   through `SCRIPT.md`'s printer and parser, every reference proof replays
   to its loader report through `POST /tactic`, and each malformed form is
   `bad-tactic`.
3. Nothing under `kernel/` changes; the kernel suite still passes.
