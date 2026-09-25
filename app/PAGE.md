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
(no CDN, no fonts), so `./calc` works offline (§16.1).

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

## The page

Three panes and a move strip, as §16.4 draws them:

- **Problem** (left). A picker listing `/problems` plus a "Your own goal"
  field (goal text, optional functions as `name/arity` pairs). Starting one
  calls `POST /session`. Then the problem's title and statement, and the
  formal goal as text. A parse echo box: type a term, see `/parse`'s `show`
  of it, or its refusal.
- **Attempts** (middle). `/tree` as a tree: each node's summary and a mark,
  `✓` proved, `✗` retracted (kept, struck through), `·` open. Clicking a node
  selects it. Stepping from a node that has children forks, as the API does.
- **State** (right). The selected node's `report` on top, its goal, its
  theorem when closed, the handles bound on its path, and the obligation
  table: key, status, method and cites, sources, reason; rows the step added
  (`new`) are marked.
- **Move strip** (bottom). A move picker from `/moves`; one input per
  argument (term arguments as text, `inst` as `name := term` lines, `facts`
  as a multi-select of the node's handles, `check` as ring/field). "Check"
  sends `POST /step` from the selected node. A refusal is shown in the
  strip with its code, message and residual, and adds nothing. "Retract"
  sends `POST /retract` on the selected node and selects the parent.
- **Status line.** The selected node's report, and `0 machine-checked`
  (§16.4, §14), always.

Keys: `Ctrl+Enter` checks, `Alt+↑` retracts, `Alt+←`/`Alt+→` move the
selection to the parent or the newest child.

## Deliberately not in this cut

KaTeX (`API.md`: no renderer yet, a wrong one is worse than none); hints,
palette, progress, probe; persistence and export; a corpus path argument to
`./calc` (§16.1, §18 Q6); the per-step timeout.

## Done when

1. `python3.12 -m unittest discover -s app` passes, with `/moves` covered
   (every MOVES name, in order, every arg typed) and `GET /` returning the
   page as `text/html`.
2. A headless-browser test (`app/test_page.py`, Playwright against a server
   on a free port, skipped when Playwright is not installed) proves S1
   through the page: pick the problem, `ftc` with F := x^3 + x^2, `close`
   with 2, and the status line reads `Proved.`; a wrong F shows
   `ftc-check-failed` and adds no node; retracting marks the node `✗` and
   keeps it.
3. Nothing under `kernel/` changes; the kernel suite still passes.
