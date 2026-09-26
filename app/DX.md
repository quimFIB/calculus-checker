# .dx files and the Emacs mode

The owner's ask (2026-09-26): "also can we have the html part and an
Emacs mode. Take inspiration on rocq mode. You may assume the file
extension for this is .dx". Written before the code. The page's half of
the same ask is `PRETTY.md`.

**Revised 2026-09-26: the stepping model below is replaced by a language
server (LSP.md).** The owner chose "LSP, retire REPL": `./calc --repl`,
`app/repl.py` and the stepping commands are gone. The .dx format, the
header, `POST /session {header}`, the pretty display and font lock stay as
written here. The sections that no longer hold are marked.

Untrusted, like all of `app/`. The Emacs mode is a second client of the
same API (API.md), as the page is: every verdict it shows is a string the
kernel produced.

## Where it sits

```
app/dx.py                 a .dx file's header sentence: read and print
app/lsp.py                the language server; ./calc --lsp starts it (LSP.md)
emacs/dx-mode.el          the major mode and its eglot client, Emacs 29+
emacs/test-dx-mode.el     ERT tests, run by app/test_lsp.py against ./calc --lsp
app/test_dx.py            dx.py and the sentence fixture
```

## The .dx file

A .dx file is a tactic script (SCRIPT.md: sentences, `(* comments *)`)
whose **first sentence is a header** naming the goal:

```
(* readiness S1 *)
problem stage0.S1.

ftc x^3 + x^2 by ring.
close 2.
```

or, for a goal of your own:

```
goal Int[x = 0 .. 1] f(x) == ?A functions f/1.
```

- `problem ID.` names a problem as `/problems` lists it. The id's own dots
  do not end the sentence, since a sentence ends only at a `.` followed by
  whitespace or the end.
- `goal G [functions f/1] [assuming name: J for s in I; ...].` adds Γ
  (p1_expected E147, E155): each item is a law or order judgement `J`, or
  `v in C^k` for a regularity, on `s in I` (`I` as a domain item writes
  it, `[0, oo)`). The last depth-0 `assuming` and each item's last depth-0
  `for` split. Example:
  `goal v(t) == v(0) + t @ t >= 0 functions v/1 assuming eom: D[s] v(s) == 1 for s in [0, oo); regv: v in C^1 for s in [0, oo).`
- `goal G [functions f/1, g/2].` is `/session`'s goal and functions. The
  word `functions` splits at bracket depth 0 only, as SCRIPT.md's clause
  words do.
- Anything else as the first sentence is refused `bad-header`, naming the
  two forms. Every later sentence is a tactic.

`dx.header(sentence)` returns `{"problem": id}` or `{"goal": g,
"functions": {...}}`, and `dx.show_header` prints it back;
`header(show_header(h)) == h`.

The header is sent as `POST /session {header}` (review 3), so no client
parses one.

## The REPL (`./calc --repl`): retired, see LSP.md

One JSON object per line each way, UTF-8:

```
-> {"id": 1, "method": "POST", "path": "/tactic", "body": {...}}
<- {"id": 1, "status": 200, "body": {...}}
```

It serves every API.md route through TIMEOUT.md's worker, so a step that
runs past `--step-timeout` (default 10 s) answers the usual `{"timeout"}`
body and the session comes back. `{"path": "/cancel"}` is answered at once,
even while another request runs; everything else is answered in order.
The first line it writes is `{"ready": true, "protocol": 1}`. Nothing is
saved: the .dx buffer is the learner's work, so the REPL runs with no work
directory (PERSIST.md's `WORK_DIR` None). A line that is not a JSON object
answers `{"id": null, "status": 400, "body": {"error": ...}}`. End of input
stops it.

## The Emacs mode

*The stepping model, keys and windows below are replaced by LSP.md's
eglot client; the pretty display and font lock still hold.*

Proof General's model, as the page's text mode already follows it (PAGE.md
revision 2). The buffer is the script; a **locked region** at its start is
every sentence the kernel accepted, shaded; the goals and the last response
are shown in two other windows.

**Starting.** Visiting a `.dx` file turns on `dx-mode`. The process
`dx-calc-program` (default: `calc` next to this file's repository, found
from `dx-mode.el`'s own location, else `calc` on `exec-path`) with
`dx-calc-args` (default `("--repl")`) starts on the first step, one per
buffer. Asserting the header sentence opens the session (`/session`,
`resume` false); it is the first sentence of the locked region.

**Keys** (Proof General's where it has one):

| Key | Command | Does |
|---|---|---|
| `C-c C-n`, `M-<down>` | `dx-next` | check the next sentence |
| `C-c C-u`, `M-<up>` | `dx-undo` | retract the last checked sentence |
| `C-c RET` | `dx-goto-point` | check or retract up to point |
| `C-c C-b` | `dx-goto-end` | check to the end of the buffer |
| `C-c C-r` | `dx-retract-all` | retract everything, the header too |
| `C-c C-.` | `dx-goto-locked-end` | move point to the end of the locked region |
| `C-c C-c` | `dx-interrupt` | `/cancel` the running step |
| `C-c C-a` | `dx-use-suggestion` | put the last refusal's suggestion in place of the refused sentence (STUCK.md) |
| `C-c C-t` | `dx-hint` | the next hint rung (1, 2, 3) on the current node; with a numeric prefix, that rung |
| `C-c C-l` | `dx-layout` | show the goals and response windows again |
| `C-c C-p` | `prettify-symbols-mode` | toggle the pretty display (below) |
| `C-c C-x` | `dx-exit` | stop the process; the locked region is cleared |

Stepping to point or to the end sends one sentence at a time and stops at
the first refusal or timeout. A running sentence is shaded amber; a refused
one is underlined red until it is edited; a stopped one is dashed.

**Editing the locked region** retracts to the sentence being edited before
the edit happens, as the page's text mode does. While a request runs, an
edit there is refused with "busy: wait, or C-c C-c".

**The goals window** (`*dx-goals*`) shows the current node's report, its
goal, its theorem when closed, the facts, and the obligations one per line
with status and method, all as the API sends them. **The response window**
(`*dx-response*`) shows the last success, refusal (code, message,
residual, the stuck explanation and its suggestion) or hint.

**Pretty display.** `dx-pretty-mode` (on by default, `dx-pretty` to
change) is `prettify-symbols-mode` with a table for the grammar: `Int` ∫,
`sqrt` √, `pi` π, `oo` ∞, `<=` ≤, `>=` ≥, `==` ≐, `:=` ≔, `*` ·, `->` →,
`/\` ∧, and the spelled Greek letters. It changes only what is drawn: the
buffer's text, what is saved and what is sent are the plain grammar, and
the symbol under point is shown unprettified
(`prettify-symbols-unprettify-at-point`). It applies to the goals and
response windows too. Emacs has no 2D fraction boxes; those are the
page's (PRETTY.md).

Font lock: the moves, the header words, the clause words, `ring` and
`field`, entry names after `rewrite` and `fact`, and comments.

## Done when

1. `app/test_dx.py`: `header` reads both forms and refuses others, round
   trips through `show_header`; the REPL answers `ready`, proves S1 by
   `/session` and `/tactic`, answers a bad line with 400, and a `/cancel`
   stops a slow step with the `timeout` body while the REPL keeps serving.
2. `emacs/test-dx-mode.el`, run by `test_dx.py` when `emacs` is on the
   PATH (skipped otherwise): a .dx for S1 is checked to the end and the
   goals buffer says `Proved.`; a wrong `ftc` is refused, marked, and its
   suggestion applied with `dx-use-suggestion` then checks; an edit in
   the locked region retracts; `dx-undo` and `dx-goto-point` move the
   locked region; P3_LOWER proves from its reference proof; a `goal`
   header with `functions` opens a session.
3. `app/sentences.json`'s cases pass in all three splitters.
4. Nothing under `kernel/` changes; the kernel suite still passes.

## Review (2026-09-26), folded in before the code

1. **Page Save/Open .dx is cut**, with `/dxheader`. Export and Import
   already move work in and out of the page, and a rebuilt header would
   drop the file's preamble comments. Emacs is the .dx client.
2. **Locked region, both clients.** An edit in the locked region shrinks
   it at once, locally, to the sentences before the edited one, and the
   `/retract` goes out afterwards; the next step's parent is the local
   path, so nothing waits. An insertion that does not start with
   whitespace right after the last checked `.` counts as an edit of that
   sentence (`close 2.` + `5`). While a request runs, the locked and
   queued text carry the `read-only` text property, so no change hook
   ever signals (a signal there would switch the hook off). `undo` and
   `yank` go through the same path and are tested.
3. **The header.** It is sent as `POST /session {header}` (new: the API
   reads the header with `dx.header`, so neither client parses one);
   `bad-header` joins API.md's refusal codes. Retracting the header drops
   the session on the client (the API refuses `/retract` of n0). A 400
   (an unknown problem id) is shown in the response window with its code,
   as a refusal is, and the header is not locked. `functions` splits at
   the last depth-0 occurrence of the word.
4. **One sentence rule, three splitters.** `app/sentences.json` holds
   cases (comments, `..`, `1.5`, ids with dots, trailing text, non-ASCII
   space); `script.next_sentence`, the page's `nextSentence` and
   `dx-mode`'s splitter are each tested against it. The mode's syntax
   table does not nest comments, as the Python and JS splitters do not.
5. **The REPL.** GET bodies are the query as strings (`"rung": "2"`).
   A reader thread takes stdin; `/cancel` is answered at once, and with
   `{"id": N}` it stops only request N (without, whatever runs); the
   `/cancel` answer can precede the stopped request's own answer. Writes
   to stdout take a lock. `--repl` runs with no work directory whatever
   `--work` says. `/layout`, `/untex` and `/parse` are answered by the
   REPL process itself, never queued behind a step.
6. **Emacs 28 or later** (`json-parse-string` without jansson is 28+;
   tested on 29). The process filter keeps partial lines, and skips the
   `ready` line.
7. **Keys.** The hint is `C-c C-t` (a tip; `C-c C-h` would hide the
   prefix help). The pretty display is `prettify-symbols-mode` itself,
   toggled by `C-c C-p`; `*` is not prettified (it would draw the `(*`
   of comments as `(·`).
