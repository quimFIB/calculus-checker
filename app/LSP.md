# The .dx language server — `./calc --lsp`

The owner (2026-09-26), after the stepping Emacs mode (DX.md) was built:
"maybe for emacs would be better to have an LSP server like rocq-mode".
Written before the code. It replaces DX.md's stepping model; the .dx
format, the header and `POST /session {header}` stay.

Untrusted, like all of `app/`. The server is a second client of the API
(after the page): every verdict it reports is a string the
kernel produced.

## Where it sits

```
app/lsp.py              JSON-RPC 2.0 over stdio, stdlib only; the checker
app/test_lsp.py         the protocol end to end, and the ERT suite
./calc --lsp            starts it
emacs/dx-mode.el        now a thin eglot client: the mode, eglot's server
                        entry, the goals window, the checked-region shading
```

## The model: the whole document, checked incrementally

As coq-lsp does, the server checks the document, not a stepped prefix.
For each open `.dx` document it keeps the **checked prefix**: the header's
session and, for each sentence k after it, the sentence's text and the
node the kernel returned. On every change:

1. Split the new text (`script.spans`) and read the header.
2. If the header's text changed, start a new session (`/session
   {header}`) and check from the first tactic; else find the first
   sentence whose text differs from the checked prefix.
3. Step each later sentence (`/tactic`) from the node before it. Stepping
   from a node that already has children forks (API.md), so nothing is
   retracted; old branches stay in the session, unused.
4. Stop at the first refusal or timeout. The sentences after it are not
   checked, and are reported as such.

Checking runs on one thread, behind a 250 ms debounce. A change that
arrives while a sentence is being checked cancels it (TIMEOUT.md's
worker, `/cancel`), and checking restarts from the new text. A cancelled
sentence is not reported as refused.

## Protocol

Standard LSP 3.17 over stdio (`Content-Length` framing). Positions use
UTF-16 code units, as the protocol requires, converted at the edge.

| Message | What it does |
|---|---|
| `initialize` | capabilities: full text sync, completion, code actions |
| `textDocument/didOpen`, `didChange`, `didClose` | check, as above; close drops the document |
| `textDocument/publishDiagnostics` (sent) | one per refused or stopped sentence: Error for a refusal (`code: message`, then the residual and the stuck headline and lines), Warning for a timeout, and one Information "not checked: an earlier sentence was refused" spanning the rest |
| `textDocument/completion` | at a word start: each move's template (PRETTY.md) as a snippet, `_` holes as tab stops |
| `textDocument/codeAction` | on a refused sentence with a suggestion (STUCK.md): "Use this", an edit replacing the sentence |
| `dx/goals` (request) | `{textDocument, position}` -> the rendered node (API.md) after the last checked sentence ending at or before the position, with `checked: bool` false when the position is past the checked prefix, or `null` before the header is checked |
| `dx/progress` (sent) | `{uri, version, checked: Range[], running: Range \| null}` after every sentence: the checked sentences' ranges and the one being checked, for shading |
| `shutdown`, `exit` | as the protocol says; the worker is stopped |

A header that is refused (`bad-header`) or an unknown problem id is an
Error diagnostic on the header, and nothing else is checked.

## Emacs

`dx-mode` stays the major mode (font lock, comments, `prettify-symbols`
from DX.md) and adds:

- `eglot-server-programs` entry `(dx-mode . ("<repo>/calc" "--lsp"))`;
  `M-x eglot` (or `dx-eglot-auto`, default t) connects;
- the checked prefix shaded from `dx/progress` (a light green overlay, the
  running sentence amber);
- a `*dx-goals*` window showing `dx/goals` at point, refreshed when point
  stops for 0.2 s and after each `dx/progress`;
- a `*dx-response*` window with the full message of a refusal on point's
  line (the stuck explanation and its suggestion), and hints;
- diagnostics, completion and the "Use this" code action are
  eglot's own (flymake, eldoc, completion-at-point, `eglot-code-actions`).

Keys: `C-c C-l` shows the goals window, `C-c C-t` asks the next hint rung
for the node at point (`GET /hint` through a `dx/hint` request with the
same position rule as `dx/goals`), `C-c C-p` toggles the pretty display.
The stepping commands, `./calc --repl` and `app/repl.py` are removed, with
their tests: the owner chose "LSP, retire REPL" (2026-09-26). `C-c C-a`
runs the quickfix code action, and `C-c TAB` still completes a move name
into its template without the server.

## Done when

1. `app/test_lsp.py` drives `./calc --lsp` over stdio: S1 opens and checks
   to Proved (`dx/goals` at the end reports `Proved.`); a wrong `ftc`
   gives one Error diagnostic on that sentence and an Information after
   it, its code action's edit makes a document that checks; an edit in the
   middle re-checks from that sentence only (counted: the sentences before
   it are not re-sent); an edit during a slow sentence cancels it and the
   final diagnostics match the final text; completion offers the ten
   templates; positions after a non-ASCII character are right (UTF-16);
   P3_LOWER checks to Proved.
2. `emacs/test-dx-mode.el`, run by `test_lsp.py` when emacs is installed:
   a .dx buffer connects through eglot, the checked region is shaded, the
   goals window says `Proved.` at the end of S1, a refusal shows as a
   flymake error.
3. Nothing under `kernel/` changes.

## Review (2026-09-26), folded in before the code

A skeptic read this file before any code. What changed:

1. **One cache replaces "re-check from the first change".** The server
   keeps, per document, `results[(parent node, sentence)]`: the rendered
   node, the refusal, or a genuine timeout, with the sentence compared by
   `script.strip_sentence` (so editing a comment or spacing re-checks
   nothing). A check walks the current sentences from n0 through the
   cache and sends only the first miss. So nothing is re-sent that was
   answered before, going back to an earlier text reuses its nodes, and a
   sentence that ran out of time is retried only when its text (or
   something before it) changes. A cancelled sentence is not cached.
2. **Cancel only what the edit made stale.** When a change arrives while a
   sentence runs, the server walks the new text through the cache; if
   that walk still ends at the running (parent, sentence), it lets it
   finish. Otherwise it cancels. A generation counter, read before each
   step, makes sure a result is published only for the text it was
   computed for.
3. **Bounded memory.** When a session holds more than twice as many nodes
   as the current path plus 50, the server opens a new session and
   replays the current path into it (the cache is rebuilt as it goes). A
   header change or `didClose` drops the old session: a new API route
   `POST /drop {session} -> {dropped: bool}` forgets it in `api.SESSIONS`
   and in the worker's documents (app-side only; the kernel is untouched).
4. **The reader never waits on the worker.** `dx/goals` and code actions
   are answered from the cache. `dx/hint` runs on its own thread and
   answers when the worker does. The templates are loaded once.
5. **Protocol details.** Bytes on stdin/stdout with `Content-Length` in
   UTF-8 bytes; one write lock; lines split on `\n`, `\r\n` and `\r`
   only. The position encoding is negotiated: `utf-32` (Python's own
   indices) when the client offers it, else `utf-16`; both are tested.
   Every `publishDiagnostics` carries the full list and the version; an
   empty list on close. Nothing is sent before `initialized`; unknown
   requests answer -32601, unknown notifications are ignored;
   `$/cancelRequest` is honoured for `dx/hint`; `exit` without
   `shutdown` exits 1. `server.py` routes `--lsp`, and the server runs
   with no work directory.
6. **Eglot.** A `cl-defmethod eglot-handle-notification` for `dx/progress`
   (eglot only logs notifications it does not know); stale versions are
   dropped. `dx/goals` goes out with `jsonrpc-async-request`, and a reply
   older than the latest request is dropped. Completion sends snippets
   only when the client says `snippetSupport`; otherwise the plain
   template with `_` holes.
7. **Cut:** the server-side debounce (eglot batches changes), the "not
   checked" Information diagnostic (the shading shows it), hover (the
   goals window shows the same thing). `dx/progress` sends
   `{uri, version, checkedEnd: Position | null, running: Range | null}`,
   not every range.
8. **Tests** add: an edit below a running slow sentence does not cancel
   it; a timed-out sentence is not retried until edited; about 50 edits
   leave the session's node count bounded. A `dx/stats` request (tactics
   sent, nodes held) makes the counting observable.
