# Persistence and export — DESIGN.md §16.4

WHAT.md's next step: restarting `./calc` loses the attempt tree and the
script. §16.4: "a file per problem under the working directory, plus
explicit export/import — the whole tree, including the dead ends. Scripts
and trees, never theorems; everything is re-checked on load." §15.3: "Nothing
reconstructs a judgement from storage." Written before the code.

Untrusted, like the rest of `app/`. A work file holds moves and their
arguments, exactly what the page already sends; a verdict is never read
from one. Loading one is replaying it through `kernel.step`, so a
hand-edited or stale file can at worst fail to replay, never produce a
theorem.

## Where it sits

```
app/work.py           the work file: write, read, key, replay
app/script.py         also sentences(text): the page's splitter, in Python
app/api.py            autosave; /session resume; /script; /export; /import
app/server.py         --work DIR (default ./calc-work)
app/page/index.html   Export, Import, Start fresh; saved state on the status line
```

## The work file

```
{ "format": "calc-work", "version": 1,
  "problem": str | null,              -- a problem id, or null for your own goal
  "goal": str, "functions": {name: arity},
  "script": str,                      -- the page's script text
  "path": [str],                      -- node ids: the checked path, from n0
  "max_rung": int,
  "nodes": [{ "node": str, "parent": str, "move": str, "args": {...},
              "retracted": bool }],   -- every node but n0, parents first
  "saved": str }                      -- ISO 8601 UTC, information only
```

No proof state, report, theorem, obligation, handle or residual is written.
`args` are the problem-file shapes `/step` takes (ARCHITECTURE.md §9).

**Where.** `DIR/<key>.json`, DIR from `./calc --work DIR`, default
`calc-work` under the directory `./calc` was started in (and ignored by
git). `api.py` itself saves nothing until a directory is set, so the test
suites, which build the API in-process, never touch real work. The key is
the problem id when it is made only of `[A-Za-z0-9._-]`, is not `.` or
`..`, and does not end in `.prev` or `.bad` (every problem id qualifies);
else, and for your own goal, `goal-` and the first 12 hex digits of the
SHA-256 of `json.dumps([goal, sorted(functions.items())])` in UTF-8. A key
never comes from an imported file's name.

**Ownership.** One session writes a key's file: the newest one started
or imported for that key. An older session (another tab, a tab left open
across a Start fresh) stops saving, and `/tree` says so (`saved:
{"error": "superseded: ..."}`), so a stale tab can never overwrite newer
work.

**When.** When the session starts (so a Start fresh sticks at once),
and after every change to the session's saved content: an accepted
`/step` or `/tactic` (a refusal changes nothing), `/retract`, `/hint`
(max rung), and `POST /script`. Written to a temporary file in DIR and
moved into place with `os.replace`, so a crash leaves the old file or the
new, never half of one. A write that fails never fails the request; `/tree`
reports it (below).

**Starting over.** When a session starts with `resume: false` over an
existing file, or `/import` lands on an existing file, the old file is
first copied to `<key>.prev.json` (one generation, replaced each time).
Start fresh keeps the old file's `max_rung`: the rung reached is §17's
record and is not reset by starting again. (A hand edit can still lower
it; the file is the learner's.) A file that cannot be read at all (an
OS error) is left alone and the session does not save over it.

## Replay

`work.replay(doc)` builds a `Session` from `goal` and `functions` (the
problem's own when `problem` names one: the file's copy is ignored, since
the problem file is the authority), then steps each node, in file order,
from its parent's new node with `Session.step`, the same call `/step`
makes. A node is **dropped**, with its descendants, when its parent was
dropped, when a field is malformed, or when the kernel refuses it (the
kernel changed, or the file was edited); each drop is reported as
`{node, move, code, message}`. Then the `retracted` marks are set on the
nodes that replayed (only the JSON value `true` marks one). A goal that no
longer installs is the kernel's refusal, as `/session` returns one. New node ids are assigned in order, so they equal the
old ones when nothing was dropped; the response carries the map.

**The checked prefix.** The mapped `path` is first cut to a parent chain:
it starts at n0 and stops before the first id that did not replay or is
not a child of the id before it. Then k is the longest prefix of the
script's sentences where sentence i parses (SCRIPT.md) to exactly the move
and args of the chain's node i+1, and that node is not retracted. The
page marks those k sentences checked, at the character spans the server
returns (`spans`), so the page never re-splits the script to find them.
A node made by `/step` with args not in `parse`'s canonical form (an
explicit `mode: "forward"`, say) simply does not count as checked. So a file whose path and script drifted apart (a crash
between the step and the `/script` post, an edit by hand) resumes with the
matching part checked and the rest as unchecked text, never with a
sentence marked checked that the node below it did not come from.

`script.sentences` is `nextSentence` in the page, ported: a sentence ends
at a `.` followed by whitespace or the end, outside `(* *)` comments, never
inside `..`. Whitespace is the ASCII set ` \t\n\r\f\v` in both, since
Python's `isspace` and JavaScript's `\s` disagree beyond it. A test runs
both over the same scripts, those characters included.

## The API

- `POST /session` takes `resume: bool` (default false, so existing
  callers are unchanged). With `resume: true` and a work file for the key,
  the session is the file's replay, and the response is n0 rendered plus
  `"resumed": {script, path, checked, spans, dropped, ids, max_rung}`
  (`path` already mapped and cut to `checked + 1` nodes), `"problem"` and
  `"key"`. With no file, `"resumed": null`. A file that is not a readable `calc-work` version 1
  document is not replayed: it is moved to `<key>.bad.json` and
  `resumed` is `{"error": message}`.
- `POST /script {session, script, path}` records the page's script and
  checked path (node ids of this session) and saves. `{saved: bool}`.
- `GET /export ?session` returns the work file for the session, as it
  would be saved now.
- `POST /import {document}` replays the document as resume does and
  saves it under its key; the response is `/session`'s with `resumed`.
  The server's 1 MiB body limit caps an import at a few thousand nodes;
  export has no cap. Replay has no timeout (the per-step timeout is next).
  A document that is not a `calc-work` version 1 object, or names an
  unknown problem, is a 400 `bad-document`.
- `GET /tree` gains `"saved": {"file", "at"} | {"error"} | null`.

## The page

- Starting a problem or your own goal sends `resume: true`, and sets the
  script, the checked sentences and the path from `resumed`. Dropped steps
  are listed in the response box ("2 saved steps no longer check: …") with
  each one's code and message.
- The script is posted with `/script` after each step, retraction and
  (debounced, 500 ms) edit. It replaces the browser's localStorage copy,
  so there is one saved copy of the work, the server's; copies already in
  localStorage are left there and not read.
- **Export** downloads `/export` as `<key>.calc.json`. **Import** reads a
  chosen file and posts it to `/import`. **Start fresh** starts the same
  goal with `resume: false`.
- The status line shows `saved` (or `not saved: <why>`) from `/tree`.

## Deliberately not in this cut

Several saved attempts per problem (the tree already holds every
attempt); merging two files; saving the hint texts shown; the per-step
timeout (next); removing sessions from memory (every start adds one, as
before).

## Done when

1. `app/test_work.py`: a session with a dead end (a retracted branch), a
   fact, a hint and a script round-trips through the work file into an
   equal tree (same nodes, parents, moves, args, retracted marks, reports
   recomputed equal), path and max rung; a node refused on replay is
   dropped with its descendants and reported; an edited `path` or script
   gives the matching checked prefix, a path into a dead end is cut, and
   the spans are exactly the checked sentences; a file holding a report or
   theorem field is read as moves only (the field is ignored); a corrupt
   file is moved aside; the write is atomic (the old file survives a
   failed write); the newer of two sessions owns the file; Start fresh
   sticks and keeps the rung; with no work directory nothing is written;
   `script.sentences` agrees with the page's `nextSentence` (run in node)
   on scripts with non-ASCII whitespace.
2. The routes (`/session` resume, `/script`, `/export`, `/import`,
   `/tree`'s `saved`) are exercised by those tests over a temporary work
   directory.
3. `app/test_page.py`: step S1 halfway, reload the page, start S1 again:
   the script and checked region come back and the next step closes it;
   Export then Import gives the same tree.
4. Nothing under `kernel/` changes; the kernel suite still passes.

## Review (2026-09-25), folded in

An independent skeptic read this spec against DESIGN.md and the code (4
blocking findings, 7 minor). It confirmed fact handles cannot cross
branches on replay and injected verdict fields are ignored. Folded above:
two tabs or a stale tab overwriting newer work (ownership); the test
suites writing into real work (no directory, no saving); the two sentence
splitters disagreeing on non-ASCII whitespace (ASCII only, and the server
returns the spans); the path as a parent chain; Start fresh resetting the
rung and not sticking; `/step` nodes in non-canonical form; the import
size limit; the response's problem and key, a goal that no longer
installs, a non-bool `retracted`, the key's exact bytes and backup-name
collisions, an OS error not moving a file aside, and localStorage.
