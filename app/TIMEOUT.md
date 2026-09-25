# The per-step timeout and cancel — DESIGN.md §16.4

WHAT.md's next step. §16.4: "Cancellation is a first-class control …
The server enforces a per-step timeout and reports it as a *timeout*, not
a failure — a step that ran out of budget has not been refused." §16.2
names normalisation as the one real performance risk, and it is real:
`close 0.` on `(x + y + z + w + 1)^24 == ?A` takes about 9 s, and `^32`
about 74 s, in `ring`, during which the page is frozen and the server
answers nothing. Written before the code.

## Why a process

Python cannot stop a running thread, and the kernel is pure computation
with no place to poll a flag without touching trusted code. So the kernel
runs in a **worker process**, and stopping a step is killing the worker.
A proof state cannot move between processes (states demand a
kernel-private sentinel and fact handles refuse copies, §15.3), so the
worker holds the sessions, and the server holds only what rebuilds them:
each session's work file (PERSIST.md), which is moves, never verdicts.

## Where it sits

```
app/worker.py    the worker: JSON lines on stdin/stdout, api.handle in a
                 loop; after a request that changed a session, it also
                 returns that session's work document
app/backend.py   Backend (in-process, as before) and Worker (one child
                 process, a lock, the timeout, cancel, respawn)
app/api.py       an internal restore: a session rebuilt under its own id
app/server.py    ThreadingHTTPServer; every API request goes to the
                 backend; POST /cancel does not wait for the lock;
                 --step-timeout SECONDS (default 10)
app/page/index.html  a Cancel button while a request runs; a timeout is
                 shown as one, never as a refusal
```

## The worker

`python3 app/worker.py --work DIR` reads one JSON line per request,
`{"method", "path", "args"}`, calls `api.handle`, and writes one line,
`{"status", "body", "docs": {id: document}, "saved": {id: outcome},
"owner": OWNER}`. `docs` and `saved` carry the work document and save
outcome of the session the request named or made, after every route that
can change one (`/session`, `/import`, `/step`, `/tactic`, `/retract`,
`/script`, `/hint`), refusals included (`/hint` records the rung before it
can refuse), and are empty otherwise; `owner` is PERSIST.md's ownership
table. An internal line `{"restore": {"sessions", "owner", "saved"}}`
rebuilds sessions (below) and answers `{"restored": [...], "failed":
{id: message}}`. The worker never reads a request from anywhere but its
stdin, and the internal line is not reachable over HTTP. The protocol
writes to a duplicate of the original stdout; file descriptor 1 and
`sys.stdout` are pointed at stderr, so a stray print cannot corrupt an
answer.

## The server

`Worker.handle(method, path, args)` takes a lock (one request at a time,
as before: the kernel's module tables were not written for concurrency),
writes the line, and waits for the answer at most the timeout. On time,
it keeps `docs`, `saved` and `owner` and returns `(status, body)`. The
timeout counts from when a request gets the lock, so requests queued
behind a slow one wait for it too.

**Who stops what.** `POST /cancel` does not take the lock: it puts a
cancel token naming the running request's id on that request's answer
queue, and returns `{"cancelled": true}` at once (`false` with nothing
running). Only the thread holding the lock kills the worker and starts
the next one, whether for a timeout, a cancel token for its own request,
or the worker's end of file; a token for a request that already
finished is ignored, and so is a request's answer that arrives after its
token. Requests waiting on the lock reach the new worker only after that.
A worker found dead between requests is replaced before the next one,
which then runs normally.

**Restore is lazy.** A new worker holds no sessions. The first request
that names a session the new worker does not hold first restores that
one session from its latest document, under the same timeout, so a
timeout costs nothing for sessions not used again and never replays
every session at once. The request that was stopped gets a **200**:

```
{"timeout": {"seconds": float, "cancelled": bool,
             "message": "the step ran out of time; nothing changed"}}
```

The session the learner has is the one before the stopped request: the
server's document is from before it. The work file may be one step
ahead, when the kill came after a step's save and before its answer (or
`/hint` saved its rung first); the next save from the restored session
rewrites it, and a temporary file a kill left behind is removed when the
next worker starts.

**Restore** replays the document (`work.replay`) under the session's own
id, restores `path`, `script`, `max_rung` and its last save outcome
exactly (not cut to the checked prefix: the page's state is unchanged),
sets the ownership table to the one the worker last reported (so a
session kept from saving over an unreadable file stays kept, and a stale
tab is not promoted), and writes nothing. Every node must come back
under its own id; if any node drops or renumbers (a kernel bug, E21, or
a `RecursionError` that depends on the stack), the whole session fails
to restore rather than let the page's node ids point at different moves.
A session that fails to restore, or whose restore itself runs out of
time, is gone: its requests are a 400 `unknown-session` and the page
says so (its work file is intact, and starting the goal resumes it).

The timeout applies to every API request, since `/palette`, `/hint` and
`/node` also call the kernel; the page shows a timeout of any of them
the same way. A worker that dies on its own (a crash, E21) is treated as
a timeout with `cancelled: false` and message "the worker stopped".
`--step-timeout 0` turns the timeout off (cancel still works). Cancel
stops whatever request is running, which may be the palette's rather
than the step; the page asks for what it needs again.

`api.handle` in-process remains the `Backend` the tests and
`test_page.py` use unless they ask for a worker; `./calc` uses a worker.

## The page

While any request runs (an in-flight count kept by the page's one
request function, not the step's busy flag), a **Cancel** button
(Escape) is enabled and posts `/cancel`. A timeout answer to anything but
`/tactic` is thrown as an error by that function, so no pane reads a
timeout as data; to `/tactic` it is the step's own outcome. A timeout or cancellation of a step marks its sentence
`timeout` (amber, not the refusal's red), and the response box says
"Stopped: the step ran out of time after 10 s. Nothing changed; it was
not refused." or "Cancelled. Nothing changed." To cursor stops there.

## Deliberately not in this cut

A time budget inside the kernel; partial results of a stopped step;
running two requests at once; a per-route timeout.

## Done when

1. `app/test_worker.py`, with a worker and a 1 s timeout (a slow value
   `close` stands in for the slow step when the test needs a session that
   is fast otherwise): `close 0.` on
   `(x + y + z + w + 1)^24 == ?A` answers `timeout` within 3 s; the
   session's tree, reports and handles are unchanged afterwards (a fact
   bound before the timeout is still usable after it); a step after it
   is accepted; a cancel from another thread stops it the same way;
   `/cancel` with nothing running says so; sessions for two keys both
   survive a restart, the newer of two sessions for one key still owns
   its file, and nothing is written to the work file by the restore;
   every ordinary route answers through the worker exactly as in-process
   (the API tests' S1 flow, compared); a worker killed between requests is
   replaced and its sessions come back; a session whose document no
   longer replays answers `unknown-session`; a stray print does not
   corrupt an answer.
2. `app/test_page.py`: over a threaded server, as `./calc` runs it, with a
   worker and a 3 s timeout, stepping the slow
   `close` shows the timeout, marks the sentence `timeout`, and the next
   good step is accepted; Cancel stops a slow step before the timeout.
3. Nothing under `kernel/` changes; the kernel suite still passes.

## Review (2026-09-25), folded in

An independent skeptic read this spec against DESIGN.md, PERSIST.md and
the code (6 blocking findings, 5 minor). Folded above: one owner (the
lock holder) for kill and respawn, with cancel only posting a token; a
cancel racing a finishing request (tokens name the request id); the
ownership table and save outcomes restored as they were, not re-derived;
node ids that must not shift (the session fails instead); restore made
lazy, one session on first use, under the timeout; the page reading a
timeout as data (thrown, and an in-flight count for Cancel); "nothing was
written" corrected; stray stdout; queued requests waiting; docs sent on
refusals. Not built: tests for a cancel racing a finishing request and
for a request queued during a restart (the mechanism above covers both;
recorded).
