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
`{"status", "body", "docs": {session id: document}}`. `docs` carries the
work document of the session the request named or made, after every
route that can change one (`/session`, `/import`, `/step`, `/tactic`,
`/retract`, `/script`, `/hint`), and is empty otherwise. An internal
line `{"restore": {session id: document, ...}}` rebuilds sessions (below)
and answers `{"restored": [...], "failed": {id: message}}`. The worker
never reads a request from anywhere but its stdin, and the internal
line is not reachable over HTTP.

## The server

`Worker.handle(method, path, args)` takes a lock (one request at a time,
as before: the kernel's module tables were not written for concurrency),
writes the line, and waits for the answer at most the timeout. On time,
it keeps `docs` (the latest document per session id, and the order
sessions were made) and returns `(status, body)`.

**When the timeout passes**, or **POST /cancel** arrives (it does not
take the lock), the worker is killed, a new one is started, and every
session is restored from its latest document, in the order the sessions
were made, so the newest session for a key still owns its file. The
request that was running gets a **200**:

```
{"timeout": {"seconds": float, "cancelled": bool,
             "message": "the step ran out of time; nothing changed"}}
```

It changed nothing: its session's document is from before it, so the
restored session is exactly the one the learner had, and nothing was
written to the work file by the killed request that the restore would
not reproduce (a save happens only after a step is accepted, and the
document the server keeps is the one after that save). `/cancel` with
nothing running answers `{"cancelled": false}`; with a request running,
`{"cancelled": true}` once the new worker is ready.

**Restore** replays each document (`work.replay`) under the session's
own id, sets its key and ownership, restores `path`, `script` and
`max_rung` exactly (not cut to the checked prefix: the page's state is
unchanged), and does not write the work file. Node ids come back the
same, since the replay is of the same moves in the same order through the
same kernel; a node that does not (a kernel bug, E21) is reported in the
restore answer and the server keeps going. A session whose document
fails to restore is gone: its next request is a 400 `unknown-session`,
and the page says to start the goal again (its work file is intact).

The timeout applies to every API request, since `/palette`, `/hint` and
`/node` also call the kernel; the page shows a timeout of any of them
the same way. A worker that dies on its own (a crash, E21) is treated as
a timeout with `cancelled: false` and message "the worker stopped".
`--step-timeout 0` turns the timeout off (cancel still works).

`api.handle` in-process remains the `Backend` the tests and
`test_page.py` use unless they ask for a worker; `./calc` uses a worker.

## The page

While any request runs, a **Cancel** button (Escape) is enabled and
posts `/cancel`. A timeout or cancellation of a step marks its sentence
`timeout` (amber, not the refusal's red), and the response box says
"Stopped: the step ran out of time after 10 s. Nothing changed; it was
not refused." or "Cancelled. Nothing changed." To cursor stops there.

## Deliberately not in this cut

A time budget inside the kernel; partial results of a stopped step;
running two requests at once; a per-route timeout.

## Done when

1. `app/test_worker.py`, with a worker and a 1 s timeout: `close 0.` on
   `(x + y + z + w + 1)^24 == ?A` answers `timeout` within 3 s; the
   session's tree, reports and handles are unchanged afterwards (a fact
   bound before the timeout is still usable after it); a step after it
   is accepted; a cancel from another thread stops it the same way;
   `/cancel` with nothing running says so; sessions for two keys both
   survive a restart, the newer of two sessions for one key still owns
   its file, and nothing is written to the work file by the restore;
   every ordinary route answers through the worker exactly as in-process
   (the API tests' S1 flow, compared).
2. `app/test_page.py`: with a worker and a 1 s timeout, stepping the slow
   `close` shows the timeout, marks the sentence `timeout`, and the next
   good step is accepted; Cancel stops a slow step before the timeout.
3. Nothing under `kernel/` changes; the kernel suite still passes.
