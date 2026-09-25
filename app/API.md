# The JSON API — DESIGN.md §16.3, first cut

The kernel's in-process `step()` behind a local HTTP server. Written before
the code, as every step in this repo has been. It covers what the kernel can
already answer; the assistance calls (`/hint`, `/palette`) were first added as
refusals, and are now answered (RECOGNIZER.md, UI.md).

## Where it sits

```
app/session.py   the attempt tree (§16.4): nodes, parents, retraction.   untrusted
app/api.py       JSON in, JSON out: one function per route, no HTTP.      untrusted
app/server.py    http.server over api.py, localhost only.                 untrusted
./calc           starts the server.
```

Nothing in `app/` is trusted. It parses strings with the trusted parser and
passes terms to `kernel.install` and `kernel.step`, exactly as
`kernel/loader.py` does, and it reuses `loader.step_args` for the argument
shapes. **No proof state crosses the API** (§15.3, §16.3): the server keeps
each `ProofState` in its session and hands out node ids. The client gets
rendered text, never a state, and nothing it sends can become one. A bug in
`app/` can show the wrong goal; it cannot produce a theorem, because every
verdict string comes from `kernel.report`.

Standard library only (§16.2): `json`, `http.server`, `secrets`.

## Conventions

- Every request and response body is a JSON object. `GET` routes take their
  arguments as a query string instead.
- Ids are strings: sessions are random (`secrets.token_hex(8)`), nodes are
  `n0`, `n1`, ... within a session. `n0` is the installed goal.
- **A refusal is a 200**, because a refused move is an answer, not an error:
  `{"refusal": {"code", "message", "residual", "stuck"}}`, `residual` a
  term string or `null`; `stuck` is STUCK.md's explanation on `/step` and
  `/tactic` refusals (`{kind, headline, lines, suggest}`, `suggest` a list
  of sentences the kernel accepted from that node, or `null`), `null`
  elsewhere. Codes are the kernel's own (ARCHITECTURE.md §6, GRAMMAR.md §1),
  plus the API's, below.
- An unknown route is a **404**. A malformed request (bad JSON, missing or
  mistyped field, unknown session, node or problem) is a **400**, with `{"error": {"code", "message"}}`.
- An exception from the kernel that is not a refusal is a kernel bug (E21):
  **500** with `{"error": {"code": "kernel-error", "message"}}`, and the
  session is left as it was.

## The rendered node

Every route that lands on a node returns this shape:

```
{ "session": str,
  "node":    str,
  "parent":  str | null,
  "move":    "install" | one of kernel.MOVES,
  "report":  kernel.report(state)            -- "Open: ...", "Proved.", ...
  "goal":    str | null                      -- show_goal, null once closed
  "theorem": str | null                      -- after close
  "obligations": [ { "key", "sources", "status", "method", "cites",
                     "reason", "new" } ... ]
  "occurrences": int | null                  -- rewrite (E2)
  "handles": [str]                           -- fact binds usable here
  "retracted": bool
  "goal_tex", "theorem_tex": str | null      -- UI.md §1, KaTeX input
  "progress": {signal, detail} | null        -- UI.md §3, null at n0
  "probe": {before, after, digits, agree} | {skipped} | null   -- UI.md §4
  "admissions": int                          -- obligations admitted here
  "stuck": {kind, headline, lines, suggest} | null  -- STUCK.md, when this
                                               step admitted an obligation
  "steps": int                               -- accepted steps from n0
}
```

`key` is `show(ob.key)`, `sources` sorted, `method`/`cites` the tag's two
halves, `reason` the admission reason or null, and `new` true when the key
was not in the parent's tracker (StepRecord has no such flag; the caller
compares, §4). Certificates are not sent in this cut.

## Routes

```
GET  /problems                         -> {problems: [{id, title, statement}]}
POST /session  {problem: id}           -> node n0
POST /session  {goal: str, functions?: {name: arity}}   -> node n0
POST /step     {session, node, move, args}               -> the new node | refusal
POST /retract  {session, node}         -> the parent node
GET  /node     ?session&node           -> that node
GET  /tree     ?session                -> {session, nodes: [{node, parent, move,
                                            report, retracted, summary}]}
POST /parse    {text, functions?}      -> {term: str, katex: str} | refusal
GET  /moves                            -> {moves: [{name, args}]}   (PAGE.md)
POST /tactic   {session, node, text}   -> the new node | refusal    (SCRIPT.md)
GET  /hint     ?session&node&rung      -> {rung, integral, row, text, cost} | refusal
                                            (assist/RECOGNIZER.md)
GET  /palette  ?session&node           -> {moves, rewrites, card}   (UI.md §2)
```

- **`/problems`** lists every `*.json` under `kernel/problems/` that
  `loader.load` accepts. A problem's `reference_proof` is never sent (PF1).
- **`/session`** installs a goal. `install`'s refusal is returned as a
  refusal and no session is made.
- **`/step`** feeds one move from any node, not just the latest. Stepping
  from a node that already has children **forks**: the attempt tree is the
  state model (§16.4). `args` are the problem-file shapes
  (ARCHITECTURE.md §9): terms as GRAMMAR.md strings, a fact as
  `["handle", name]`. Handles are scoped to the path: a `fact` step's
  `bind` is visible from its node and every node below it, and nowhere
  else. A parse failure in an argument is a refusal with the parser's code.
  An unknown handle name is a refusal `unknown-handle`. A refused move adds
  no node.
- **`/retract`** marks the node and everything below it retracted and
  returns its parent. **Nothing is deleted** (§16.4): a retracted branch
  stays in `/tree` with its report, and stepping from a retracted node is
  allowed and un-retracts nothing but the new node. Retracting `n0` is a
  refusal `retract-root`.
- **`/tree`**'s `summary` is the move and its main argument (`ftc F := ...`,
  `rewrite ln_one`), for the attempts pane.
- **`/parse`** is §16.3's echo. It parses a term, or a goal when the text
  contains `==`, and returns `show` of it. `katex` was null until a
  tested printer existed (a wrong one is worse than none); it is now
  `tex.tex`'s output, round-tripped through the trusted parser (UI.md §1).
- **`/hint`** is the ladder (`assist/RECOGNIZER.md`): rung 1, 2 or 3 of
  the first recognizer row matching the first `Int` in the node's goal.
  Refusals `no-integral`, `no-row`, and `not-built` for rung 4.
- **`/palette`** is UI.md §2: the moves whose shape fits the goal, the
  entry rewrites that match (each a ready tactic sentence) and the
  antiderivative card with its matching rows marked. `/parse`'s `katex`
  is now the term's TeX (UI.md §1), and `/tree` carries the session's
  `max_rung`, which `/hint` records.

API-local refusal codes: `unknown-handle`, `retract-root`, `not-built`,
`no-integral`, `no-row` (RECOGNIZER.md),
`bad-tactic` (SCRIPT.md).
Error codes: `bad-json`, `bad-request`, `unknown-route`, `unknown-session`,
`unknown-node`, `unknown-problem`, `kernel-error`.

## Deliberately not in this cut

- **The per-step timeout** (§16.4). Python cannot cancel a running step in
  a thread, and a child process per step costs the latency §16.3 is about.
  The kernel's own bounds (`power-too-large`, ARCHITECTURE.md §6) are what
  stops a runaway step today.
- **Progress and probe** on `/step` (§8.5, §8.6): they need the recognizer.
- **Persistence and export** of trees (§16.4).
- **KaTeX**, above.
- **Remote access.** The server binds `127.0.0.1` only.

## Done when

1. `python3 -m unittest discover -s app` passes, covering: every route; each
   error and refusal code above; every problem file replayed through the
   API reaching the same `report` and obligation keys as `loader.replay`;
   forking, retraction and handle scoping; a refused step adding no node;
   and a proof state never appearing in any response (every response is
   plain JSON).
2. `python3 kernel/proof_of_life.py` and the kernel's unit tests still
   pass: nothing under `kernel/` changes.
3. `./calc` starts the server and a `curl` session proves S1.
