"""The attempt tree (DESIGN.md §16.4): one session per installed goal, one
node per accepted move, retraction by marking, never by deleting.

Untrusted. It holds ProofStates the kernel made and passes them back to
`kernel.step`; it never builds a state, an obligation, a handle or a
verdict, so no bug here can produce a theorem (app/API.md). Arguments are
turned into kernel args by `loader.step_args`, the problem files' own path.

Auto-simpl (AUTOSIMPL.md, p1_expected E162) lives here too, as data on the
nodes: each node carries the setting in force after it, a `set` node
changes it without a kernel call, and a move's node holds the chain
autosimpl.py ran after it, every step of which the kernel checked.
"""

import itertools
import os
import sys

KERNEL = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(
    __file__))), "kernel")
if KERNEL not in sys.path:
    sys.path.insert(0, KERNEL)

import kernel as K  # noqa: E402
import loader  # noqa: E402
from terms import Refused, parse_goal  # noqa: E402


# the moves that mint a handle under args["bind"]
BINDS = ("fact", "taylor_lagrange", "quad_t", "sep_autonomous",
         "energy_integral")


class Refusal(Exception):
    """An API-local refusal, or a kernel one re-raised: code, message and
    residual (a Term or None), as kernel.Refusal carries them."""

    def __init__(self, code, message, residual=None):
        super().__init__(f"{code}: {message}")
        self.code, self.message, self.residual = code, message, residual

    @classmethod
    def of(cls, r):
        return cls(r.code, r.message, r.residual)


class Node:
    """One accepted move. `handles` maps each fact bind on the path from the
    root to this node to the Handle the kernel minted for it."""

    __slots__ = ("id", "parent", "state", "move", "args", "handles",
                 "retracted", "auto_simpl", "auto", "auto_stopped")

    def __init__(self, id, parent, state, move, args, handles,
                 auto_simpl=True, auto=(), auto_stopped=None):
        self.id, self.parent, self.state = id, parent, state
        self.move, self.args, self.handles = move, args, handles
        self.retracted = False
        # E162: the setting after this node; the chain run after its move,
        # as (move, args) fed; why a chain that ran did not close the goal
        self.auto_simpl, self.auto = auto_simpl, list(auto)
        self.auto_stopped = auto_stopped


def feed(state, handles, move, args, sig):
    """One kernel move from `state`: (new state, new handles), or Refusal.
    The shared path of typed moves, replays and auto-simpl's chain."""
    try:
        # the loader's own shape check: ARG_TYPES, inst and fact shapes
        loader._steps([{"id": "step", "move": move, "args": args}],
                      "the request")
    except ValueError as e:
        raise Refusal("bad-args", str(e)) from None
    for ref in args.get("facts", ()):
        if ref[1] not in handles:
            raise Refusal("unknown-handle", f"no fact step on this path "
                          f"binds {ref[1]!r}")
    try:
        kargs = loader.step_args(args, handles, sig)
    except Refused as r:  # a term argument the parser refused
        raise Refusal.of(r) from None
    r = K.step(state, move, kargs)
    if isinstance(r, K.Refusal):
        raise Refusal.of(r)
    handles = dict(handles)
    if move in BINDS:  # each binds a handle
        handles[args["bind"]] = r.last.handle
    return r, handles


class Session:
    def __init__(self, id, goal_text, sig, problem_id=None, assume=(),
                 auto_simpl=True):
        """Install `goal_text`, parsed with `sig`, under `assume`, Γ as a
        problem file writes it (p1_expected E155). `auto_simpl` is the
        setting at the installed goal (E162): on, except when a work file
        saved before E162 is replayed. Raises Refusal when the parser, the
        loader ('bad-assume') or kernel.install refuses."""
        try:
            goal = parse_goal(goal_text, sig)
            gamma = loader.assumptions(list(assume), sig)
        except Refused as r:
            raise Refusal.of(r) from None
        except ValueError as e:
            raise Refusal("bad-assume", str(e)) from None
        st = K.install(goal, gamma)
        if isinstance(st, K.Refusal):
            raise Refusal.of(st)
        self.id, self.sig, self.problem_id = id, dict(sig), problem_id
        self.goal_text = goal_text
        self.assume = [dict(a) for a in assume]
        self._ids = itertools.count()
        self.nodes = {}  # insertion-ordered: parents before children
        self._add(None, st, "install", {}, {}, auto_simpl)

    def _add(self, parent, state, move, args, handles, auto_simpl,
             auto=(), auto_stopped=None):
        n = Node(f"n{next(self._ids)}", parent, state, move, args, handles,
                 auto_simpl, auto, auto_stopped)
        self.nodes[n.id] = n
        return n

    def root(self):
        return self.nodes["n0"]

    def children(self, node_id):
        return [n for n in self.nodes.values() if n.parent == node_id]

    def step(self, node_id, move, args, auto=None, auto_stopped=None):
        """Feed one move from node `node_id` (any node: a node with children
        forks). Returns the new Node, or raises Refusal. A refused move adds
        nothing. `args` are the problem-file shapes (ARCHITECTURE.md §9).

        E162: `set` changes the setting and calls no kernel; `simpl` (the
        script's, with the setting on) is the chain alone; any other move
        is followed by the chain when AUTOSIMPL.md's trigger holds. `auto`
        is None live, and on replay the recorded chain, applied exactly and
        never recomputed, with `auto_stopped` its recorded note."""
        at = self.nodes[node_id]
        replay = auto is not None
        if at.state.goal is None and move in ("set", "simpl"):
            # the kernel's proof-finished, as any other move gets it
            self._feed_from(at, "close", {"value": "0", "check": "ring",
                                          "facts": []})
        if move == "set":
            if (set(args) != {"auto_simpl"}
                    or type(args["auto_simpl"]) is not bool):
                raise Refusal("bad-args", "set takes {auto_simpl: bool}")
            return self._add(at.id, at.state, move, dict(args),
                             dict(at.handles), args["auto_simpl"])
        if move == "simpl":
            import autosimpl
            if not at.auto_simpl:
                raise Refusal("bad-move", "simpl is close with its value "
                              "computed while auto-simpl is off (fill.py)")
            self._simpl_args(at, args)
            if replay:
                if not auto:  # a typed simpl is its chain, or nothing
                    raise Refusal("auto-replay", "a simpl node with no "
                                  "recorded chain")
                state, handles = self._replay(at, at.state, at.handles,
                                              auto)
                steps = list(auto)
            else:
                try:
                    steps, state, handles = autosimpl.run(
                        at.state, at.handles, self._feed,
                        args.get("facts", ()))
                except autosimpl.Stopped as e:
                    raise Refusal("simpl-stopped", "auto-simpl stopped: "
                                  f"{e.message}", e.residual) from None
            return self._add(at.id, state, move, dict(args), handles,
                             at.auto_simpl, steps)
        state, handles = self._feed_from(at, move, args)
        steps, stopped = [], None
        triggers = at.auto_simpl and self._triggers(at.state, state)
        if replay:
            if auto and not triggers:
                raise Refusal("auto-replay", "a recorded auto-simpl chain "
                              "where none could run")
            state, handles = self._replay(at, state, handles, auto)
            steps, stopped = list(auto), auto_stopped
        elif triggers:
            import autosimpl
            try:
                steps, state, handles = autosimpl.run(state, handles,
                                                      self._feed)
            except autosimpl.Stopped as e:
                stopped = e.message
        return self._add(at.id, state, move, dict(args), handles,
                         at.auto_simpl, steps, stopped)

    def _simpl_args(self, at, args):
        """A typed simpl with the setting on: args as simpl's own (check,
        facts), on a goal of constants with ?A (fill.py's test, which
        the raw /step route does not pass through)."""
        import autosimpl
        if not set(args) <= {"check", "facts"}:
            raise Refusal("bad-args", "simpl takes check and facts")
        try:
            loader._steps([{"id": "step", "move": "close", "args": {
                "value": "0", "check": args.get("check", "ring"),
                "facts": args.get("facts", [])}}], "the request")
        except ValueError as e:
            raise Refusal("bad-args", str(e)) from None
        if not autosimpl.constant_goal(at.state):
            raise Refusal("bad-args", "simpl computes the value of a goal "
                          "that is only constants, with ?A")

    def _feed_from(self, at, move, args):
        """_feed from node `at`, naming auto-simpl when the goal it closed
        after a move (not a typed simpl) is why the move is refused
        proof-finished (AUTOSIMPL.md)."""
        try:
            return self._feed(at.state, at.handles, move, args)
        except Refusal as r:
            if r.code == "proof-finished" and at.auto and \
                    at.move != "simpl":
                r.message += ("; auto-simpl closed this goal after the "
                              "previous move: put `Unset Auto Simpl.` before "
                              "that move to make these moves yourself")
            raise

    def _feed(self, state, handles, move, args):
        return feed(state, handles, move, args, self.sig)

    def _replay(self, at, state, handles, steps):
        """A recorded chain, applied exactly (PERSIST.md, E162), and held
        to the rules a live chain keeps: only rewrite, fact and close,
        no admission added, and the goal closed at the end. Anything else
        is 'auto-replay', which drops the node, so a work file cannot
        put a chain on the page that auto-simpl would never have run."""
        import autosimpl
        if not steps:
            return state, handles
        base = autosimpl.admissions(state)
        for m, a in steps:
            if m not in ("rewrite", "fact", "close"):
                raise Refusal("auto-replay", f"a recorded auto-simpl step "
                              f"{m} is not rewrite, fact or close")
            try:
                state, handles = self._feed(state, handles, m, a)
            except Refusal as r:
                raise Refusal("auto-replay", f"the recorded auto-simpl step "
                              f"{m} was refused: {r.code}: {r.message}") \
                    from None
            if autosimpl.admissions(state) > base:
                raise Refusal("auto-replay", f"the recorded auto-simpl step "
                              f"{m} adds an admitted obligation")
        if state.goal is not None:
            raise Refusal("auto-replay", "a recorded auto-simpl chain that "
                          "does not close the goal")
        return state, handles

    @staticmethod
    def _triggers(before, after):
        """AUTOSIMPL.md's trigger: the move changed the goal (so a fact
        never triggers) and left a constant one with ?A."""
        import autosimpl
        return after.goal != before.goal and autosimpl.constant_goal(after)

    def retract(self, node_id):
        """Mark `node_id` and every node below it retracted, and return its
        parent. Nothing is deleted."""
        n = self.nodes[node_id]
        if n.parent is None:
            raise Refusal("retract-root", "the installed goal has no parent "
                          "to retract to")
        marked = {node_id}
        for m in self.nodes.values():  # parents come first
            if m.id in marked or m.parent in marked:
                marked.add(m.id)
                m.retracted = True
        return self.nodes[n.parent]
