"""The attempt tree (DESIGN.md §16.4): one session per installed goal, one
node per accepted move, retraction by marking, never by deleting.

Untrusted. It holds ProofStates the kernel made and passes them back to
`kernel.step`; it never builds a state, an obligation, a handle or a
verdict, so no bug here can produce a theorem (app/API.md). Arguments are
turned into kernel args by `loader.step_args`, the problem files' own path.
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
                 "retracted")

    def __init__(self, id, parent, state, move, args, handles):
        self.id, self.parent, self.state = id, parent, state
        self.move, self.args, self.handles = move, args, handles
        self.retracted = False


class Session:
    def __init__(self, id, goal_text, sig, problem_id=None):
        """Install `goal_text`, parsed with `sig`. Raises Refusal when the
        parser or kernel.install refuses."""
        try:
            goal = parse_goal(goal_text, sig)
        except Refused as r:
            raise Refusal.of(r) from None
        st = K.install(goal)
        if isinstance(st, K.Refusal):
            raise Refusal.of(st)
        self.id, self.sig, self.problem_id = id, dict(sig), problem_id
        self.goal_text = goal_text
        self._ids = itertools.count()
        self.nodes = {}  # insertion-ordered: parents before children
        self._add(None, st, "install", {}, {})

    def _add(self, parent, state, move, args, handles):
        n = Node(f"n{next(self._ids)}", parent, state, move, args, handles)
        self.nodes[n.id] = n
        return n

    def root(self):
        return self.nodes["n0"]

    def children(self, node_id):
        return [n for n in self.nodes.values() if n.parent == node_id]

    def step(self, node_id, move, args):
        """Feed one move from node `node_id` (any node: a node with children
        forks). Returns the new Node, or raises Refusal. A refused move adds
        nothing. `args` are the problem-file shapes (ARCHITECTURE.md §9)."""
        at = self.nodes[node_id]
        try:
            # the loader's own shape check: ARG_TYPES, inst and fact shapes
            loader._steps([{"id": "step", "move": move, "args": args}],
                          "the request")
        except ValueError as e:
            raise Refusal("bad-args", str(e)) from None
        for ref in args.get("facts", ()):
            if ref[1] not in at.handles:
                raise Refusal("unknown-handle", f"no fact step on this path "
                              f"binds {ref[1]!r}")
        try:
            kargs = loader.step_args(args, at.handles, self.sig)
        except Refused as r:  # a term argument the parser refused
            raise Refusal.of(r) from None
        r = K.step(at.state, move, kargs)
        if isinstance(r, K.Refusal):
            raise Refusal.of(r)
        handles = dict(at.handles)
        if move in ("fact", "taylor_lagrange"):  # both bind a handle
            handles[args["bind"]] = r.last.handle
        return self._add(at.id, r, move, dict(args), handles)

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
