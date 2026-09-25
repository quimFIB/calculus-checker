"""UI.md §2–§4: the palette, the card, the progress signal and the probe,
over every reference proof."""

import unittest

import api
import script
from assist import palette as PL, probe, progress
from session import K, loader
from terms import parse_goal


def _nodes():
    """(problem id, proof, [(step id, move, state)]) for every proof."""
    for pid, (p, _, _) in api._problem_files().items():
        for name, steps in p.proofs.items():
            results, _ = loader.replay(p, name)
            moves = {s["id"]: s["move"] for s in steps}
            yield pid, name, [(sid, moves.get(sid, "install"), st)
                              for sid, st in results
                              if not isinstance(st, K.Refusal)]


class Palette(unittest.TestCase):
    def test_rewrite_sentences_are_accepted_by_the_kernel(self):
        """Every sentence the palette offers on a reference node parses
        and matches; only a side condition may refuse it."""
        bad = {"bad-tactic", "rewrite-lhs-mismatch",
               "rewrite-target-not-found", "bad-args"}
        tried = 0
        for pid, _, nodes in _nodes():
            sig = api._problem_files()[pid][0].sig
            for sid, _, st in nodes:
                if st.goal is None:
                    continue
                for r in PL.rewrites(st.goal):
                    move, args = script.parse(r["sentence"])
                    got = K.step(st, move, loader.step_args(args, {}, sig))
                    tried += 1
                    code = getattr(got, "code", None)
                    with self.subTest(pid=pid, step=sid, s=r["sentence"]):
                        self.assertNotIn(code, bad, getattr(got, "message",
                                                            ""))
        self.assertGreater(tried, 30)

    def test_the_reference_rewrites_are_offered(self):
        """Each rewrite a reference proof takes is in its node's palette."""
        for pid, (p, _, _) in api._problem_files().items():
            for name, steps in p.proofs.items():
                results, _ = loader.replay(p, name)
                states = dict(results)
                prev = results[0][1]
                for s in steps:
                    if s["move"] == "rewrite" and not isinstance(
                            prev, K.Refusal):
                        entries = {r["entry"] for r in PL.rewrites(prev.goal)}
                        with self.subTest(pid=pid, step=s["id"]):
                            self.assertIn(s["args"]["entry"], entries)
                    prev = states.get(s["id"], prev)

    def test_moves(self):
        g = parse_goal("Int[x = 1 .. 0] x == ?A")
        self.assertEqual([m["move"] for m in PL.moves(g)],
                         ["ftc", "int_subst", "int_parts", "int_flip",
                          "fact"])
        g = parse_goal("sin 0 + 1 == ?A")
        self.assertEqual([m["move"] for m in PL.moves(g)], ["close", "fact"])

    def test_card(self):
        g = parse_goal("Int[x = 0 .. 1] 1/(1 + x^2) + cos(2*x) == ?A")
        marked = [c["id"] for c in PL.card(g) if c["matches"]]
        self.assertEqual(marked, ["cos", "arctan"])


class Progress(unittest.TestCase):
    def test_finishing_ftc_is_never_worse(self):
        n = 0
        for pid, _, nodes in _nodes():
            for (_, _, a), (sid, move, b) in zip(nodes, nodes[1:]):
                if move in ("ftc", "int_improper") and a.goal:
                    with self.subTest(pid=pid, step=sid):
                        sig = progress.signal(a.goal, b.goal)["signal"]
                        self.assertIn(sig, ("finishable", "closed"))
                    n += 1
        self.assertGreater(n, 8)

    def test_signals(self):
        a = parse_goal("Int[x = 0 .. 1] x*exp(x^2) == ?A")
        b = parse_goal("Int[u = 0 .. 1] exp u / 2 == ?A")
        self.assertEqual(progress.signal(a, b)["signal"], "finishable")
        self.assertEqual(progress.signal(a, None)["signal"], "closed")
        c = parse_goal("Int[x = 0 .. 1] sqrt(x^2) == ?A")
        self.assertEqual(progress.signal(a, c)["signal"], "rule now matches")
        d = parse_goal("Int[x = 0 .. 1] x*exp(x^2)*sin(ln x) == ?A")
        self.assertEqual(progress.signal(a, d)["signal"], "worse")
        e = parse_goal("Int[x = 0 .. 1] exp(x)*sin x == ?A")
        f = parse_goal("Int[x = 0 .. 1] exp(x)*sin x*cos(ln x) == ?A")
        self.assertNotEqual(progress.signal(e, f)["signal"], "worse")


class Probe(unittest.TestCase):
    def test_every_accepted_step_agrees(self):
        n = 0
        for pid, _, nodes in _nodes():
            for (_, _, a), (sid, _, b) in zip(nodes, nodes[1:]):
                if a.goal is None or b.goal is None:
                    continue
                r = probe.compare(a.goal, b.goal)
                if "skipped" in r:
                    continue
                with self.subTest(pid=pid, step=sid):
                    self.assertTrue(r["agree"], r)
                n += 1
        self.assertGreater(n, 30)

    def test_the_wrong_substitution_of_8_6(self):
        r = probe.compare(
            parse_goal("Int[x = 0 .. pi^2/4] sin(sqrt x) == ?A"),
            parse_goal("Int[t = 0 .. pi/2] sin(sqrt(sin t))*cos t == ?A"))
        self.assertFalse(r["agree"])
        self.assertAlmostEqual(r["before"], 2.0, places=10)
        self.assertAlmostEqual(r["after"], 2 * (0.8414709848078965
                                                - 0.5403023058681398), 10)

    def test_improper_and_skips(self):
        r = probe.compare(parse_goal("Int[x = 0 .. oo] 1/(1 + x^4) == ?A"),
                          parse_goal("pi*sqrt 2/4 == ?A"))
        self.assertEqual(r["digits"], 12)
        self.assertEqual(
            probe.compare(parse_goal("Int[x = 0 .. 1] a*x == ?A"),
                          parse_goal("a/2 == ?A")), {"skipped": "symbols a"})
        self.assertIn("skipped", probe.compare(
            parse_goal("D[x](x^2) == ?A"), parse_goal("2*x == ?A")))

    def test_digits_near_zero(self):
        self.assertEqual(probe.digits(0.0, 1.2e-16), 12)
        self.assertEqual(probe.digits(1.0, 1.001), 3)


if __name__ == "__main__":
    unittest.main()
