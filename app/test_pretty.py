"""PRETTY.md Done-when 1: script.layout, untex and the templates."""

import glob
import json
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import script  # noqa: E402
import tex  # noqa: E402
import untex  # noqa: E402
from session import loader  # noqa: E402
from terms import Refused, parse_term, show  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEMS = sorted(glob.glob(os.path.join(HERE, "..", "kernel", "problems",
                                         "**", "*.json"), recursive=True))
# args that hold a term, as the loader reads them (and taylor's derivs)
TERM_ARGS = set(loader.TERM_ARGS) | {"derivs"}


def steps():
    for f in PROBLEMS:
        prob = loader.load(f)
        for proof in prob.proofs.values():
            for st in proof:
                yield prob, st


def terms_in(move, args):
    out = []
    for k, v in args.items():
        if k == "inst":
            out += list(v.values())
        elif k == "derivs":
            out += v
        elif k in TERM_ARGS and isinstance(v, str) and k != "bind":
            out.append(v)
    return out


class Layout(unittest.TestCase):
    def test_every_step_is_covered_exactly(self):
        n = 0
        for prob, st in steps():
            s = script.show(st["move"], st["args"])
            segs = script.layout(s)
            with self.subTest(s):
                self.assertEqual("".join(next(iter(g.values()))
                                         for g in segs), s)
                got = sorted(g["term"] for g in segs if "term" in g)
                self.assertEqual(got, sorted(terms_in(st["move"],
                                                      st["args"])))
                n += 1
        self.assertGreater(n, 30)

    def test_names_and_choices(self):
        segs = script.layout("taylor_lagrange hl := upper of 1/sqrt(1 - u) "
                             "in u from 0 to 1 at b^2 derivs 1/u; 3/u "
                             "decreasing by field using hs, h1.")
        self.assertEqual([g["name"] for g in segs if "name" in g],
                         ["hl", "u", "hs", "h1"])
        self.assertEqual([(g["choice"], g["options"]) for g in segs
                          if "choice" in g],
                         [("upper", ["lower", "upper"]),
                          ("decreasing", ["increasing", "decreasing"]),
                          ("field", ["ring", "field"])])

    def test_refused_or_commented_is_one_text(self):
        for s in ("ftc.", "nonsense x.", "ftc (* F *) x by ring."):
            self.assertEqual(script.layout(s), [{"text": s}])

    def test_templates_parse_and_holes_are_terms(self):
        self.assertEqual(list(script.TEMPLATES), list(script.FORMS))
        for m, t in script.TEMPLATES.items():
            with self.subTest(m):
                self.assertEqual(script.parse(t)[0], m)
                holes = t.count("_ ") + t.count("_.") + t.count("_;")
                self.assertEqual(sum(1 for g in script.layout(t)
                                     if g.get("term") == "_"), holes)


class Untex(unittest.TestCase):
    def test_round_trip_of_every_problem_term(self):
        n = 0
        for prob, st in steps():
            for t in terms_in(st["move"], st["args"]):
                try:
                    term = parse_term(t, prob.sig)
                except Refused:
                    continue
                with self.subTest(t):
                    self.assertEqual(show(untex.read(tex.tex(term),
                                                     prob.sig)), show(term))
                    n += 1
        self.assertGreater(n, 50)

    def test_cases(self):
        with open(os.path.join(HERE, "untex_cases.json")) as f:
            cases = json.load(f)["cases"]
        for c in cases:
            with self.subTest(c["latex"]):
                sig = c.get("functions")
                if "expect" in c:
                    self.assertEqual(show(untex.read(c["latex"], sig)),
                                     c["expect"])
                else:
                    with self.assertRaises((untex.TexError, Refused)) as cm:
                        untex.read(c["latex"], sig)
                    self.assertIn(c["refuse"], str(cm.exception))


if __name__ == "__main__":
    unittest.main()
