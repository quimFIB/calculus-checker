"""DX.md: the header and the sentence fixture. The language server and the
Emacs suite are tested in test_lsp.py (LSP.md)."""

import json
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import dx  # noqa: E402
import script  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


class Header(unittest.TestCase):
    def test_forms(self):
        self.assertEqual(dx.header("problem stage0.S1."),
                         {"problem": "stage0.S1"})
        self.assertEqual(dx.header("goal Int[x = 0 .. 1] f(x) == ?A "
                                   "functions f/1, g/2."),
                         {"goal": "Int[x = 0 .. 1] f(x) == ?A",
                          "functions": {"f": 1, "g": 2}})
        self.assertEqual(dx.header("goal x == ?A."),
                         {"goal": "x == ?A", "functions": {}})
        # the last depth-0 `functions` splits (a function may be so named)
        self.assertEqual(dx.header("goal functions(x) == ?A functions "
                                   "functions/1."),
                         {"goal": "functions(x) == ?A",
                          "functions": {"functions": 1}})

    def test_assuming(self):
        """p1_expected E155's items after `assuming`, ';'-separated; a reg
        is written 'v in C^k'."""
        h = dx.header("goal v(t) == v(0) + t functions v/1 assuming eom: "
                      "D[s] v(s) == 1 for s in [0, oo); regv: v in C^1 for "
                      "s in [0, oo).")
        self.assertEqual(h["functions"], {"v": 1})
        self.assertEqual(h["assume"], [
            {"name": "eom", "var": "s", "in": "[0, oo)",
             "law": "D[s] v(s) == 1"},
            {"name": "regv", "var": "s", "in": "[0, oo)",
             "reg": {"fn": "v", "class": 1}}])
        self.assertEqual(dx.header(dx.show_header(h)), h)
        for bad in ("goal x assuming .", "goal x assuming eom D[s] v(s).",
                    "goal x assuming eom: v(s) >= 0."):
            with self.subTest(bad), self.assertRaises(dx.HeaderError):
                dx.header(bad)

    def test_refusals(self):
        for bad in ("ftc x by ring.", "problem a b.", "goal .",
                    "goal x == ?A functions f.", "goal x functions f/0."):
            with self.subTest(bad), self.assertRaises(dx.HeaderError):
                dx.header(bad)

    def test_round_trip(self):
        for h in ({"problem": "stage0.S1"},
                  {"goal": "x == ?A", "functions": {}},
                  {"goal": "f(x) == ?A", "functions": {"f": 1}}):
            self.assertEqual(dx.header(dx.show_header(h)), h)


class Sentences(unittest.TestCase):
    def test_python_splitter_matches_the_fixture(self):
        with open(os.path.join(HERE, "sentences.json")) as f:
            cases = json.load(f)["cases"]
        for c in cases:
            self.assertEqual([list(s) for s in script.spans(c["text"])],
                             c["spans"], c["text"])


if __name__ == "__main__":
    unittest.main()
