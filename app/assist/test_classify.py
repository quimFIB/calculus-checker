"""CLASSIFY.md: unit 00 P1's five equations, a constant, custom names, a
refusal, and the route."""

import unittest

from assist.classify import Refusal, classify
import api


class Classify(unittest.TestCase):
    def test_unit00_p1(self):
        cases = {  # the sheet's (a)-(e), with the worked solution's verdicts
            "-(m*g) - b*v": "F(v)", "-kappa*x^3": "F(x)",
            "F0*exp(-t/tau)": "F(t)", "-b*v - kappa*x": "none",
            "-kappa*x*(1 + epsilon*cos(omega*t))": "none"}
        for f, want in cases.items():
            with self.subTest(f):
                self.assertEqual(classify(f)["case"], want)

    def test_repairs(self):
        """'What would have to be true': b = 0 or kappa = 0 for (d),
        epsilon = 0 for (e)."""
        d = {(r["parameter"], r["case"])
             for r in classify("-b*v - kappa*x")["repairs"]}
        self.assertEqual(d, {("b", "F(x)"), ("kappa", "F(v)")})
        e = {r["parameter"]: r["case"] for r in
             classify("-kappa*x*(1 + epsilon*cos(omega*t))")["repairs"]}
        self.assertEqual(e.get("epsilon"), "F(x)")
        self.assertEqual(classify("-b*v - kappa*x")["free"], ["v", "x"])

    def test_constant_and_names(self):
        self.assertEqual(classify("-(m*g)")["case"], "constant")
        r = classify("-k*y", t="s", v="u", x="y")
        self.assertEqual((r["case"], r["free"]), ("F(x)", ["y"]))
        # a variable that cancels does not count: v - v
        self.assertEqual(classify("v - v + x")["case"], "F(x)")

    def test_refusals(self):
        with self.assertRaises(Refusal) as c:
            classify("x(x + 1)")
        self.assertEqual(c.exception.code, "bad-term")
        with self.assertRaises(Refusal):
            classify("x", t="x")

    def test_route(self):
        code, body = api.handle("POST", "/classify", {"force": "-b*v"})
        self.assertEqual((code, body["case"]), (200, "F(v)"))
        code, body = api.handle("POST", "/classify", {"force": "1 +"})
        self.assertEqual(body["refusal"]["code"], "bad-term")


if __name__ == "__main__":
    unittest.main()
