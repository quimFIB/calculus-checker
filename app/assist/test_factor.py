"""FACTOR.md Done-when 1: the factoriser and the partial-fraction solver.
Every result is also re-checked here by the kernel's field, independently
of the check factor.py ran."""

import unittest
from unittest import mock

import api
import field as FD
from assist import factor as F
from terms import parse_term


def T(s):
    return parse_term(s, {})


def same(a, b, d=0):
    facts = [(T(f"(sqrt {d})^2"), T(str(d)))] if d else []
    FD.field(T(a), T(b), facts)  # raises unless the kernel agrees
    return True


class Factor(unittest.TestCase):
    def f(self, t, field):
        return F.factor(T(t), "x", field)

    def test_readiness_p1_over_q(self):
        r = self.f("1 + x^3", "Q")
        self.assertEqual([x["term"] for x in r["factors"]],
                         ["x + 1", "x^2 - x + 1"])
        self.assertEqual(r["check"], "ring")
        self.assertEqual([x["irreducible"] for x in r["factors"]],
                         [True, True])

    def test_readiness_p5_over_q_is_left_whole(self):
        r = self.f("1 + x^4", "Q")
        self.assertEqual(r["product"], "x^4 + 1")
        self.assertIn("no further factor", r["note"])
        self.assertIsNone(r["factors"][0]["irreducible"])

    def test_readiness_p5_over_r(self):
        r = self.f("1 + x^4", "R")
        self.assertEqual([x["term"] for x in r["factors"]],
                         ["x^2 - sqrt 2 * x + 1", "x^2 + sqrt 2 * x + 1"])
        self.assertEqual(r["check"], "field using sqrt_sq_val with a := 2")
        self.assertTrue(same("1 + x^4", r["product"], 2))

    def test_a_real_quadratic(self):
        r = self.f("x^2 - 2", "R")
        self.assertEqual(r["product"], "(x - sqrt 2)*(x + sqrt 2)")
        self.assertIsNone(self.f("x^2 - 2", "Q")["note"])
        self.assertEqual(self.f("x^2 - 2", "Q")["factors"][0]["irreducible"],
                         True)

    def test_roots_powers_content_and_quartics(self):
        for t, want in [("x^3 - x^2", "(x - 1)*x^2"),
                        ("2*x^2 - 2", "2*(x - 1)*(x + 1)"),
                        ("x^4 + x^2 + 1", "(x^2 - x + 1)*(x^2 + x + 1)"),
                        ("x^4 + 4", "(x^2 - 2*x + 2)*(x^2 + 2*x + 2)"),
                        ("(x - 1/2)^2*(x + 3)", "(x - 1/2)^2*(x + 3)"),
                        ("4*x^4 + 1", "4*(x^2 - x + 1/2)*(x^2 + x + 1/2)")]:
            r = self.f(t, "Q")
            self.assertEqual(r["product"], want, t)
            self.assertTrue(same(t, r["product"]))

    def test_one_radical_at_a_time(self):
        r = self.f("x^4 - 5*x^2 + 6", "R")
        self.assertEqual(r["product"], "(x - sqrt 3)*(x + sqrt 3)*(x^2 - 2)")
        self.assertIn("one radical at a time", r["note"])
        r = self.f("x^4 - x^2 + 1", "R")  # s = +1: √3
        self.assertEqual(r["product"],
                         "(x^2 - sqrt 3 * x + 1)*(x^2 + sqrt 3 * x + 1)")

    def test_a_vacuous_field_check_is_refused(self):
        """field accepts 1/(1+x^4) = 2/(1+x^4) through a divisor that is
        zero modulo (√2)² = 2; check() must not."""
        with self.assertRaises(F.Refusal) as e:
            F.check(T("1/(1 + x^4)"),
                    T("2*((sqrt 2)^2 - 2)/(((sqrt 2)^2 - 2)*(1 + x^4))"), 2,
                    quotients=True)
        self.assertEqual(e.exception.code, "unchecked")

    def test_a_rational_function_factors_its_denominator(self):
        r = self.f("1/(1 + x^3)", "Q")
        self.assertEqual((r["of"], r["product"]),
                         ("denominator", "(x + 1)*(x^2 - x + 1)"))


class Apart(unittest.TestCase):
    def a(self, t, field, ansatz=None):
        r = F.apart(T(t), "x", field, ansatz)
        self.assertTrue(same(t, r["sum"], 2 if "sqrt" in r["sum"] else 0))
        return r

    def test_readiness_p1(self):
        r = self.a("1/(1 + x^3)", "Q")
        self.assertEqual(r["terms"], ["(1/3)/(x + 1)",
                                      "((-1/3)*x + 2/3)/(x^2 - x + 1)"])
        self.assertEqual(r["check"], "field")

    def test_readiness_p5(self):
        r = self.a("1/(1 + x^4)", "R")
        self.assertEqual(r["terms"], [
            "((-1/4)*sqrt 2 * x + 1/2)/(x^2 - sqrt 2 * x + 1)",
            "((1/4)*sqrt 2 * x + 1/2)/(x^2 + sqrt 2 * x + 1)"])
        with self.assertRaises(F.Refusal) as e:
            F.apart(T("1/(1 + x^4)"), "x", "Q")
        self.assertEqual(e.exception.code, "not-split")

    def test_a_repeated_factor_and_a_polynomial_part(self):
        r = self.a("1/(x^2*(x - 1))", "Q")
        self.assertEqual(len(r["terms"]), 3)
        r = self.a("(x^3 + 1)/(x - 1)", "Q")
        self.assertEqual(r["polynomial"], "x^2 + x + 1")
        self.assertEqual(r["terms"], ["2/(x - 1)"])

    def test_the_learners_ansatz(self):
        good = [{"den": "x", "numerator": "constant"},
                {"den": "x^2", "numerator": "constant"},
                {"den": "x - 1", "numerator": "constant"}]
        self.a("1/(x^2*(x - 1))", "Q", good)
        with self.assertRaises(F.Refusal) as e:
            F.apart(T("1/(x^2*(x - 1))"), "x", "Q", good[::2])
        self.assertEqual(e.exception.code, "no-solution")

    def test_not_rational(self):
        for t in ("sin x", "sqrt x/(1 + x)", "pi/(1 + x^2)"):
            with self.assertRaises(F.Refusal) as e:
                F.apart(T(t), "x", "Q")
            self.assertEqual(e.exception.code, "not-rational", t)
        with self.assertRaises(F.Refusal) as e:
            F.apart(parse_term("1/(x^2 + k)", {}), "x", "Q")
        self.assertEqual(e.exception.code, "not-rational")

    def test_a_wrong_factor_is_never_shown(self):
        """A planted bug: the quartic search answers a wrong split. The
        kernel's check refuses it, so the answer is `unchecked`."""
        wrong = ([F.QD(1), F.QD(1), F.QD(1)], [F.QD(1), F.QD(-1), F.QD(2)])
        with mock.patch.object(F, "_quartic_q", return_value=wrong):
            with self.assertRaises(F.Refusal) as e:
                F.factor(T("x^4 + x^2 + 1"), "x", "Q")
        self.assertEqual(e.exception.code, "unchecked")


class Routes(unittest.TestCase):
    """FACTOR.md Done-when 2."""

    def test_factor_and_apart_on_p5(self):
        s, r = api.handle("POST", "/apart", {"term": "1/(1 + x^4)",
                                             "var": "x", "field": "R"})
        self.assertEqual(s, 200)
        self.assertIn(r"\sqrt{2}", r["sum_tex"])
        s, r = api.handle("POST", "/factor", {"term": "1/(1 + x^4)",
                                              "var": "x", "field": "Q"})
        self.assertIn("no further factor", r["note"])
        s, r = api.handle("POST", "/apart", {"term": "1/(1 + x^4)",
                                             "var": "x", "field": "Q"})
        self.assertEqual(r["refusal"]["code"], "not-split")
        s, r = api.handle("POST", "/apart", {"term": "1/(1 + x^4)",
                                             "var": "x", "field": "C"})
        self.assertEqual(s, 400)

    def test_the_palette_offers_the_tools_on_p5(self):
        sid = api.handle("POST", "/session", {"problem": "improper.P5"})[1][
            "session"]
        pl = api.handle("GET", "/palette", {"session": sid, "node": "n0"})[1]
        self.assertEqual(pl["rational"], {"term": "1/(1 + x^4)", "var": "x"})
        sid = api.handle("POST", "/session", {"problem": "trig.COS_SQ"})[1][
            "session"]
        pl = api.handle("GET", "/palette", {"session": sid, "node": "n0"})[1]
        self.assertIsNone(pl["rational"])
        sid = api.handle("POST", "/session", {"problem": "stage0.S1"})[1][
            "session"]  # a polynomial integrand: nothing to split
        pl = api.handle("GET", "/palette", {"session": sid, "node": "n0"})[1]
        self.assertIsNone(pl["rational"])


if __name__ == "__main__":
    unittest.main()
