"""STUCK.md: the three kinds of stuck, on §8.7's own examples, and every
suggestion replayed through /tactic."""

import unittest

import api


class Stuck(unittest.TestCase):
    def session(self, goal, sig=None):
        s = api.handle("POST", "/session", {"goal": goal, "sig": sig or {}})[1]
        return s["session"], s["node"]

    def tactic(self, sid, node, text):
        return api.handle("POST", "/tactic",
                          {"session": sid, "node": node, "text": text})[1]

    def refused(self, goal, text, code, kind):
        """The stuck object of `text` refused at the root of `goal`, after
        replaying its suggestion, if any, and requiring it accepted."""
        sid, node = self.session(goal)
        r = self.tactic(sid, node, text)
        self.assertEqual(r["refusal"]["code"], code, r)
        st = r["refusal"]["stuck"]
        self.assertEqual(st["kind"], kind, st)
        for sentence in st["suggest"] or ():
            got = self.tactic(sid, node, sentence)
            self.assertNotIn("refusal", got, (sentence, got))
            node = got["node"]
        return st

    # ------------------------------------------------ §8.7's own examples

    def test_sqrt_sq_over_a_negative_range_is_an_obligation(self):
        st = self.refused("Int[t = -1 .. 0] sqrt(t^2) == ?A",
                          "rewrite sqrt_sq with u := t at sqrt(t^2).",
                          "obligation-decided-false", "obligation")
        self.assertIn("t = -1", st["lines"][0])
        self.assertIn("hypothesis", st["lines"][1])
        self.assertIsNone(st["suggest"])

    def test_antiderivative_off_by_a_factor(self):
        st = self.refused("Int[t = 0 .. pi] 2*t*sin t == ?A",
                          "ftc sin t - t*cos t.", "ftc-check-failed",
                          "algebra")
        self.assertEqual(st["headline"], "D[t] F − integrand = -t*sin t")
        self.assertIn("1/2 times the integrand", st["lines"][0])
        self.assertEqual(st["suggest"], ["ftc 2*(sin t - t*cos t) by ring."])

    def test_a_right_surd_is_not_a_slip(self):
        st = self.refused("pi*sqrt 3/9 == ?A", "close pi/(3*sqrt 3).",
                          "close-check-failed", "algebra")
        self.assertIn("sqrt_sq_val", st["lines"][0])
        self.assertEqual(st["suggest"],
                         ["fact h := sqrt_sq_val with a := 3.",
                          "close pi/(3*sqrt 3) by field using h."])

    def test_a_right_trig_value_names_pyth_cos(self):
        st = self.refused("(sin x)^2 + (cos x)^2 == ?A @ x in [0, 1]",
                          "close 1.", "close-check-failed", "algebra")
        self.assertIn("pyth_cos", st["lines"][0])
        self.assertEqual(st["suggest"][-1], "close 1 by field using h.")

    def test_a_wrong_rewrite_target_is_no_match(self):
        st = self.refused("Int[t = 0 .. pi] 2*t*sin t == ?A",
                          "rewrite sin_zero at t.", "rewrite-lhs-mismatch",
                          "no-match")
        self.assertEqual(st["headline"], "No rule matches here")
        self.assertTrue(any(s.startswith("Moves whose shape fits: ftc")
                            for s in st["lines"]))
        self.assertTrue(any(s.startswith("For Int[t = 0 .. pi]")
                            for s in st["lines"]))
        self.assertEqual(st["lines"][-1], "? for a nudge.")

    # ------------------------------------------------ the rest

    def test_a_rewrite_at_the_wrong_spelling_suggests_the_match(self):
        st = self.refused("Int[t = 0 .. 1] sqrt(t^2) == ?A",
                          "rewrite sin_zero at sqrt(t^2).",
                          "rewrite-lhs-mismatch", "no-match")
        self.assertEqual(st["lines"][0], "At sqrt(t^2), what matches: "
                         "sqrt_sq.")
        self.assertEqual(st["suggest"],
                         ["rewrite sqrt_sq with u := t at sqrt(t^2)."])

    def test_two_matches_suggest_neither(self):
        st = self.refused("sin(2*(pi/2)) + sin 0 == ?A",
                          "rewrite sin_pi at sin 0.",
                          "rewrite-lhs-mismatch", "no-match")
        self.assertEqual(st["lines"][0],
                         "At sin 0, what matches: sin_zero; sin_odd.")
        self.assertIsNone(st["suggest"])

    def test_a_constant_off_is_named_without_a_suggestion(self):
        st = self.refused("Int[t = 0 .. pi] 2*t*sin t == ?A",
                          "ftc -2*t*cos t + 2*sin t + 3*t.",
                          "ftc-check-failed", "algebra")
        self.assertIn("the constant 3", st["lines"][0])
        self.assertIn("3*t", st["lines"][0])
        self.assertIsNone(st["suggest"])

    def test_otherwise_where_they_diverge(self):
        st = self.refused("Int[t = 0 .. pi] 2*t*sin t == ?A", "ftc t^2.",
                          "ftc-check-failed", "algebra")
        self.assertTrue(st["lines"][0].startswith("Where they diverge"))
        self.assertEqual(st["lines"][0].count("≈"), 6)

    def test_a_wrong_value_shows_both_numbers(self):
        st = self.refused("pi*sqrt 3/9 == ?A", "close 2.",
                          "close-check-failed", "algebra")
        self.assertEqual(st["headline"],
                         "The goal's side − your value = "
                         "(1/9)*pi*sqrt 3 - 2")
        self.assertIn("≈ 0.6046", st["lines"][0])

    def test_an_infinite_end_names_int_improper(self):
        st = self.refused("Int[x = 0 .. oo] exp(-x) == ?A", "ftc -exp(-x).",
                          "ftc-infinite-endpoint", "no-match")
        self.assertIn("int_improper", st["lines"][0])

    def test_a_bad_sentence_is_other(self):
        st = self.refused("pi == ?A", "frobnicate.", "bad-tactic", "other")
        self.assertEqual(st, {"kind": "other",
                              "headline": "Refused: bad-tactic",
                              "lines": [], "suggest": None})

    def test_the_fact_name_is_fresh(self):
        sid, node = self.session("pi*sqrt 3/9 == ?A")
        node = self.tactic(sid, node, "fact h := sin_zero.")["node"]
        r = self.tactic(sid, node, "close pi/(3*sqrt 3).")
        st = r["refusal"]["stuck"]
        self.assertEqual(st["suggest"][0],
                         "fact h1 := sqrt_sq_val with a := 3.")
        for sentence in st["suggest"]:
            got = self.tactic(sid, node, sentence)
            self.assertNotIn("refusal", got, got)
            node = got["node"]

    def test_step_refusals_carry_stuck_too(self):
        sid, node = self.session("Int[t = 0 .. pi] 2*t*sin t == ?A")
        r = api.handle("POST", "/step", {
            "session": sid, "node": node, "move": "ftc",
            "args": {"F": "sin t - t*cos t", "check": "ring",
                     "facts": []}})[1]
        self.assertEqual(r["refusal"]["stuck"]["suggest"],
                         ["ftc 2*(sin t - t*cos t) by ring."])

    def test_an_admitting_step_says_so(self):
        sid, node = self.session("Int[t = 0 .. 1] sqrt((cos t - t)^2) == ?A")
        n = self.tactic(sid, node, "rewrite sqrt_sq with u := cos t - t at "
                        "sqrt((cos t - t)^2).")
        st = n["stuck"]
        self.assertEqual((st["kind"], st["headline"]),
                         ("obligation", "Accepted, with 1 admission"))
        self.assertTrue(st["lines"][0].startswith("cos t - t >= 0"))

    def test_a_clean_step_and_the_root_have_none(self):
        sid, node = self.session("Int[t = 0 .. pi] 2*t*sin t == ?A")
        root = api.handle("GET", "/node", {"session": sid, "node": node})[1]
        self.assertIsNone(root["stuck"])
        n = self.tactic(sid, node, "ftc 2*(sin t - t*cos t).")
        self.assertIsNone(n["stuck"])


if __name__ == "__main__":
    unittest.main()
