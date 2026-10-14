"""AUTOSIMPL.md (p1_expected E162): the cases table, sentence for sentence,
through /session and /tactic, and the work file's replay of a chain."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import autosimpl  # noqa: E402
import script  # noqa: E402
import work  # noqa: E402
from session import K, loader  # noqa: E402

S1 = "problem stage0.S1."
S2 = "problem stage0.S2."
S3 = "problem stage0.S3."
L6 = "goal Int[x = 0 .. 1] sqrt(x + 1) == ?A."
FTC2 = "ftc exp(x^2)/2 by ring."
CASE1 = ["rewrite exp_one at exp(1^2).", "rewrite exp_zero at exp(0^2).",
         "close (1/2)*e_const - 1/2 by ring."]


def run(header, sentences):
    """(the session, the last response, every response) for `sentences`
    fed in order from n0, each from the node the previous one made."""
    s, n = api.handle("POST", "/session", {"header": header})
    assert s == 200 and "session" in n, n
    node, out = "n0", []
    for text in sentences:
        s, r = api.handle("POST", "/tactic", {"session": n["session"],
                                              "node": node, "text": text})
        assert s == 200, r
        out.append(r)
        node = r.get("node", node)
    return n["session"], out[-1] if out else n, out


class Cases(unittest.TestCase):
    """AUTOSIMPL.md's table; the case number is the table's."""

    def chain(self, num, header, sentences, auto, report="Proved."):
        with self.subTest(case=num):
            _, r, _ = run(header, sentences)
            self.assertNotIn("refusal", r)
            self.assertEqual(r["auto"], auto)
            self.assertIsNone(r["auto_stopped"])
            self.assertEqual(r["report"], report)
            self.assertEqual(r["admissions"], 0)

    def test_chains(self):
        self.chain(1, S2, [FTC2], CASE1)
        self.chain(2, S1, ["ftc x^3 + x^2 by ring."], ["close 2 by ring."])
        self.chain(3, S3, ["ftc (ln x)^2/2 by ring."], [
            "rewrite ln_e at ln e_const.", "rewrite ln_one at ln 1.",
            "close 1/2 by ring."])
        self.chain(4, "goal sqrt(2 + 2) + sqrt(0 + 1) + atan(-1/2) == ?A.",
                   ["simpl."], [
                       "rewrite sqrt_sq with u := 2 at sqrt(2 + 2).",
                       "rewrite sqrt_sq with u := 1 at sqrt(0 + 1).",
                       "rewrite atan_odd with u := 1/2 at atan(-1/2).",
                       "close -atan(1/2) + 3 by ring."])
        self.chain(5, "goal exp(ln 2) + (sqrt 3)^2 + (sin 1)^2 + (cos 1)^2"
                      " == ?A.", ["simpl."], [
                          "rewrite exp_ln with u := 2 at exp(ln 2).",
                          "rewrite sqrt_sq_val with a := 3 at (sqrt 3)^2.",
                          "fact auto1 := pyth_cos with u := 1.",
                          "close 6 by field using auto1."])
        self.chain(6, "goal sqrt 2 * sqrt 2 == ?A.", ["simpl."], [
            "fact auto1 := sqrt_sq_val with a := 2.",
            "close 2 by field using auto1."])
        self.chain(7, "goal 2^(1/2 + 1/2) == ?A.", ["simpl."], [
            "rewrite rpow_int with u := 2; n := 1 at 2^(1/2 + 1/2).",
            "close 2 by ring."])
        self.chain(12, S2, ["Unset Auto Simpl.", "Set Auto Simpl.", FTC2],
                   CASE1)
        self.chain(13, L6, ["fact h := sqrt_sq_val with a := x + 1.",
                            "ftc (2/3)*(x + 1)*sqrt(x + 1) by field using h."],
                   ["rewrite sqrt_sq with u := 1 at sqrt(0 + 1).",
                    "close (4/3)*sqrt 2 - 2/3 by ring."])

    def test_8_a_chain_that_would_admit_stops(self):
        _, r, _ = run("goal sqrt((pi - 4)^2) == ?A.", ["simpl."])
        self.assertEqual(r["refusal"]["code"], "simpl-stopped")
        self.assertIn("admitted", r["refusal"]["message"])

    def test_8_after_a_move_the_goal_is_left_as_the_move_left_it(self):
        goal = "goal Int[x = 0 .. 1] 2*(x - 4)*sqrt((pi - 4)^2) == ?A."
        move = "ftc (x - 4)^2*sqrt((pi - 4)^2) by ring."
        _, r, _ = run(goal, [move])
        _, off, _ = run(goal, ["Unset Auto Simpl.", move])
        self.assertNotIn("refusal", r)
        self.assertEqual(r["auto"], [])
        self.assertIn("admitted", r["auto_stopped"])
        self.assertEqual((r["goal"], r["admissions"]),
                         (off["goal"], off["admissions"]))

    def test_9_and_10_off(self):
        _, r, _ = run(S2, ["Unset Auto Simpl.", FTC2])
        self.assertEqual((r["goal"], r["auto"], r["auto_simpl"]),
                         ("exp(1^2)/2 - exp(0^2)/2 == ?A", [], False))
        _, r, _ = run(S2, ["Unset Auto Simpl.", FTC2, "simpl."])
        self.assertEqual(r["refusal"]["code"], "close-not-evaluated")
        self.assertIn("(exp_one)", r["refusal"]["message"])

    def test_11_a_move_after_the_chain_closed_the_goal(self):
        _, r, _ = run(S2, [FTC2, "simpl."])
        self.assertEqual(r["refusal"]["code"], "proof-finished")
        self.assertIn("Unset Auto Simpl.", r["refusal"]["message"])

    def test_14_a_pre_E162_document_replays_with_it_off(self):
        sid, r, _ = run(S2, ["Unset Auto Simpl.", FTC2, *CASE1[:2], "simpl."])
        self.assertEqual(r["report"], "Proved.")
        doc = work.document(api.SESSIONS[sid])
        # as saved before E162: no setting, no set node, simpl's close
        set_node = doc["nodes"][0]
        self.assertEqual(set_node["move"], "set")
        del doc["auto_simpl"]
        doc["nodes"] = [dict(n, parent="n0") if n["parent"] == set_node["node"]
                        else n for n in doc["nodes"][1:]]
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual(s, 200, out)
        self.assertFalse(out["auto_simpl"])
        self.assertEqual(out["resumed"]["dropped"], [])
        s, t = api.handle("GET", "/tree", {"session": out["session"]})
        self.assertEqual(t["nodes"][-1]["report"], "Proved.")


class ReferenceProofs(unittest.TestCase):
    def test_every_reference_proof_reaches_its_verdict_with_it_on(self):
        """Each problem file's proof, through /tactic with auto-simpl on:
        the typed steps after the chain closed the goal are skipped, and
        the verdict is the reference's, with no more admissions."""
        n_auto = 0
        for pid, (p, _, _) in api._problem_files().items():
            for name, steps in p.proofs.items():
                results, _ = loader.replay(p, name)
                if isinstance(results[-1][1], K.Refusal):
                    continue  # a proof that ends refused, by design
                want = results[-1][1]
                with self.subTest(pid=pid, proof=name):
                    s, n = api.handle("POST", "/session", {"problem": pid})
                    for st in steps:
                        if n.get("goal") is None and n.get("auto"):
                            n_auto += 1
                            break
                        s, n = api.handle("POST", "/tactic", {
                            "session": n["session"], "node": n["node"],
                            "text": script.show(st["move"], st["args"])})
                        self.assertNotIn("refusal", n)
                    adm = sum(o.status == K.ADMITTED
                              for o in want.obligations())
                    self.assertLessEqual(n["admissions"], adm)
                    self.assertEqual(n["report"].split(" modulo")[0],
                                     K.report(want).split(" modulo")[0])
        self.assertGreater(n_auto, 5)


class Setting(unittest.TestCase):
    def test_set_is_a_node_without_a_kernel_move_and_not_a_rule(self):
        _, r, out = run(S2, ["Unset Auto Simpl."])
        self.assertEqual((r["move"], r["auto_simpl"], r["steps"]),
                         ("set", False, 0))
        self.assertEqual(r["goal"], out[0]["goal"])

    def test_retracting_the_set_restores_the_setting(self):
        sid, r, _ = run(S2, ["Unset Auto Simpl."])
        s, back = api.handle("POST", "/retract", {"session": sid,
                                                  "node": r["node"]})
        self.assertTrue(back["auto_simpl"])

    def test_a_fact_never_triggers(self):
        _, r, _ = run("goal sqrt 2 * sqrt 2 == ?A.",
                      ["fact h := sqrt_sq_val with a := 2."])
        self.assertEqual((r["auto"], r["auto_stopped"]), ([], None))
        self.assertIn("?A", r["goal"])

    def test_install_never_triggers(self):
        _, r, _ = run("goal exp 1 == ?A.", [])
        self.assertEqual(r["goal"], "exp 1 == ?A")

    def test_typed_simpl_records_simpl(self):
        sid, r, _ = run("goal exp 1 == ?A.", ["simpl."])
        s, t = api.handle("GET", "/tree", {"session": sid})
        self.assertEqual(t["nodes"][-1]["move"], "simpl")
        self.assertEqual(r["auto"], ["rewrite exp_one at exp 1.",
                                     "close e_const by ring."])


class Persistence(unittest.TestCase):
    def test_a_chain_is_saved_and_replayed_exactly(self):
        sid, r, _ = run(S2, [FTC2])
        doc = work.document(api.SESSIONS[sid])
        self.assertTrue(doc["auto_simpl"])
        self.assertEqual([a["move"] for a in doc["nodes"][0]["auto"]],
                         ["rewrite", "rewrite", "close"])
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual(out["resumed"]["dropped"], [])
        s, n = api.handle("GET", "/node", {"session": out["session"],
                                           "node": "n1"})
        self.assertEqual((n["report"], n["auto"]), ("Proved.", CASE1))

    def test_a_recorded_chain_is_not_recomputed(self):
        """A valid chain other than the one auto-simpl would compute
        replays as recorded: here a close naming the value another way."""
        sid, r, _ = run(S2, [FTC2])
        doc = work.document(api.SESSIONS[sid])
        doc["nodes"][0]["auto"][-1]["args"]["value"] = "(e_const - 1)/2"
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual(out["resumed"]["dropped"], [])
        s, n = api.handle("GET", "/node", {"session": out["session"],
                                           "node": "n1"})
        self.assertEqual((n["report"], n["auto"][-1]),
                         ("Proved.", "close (e_const - 1)/2 by ring."))

    def test_a_chain_that_no_longer_replays_drops_its_node(self):
        sid, r, _ = run(S2, [FTC2])
        doc = work.document(api.SESSIONS[sid])
        doc["nodes"][0]["auto"][0]["args"]["entry"] = "ln_one"
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual([d["code"] for d in out["resumed"]["dropped"]],
                         ["auto-replay"])


class Review(unittest.TestCase):
    """E164: the review's findings, each pinned."""

    def test_an_exception_in_the_chain_stops_it_and_the_move_stands(self):
        _, r, _ = run("goal 2^100000 + sin 0 == ?A.",
                      ["rewrite sin_zero at sin 0."])
        self.assertNotIn("refusal", r)
        self.assertIn("power-too-large", r["auto_stopped"])
        _, r, _ = run("goal 2^100000 == ?A.", ["simpl."])
        self.assertEqual(r["refusal"]["code"], "simpl-stopped")

    def tampered(self, header_body, sentences, change):
        sid, r, _ = run(S2 if header_body is None else header_body, sentences)
        doc = work.document(api.SESSIONS[sid])
        change(doc["nodes"])
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual(s, 200, out)
        return [d["code"] for d in out["resumed"]["dropped"]]

    def test_replay_holds_a_chain_to_the_live_rules(self):
        admit = [{"move": "rewrite", "args": {
            "entry": "sqrt_sq", "inst": {"u": "pi - 4"},
            "at": "sqrt((pi - 4)^2)"}}]
        goal = "goal Int[x = 0 .. 1] 2*(x - 4)*sqrt((pi - 4)^2) == ?A."
        move = "ftc (x - 4)^2*sqrt((pi - 4)^2) by ring."
        self.assertEqual(self.tampered(goal, [move], lambda ns: ns[0].update(
            auto=admit)), ["auto-replay"])
        # partial: the first rewrite of case 1 alone leaves the goal open
        self.assertEqual(self.tampered(None, [FTC2], lambda ns: ns[0].update(
            auto=ns[0]["auto"][:1])), ["auto-replay"])
        # a technique inside the chain
        self.assertEqual(self.tampered(None, [FTC2], lambda ns: ns[0].update(
            auto=[{"move": "int_flip", "args": {}}])), ["auto-replay"])
        # a chain where the setting is off
        self.assertEqual(self.tampered(None, ["Unset Auto Simpl.", FTC2],
                                       lambda ns: ns[1].update(
            auto=[{"move": "close", "args": {"value": "1", "check": "ring",
                                             "facts": []}}])),
            ["auto-replay"])
        # a typed simpl with its chain removed
        self.assertEqual(self.tampered("goal exp 1 == ?A.", ["simpl."],
                                       lambda ns: ns[0].pop("auto")),
                         ["auto-replay"])

    def test_raw_step_simpl_keeps_simpls_own_checks(self):
        s, n = api.handle("POST", "/session", {"goal": "x + 1 == ?A @ x > 0",
                                               "functions": {}})
        for args in ({}, {"facts": 5}, {"bogus": 1}):
            with self.subTest(args=args):
                s, r = api.handle("POST", "/step", {
                    "session": n["session"], "node": "n0", "move": "simpl",
                    "args": args})
                self.assertEqual((s, r["refusal"]["code"]), (200, "bad-args"))

    def test_proof_finished_after_a_typed_simpl_and_for_set(self):
        _, r, _ = run("goal exp 1 == ?A.", ["simpl.", "close 1."])
        self.assertEqual(r["refusal"]["code"], "proof-finished")
        self.assertNotIn("Unset Auto Simpl", r["refusal"]["message"])
        _, r, _ = run(S2, [FTC2, "Unset Auto Simpl."])
        self.assertEqual(r["refusal"]["code"], "proof-finished")
        self.assertIn("Unset Auto Simpl", r["refusal"]["message"])
        _, r, _ = run(S2, ["Unset Auto Simpl.", FTC2, *CASE1[:2],
                           "simpl.", "simpl."])
        self.assertEqual(r["refusal"]["code"], "proof-finished")

    def test_rpow_in_the_editors(self):
        s, r = api.handle("POST", "/untex", {
            "latex": r"\operatorname{rpow}\left(2, 1\right) + 1"})
        self.assertEqual(r["term"], "rpow(2, 1) + 1")
        s, n = api.handle("POST", "/session", {"goal": "rpow(2, 1) == ?A",
                                               "functions": {},
                                               "auto_simpl": False})
        s, p = api.handle("GET", "/palette", {"session": n["session"],
                                              "node": "n0"})
        self.assertIn("rewrite rpow_int with u := 2; n := 1 at rpow(2, 1).",
                      [x["sentence"] for x in p["rewrites"]])
        # the KaTeX form reads back as the same node (the generators of
        # test_tex never built one while D17 refused it)
        for text in ("rpow(2, 1)", "rpow(x, -1)^2 + 1", "sin(rpow(2, 0))"):
            s, r = api.handle("POST", "/parse", {"text": text})
            s, back = api.handle("POST", "/untex", {"latex": r["katex"]})
            self.assertEqual(back["term"], r["term"], text)


class Redexes(unittest.TestCase):
    def test_the_first_redex_is_the_one_E27_names(self):
        """AUTOSIMPL.md: the chain makes the moves E27 would name, in
        E27's order. For values E27 refuses under (a) with a rewritable
        redex, the chain's first rewrite is at E27's subterm, by its
        entry."""
        import schema
        from terms import parse_term
        for text in ("exp 1 + ln 1", "sqrt 4 * atan(-1)", "cos(pi/2) + sin 0",
                     "exp(ln 3) + exp 0", "2^(1/2 + 1/2) + ln e_const",
                     "sqrt(9) - sqrt 0"):
            with self.subTest(text=text):
                t = parse_term(text)
                clause, at, entry = schema.evaluated_offence(t)
                name, got, _ = next(autosimpl.redexes(t))
                self.assertEqual((clause, name, got), ("a", entry, at))

    def test_bounds(self):
        self.assertEqual((autosimpl.MAX_REWRITES, autosimpl.MAX_FACTS),
                         (32, 8))


if __name__ == "__main__":
    unittest.main()
