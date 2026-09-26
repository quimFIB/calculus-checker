"""EVAL.md's Done-when: SymPy proposes, the kernel proves.

The SymPy cases need a Python that has SymPy: $CALC_SYMPY, else python3.
Without one they are skipped; the no-proposer answer, the soundness of the
checker against a lying proposal, and the process handling are tested
either way."""

import json
import os
import stat
import sys
import tempfile
import threading
import time
import unittest
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import server  # noqa: E402
import work  # noqa: E402
from assist import integrate  # noqa: E402

PY = integrate.find_python()


def fake_python(seconds):
    """An executable that stands in for SymPy's Python and is slow."""
    d = tempfile.mkdtemp()
    p = os.path.join(d, "slowpy")
    with open(p, "w") as f:
        f.write(f"#!/bin/sh\nsleep {seconds}\necho '{{}}'\n")
    os.chmod(p, os.stat(p).st_mode | stat.S_IEXEC)
    integrate._HAS[p] = True
    return p


def ev(body, proposer=None):
    status, r = integrate.evaluate(api.handle, proposer or
                                   integrate.Proposer(PY, 30), body)
    assert status == 200, r
    return r


def replay(goal, sentences, sig=None):
    s = api.handle("POST", "/session", {"goal": goal,
                                        "functions": sig or {}})[1]
    nid = s["node"]
    for t in sentences:
        r = api.handle("POST", "/tactic", {"session": s["session"],
                                           "node": nid, "text": t})[1]
        assert "refusal" not in r, (t, r)
        nid = r["node"]
    return r["report"]


class Checker(unittest.TestCase):
    """The kernel's half, against proposals written by hand."""

    def check(self, term, proposal):
        return api.handle("POST", "/evaluate/check",
                          {"term": term, "proposal": proposal})[1]

    def test_a_right_proposal_is_proved(self):
        r = self.check("Int[x = 0 .. 1] 3*x^2 + 2*x",
                       {"status": "ok", "shapes": ["x^3 + x^2"],
                        "value": "2"})
        self.assertEqual((r["status"], r["value"]), ("proved", "2"))
        self.assertEqual(r["sentences"], ["ftc x^3 + x^2 by ring.",
                                          "close 2 by ring."])

    def test_a_lying_proposal_is_never_proved(self):
        r = self.check("Int[x = 0 .. 1] 3*x^2 + 2*x",
                       {"status": "ok", "shapes": ["x^3"], "value": "5"})
        self.assertEqual(r["status"], "unverified")
        self.assertEqual(r["refusal"]["code"], "ftc-check-failed")
        self.assertFalse(r["antiderivative_checked"])
        # a right F with a wrong value: F is checked, the value is not
        r = self.check("Int[x = 0 .. 1] 3*x^2 + 2*x",
                       {"status": "ok", "shapes": ["x^3 + x^2"],
                        "value": "5"})
        self.assertEqual(r["status"], "unverified")
        self.assertTrue(r["antiderivative_checked"])
        self.assertEqual(r["value"], "5")  # shown as SymPy's claim only

    def test_a_malformed_proposal_is_refused_at_parse(self):
        r = self.check("Int[x = 0 .. 1] x",
                       {"status": "ok", "shapes": ["this is ((("],
                        "value": "1/2"})
        self.assertEqual(r["status"], "outside-grammar")
        self.assertIn("did not parse", r["message"])

    def test_not_an_integral_goal(self):
        s = api.handle("POST", "/session", {"goal": "sin(pi/2) == ?A"})[1]
        r = ev({"session": s["session"], "node": "n0"},
               integrate.Proposer(None))
        self.assertEqual(r["status"], "not-an-integral-goal")

    def test_no_proposer(self):
        r = ev({"term": "Int[x = 0 .. 1] x"}, integrate.Proposer(None))
        self.assertEqual(r["status"], "no-proposer")
        self.assertIn("--sympy", r["message"])
        self.assertAlmostEqual(r["numeric"]["value"], 0.5)

    def test_a_refused_goal(self):
        r = ev({"term": "Int[x = -1 .. 1] 1/x^2"}, integrate.Proposer(None))
        self.assertEqual(r["status"], "refused-goal")
        self.assertIn("obligation-decided-false", r["message"])

    def test_the_scratch_goal_takes_no_work_file(self):
        """Review 4: evaluating the learner's own goal as a term must not
        take save ownership from the learner's session."""
        old = api.WORK_DIR
        api.WORK_DIR = tempfile.mkdtemp()
        try:
            s = api.handle("POST", "/session", {"problem": "stage0.S1"})[1]
            key = s["key"]
            self.check("Int[x = 0 .. 1] 3*x^2 + 2*x",
                       {"status": "ok", "shapes": ["x^3 + x^2"],
                        "value": "2"})
            self.assertEqual(api.OWNER[key], s["session"])
            self.assertNotIn("scratch", api.SESSIONS)
        finally:
            api.WORK_DIR = old

    def test_evaluations_are_recorded(self):
        old = api.WORK_DIR
        api.WORK_DIR = tempfile.mkdtemp()
        try:
            s = api.handle("POST", "/session", {"problem": "stage0.S1"})[1]
            api.handle("POST", "/evaluate/check", {
                "session": s["session"], "node": "n0",
                "proposal": {"status": "ok", "shapes": ["x^3 + x^2"],
                             "value": "2"}})
            t = api.handle("GET", "/tree", {"session": s["session"]})[1]
            self.assertEqual(len(t["evaluations"]), 1)
            self.assertEqual(t["evaluations"][0]["status"], "proved")
            doc = work.read(api.WORK_DIR, s["key"])
            self.assertEqual(doc["evaluations"][0]["sentences"],
                             ["ftc x^3 + x^2 by ring.", "close 2 by ring."])
            # nothing was added to the tree
            self.assertEqual(len(t["nodes"]), 1)
        finally:
            api.WORK_DIR = old


class Process(unittest.TestCase):
    def test_the_time_limit_kills_the_proposer(self):
        p = integrate.Proposer(fake_python(30), timeout=1)
        t = time.time()
        r = ev({"term": "Int[x = 0 .. 1] x"}, p)
        self.assertLess(time.time() - t, 5)
        self.assertEqual(r["status"], "not-found")
        self.assertIn("within 1 s", r["message"])

    def test_cancel_kills_the_proposer(self):
        p = integrate.Proposer(fake_python(30), timeout=60)
        out = {}
        th = threading.Thread(target=lambda: out.update(
            ev({"term": "Int[x = 0 .. 1] x"}, p)))
        th.start()
        while p.proc is None:
            time.sleep(0.05)
        self.assertTrue(p.cancel())
        th.join(10)
        self.assertEqual(out["status"], "cancelled")

    def test_the_server_steps_while_sympy_thinks(self):
        """Review 5: the proposer runs outside the worker; /cancel stops
        it; a step meanwhile is answered at once."""
        old_b, old_p = server.BACKEND, server.PROPOSER
        server.PROPOSER = integrate.Proposer(fake_python(30), timeout=60)
        srv = server.ThreadingHTTPServer(("127.0.0.1", 0), server.Handler)
        srv.verbose = False
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        base = f"http://127.0.0.1:{srv.server_address[1]}"

        def post(path, body):
            req = urllib.request.Request(
                base + path, json.dumps(body).encode(),
                {"Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.load(r)
        try:
            out = {}
            th = threading.Thread(target=lambda: out.update(post(
                "/evaluate", {"term": "Int[x = 0 .. 1] x"})))
            th.start()
            while server.PROPOSER.proc is None:
                time.sleep(0.05)
            t = time.time()
            s = post("/session", {"problem": "stage0.S1"})
            n = post("/tactic", {"session": s["session"], "node": "n0",
                                 "text": "ftc x^3 + x^2 by ring."})
            self.assertEqual(n["node"], "n1")
            self.assertLess(time.time() - t, 5)
            self.assertTrue(post("/cancel", {})["cancelled"])
            th.join(10)
            self.assertEqual(out["status"], "cancelled")
        finally:
            srv.shutdown()
            srv.server_close()
            server.BACKEND, server.PROPOSER = old_b, old_p


@unittest.skipIf(PY is None, "no Python with SymPy ($CALC_SYMPY)")
class WithSympy(unittest.TestCase):
    def test_s1(self):
        r = ev({"term": "Int[x = 0 .. 1] 3*x^2 + 2*x"})
        self.assertEqual((r["status"], r["value"]), ("proved", "2"))
        self.assertEqual(replay("Int[x = 0 .. 1] 3*x^2 + 2*x == ?A",
                                r["sentences"]), "Proved.")

    def test_p1_2_and_the_rewrite_planner(self):
        for term, value in (
                ("Int[x = 0 .. 1] 1/(1 + x^3)", "ln 2 / 3 + sqrt 3 * pi/9"),
                ("Int[x = 0 .. 1] exp x", "-1 + e_const"),
                ("Int[x = 0 .. pi] sin x", "2"),
                ("Int[x = -2 .. -1] 1/x", "-ln 2")):
            with self.subTest(term):
                r = ev({"term": term})
                self.assertEqual((r["status"], r["value"]),
                                 ("proved", value), r)
                self.assertEqual(replay(term + " == ?A", r["sentences"]),
                                 "Proved.")
        r = ev({"term": "Int[x = 0 .. 1] 1/(1 + x^3)"})
        self.assertIn("rewrite atan_odd with u := -((2*0 - 1)/sqrt 3) at "
                      "atan((2*0 - 1)/sqrt 3).", r["sentences"])

    def test_improper(self):
        r = ev({"term": "Int[x = 0 .. oo] exp(-x)"})
        self.assertEqual((r["status"], r["value"]), ("proved", "1"))
        self.assertTrue(r["sentences"][0].startswith("int_improper"))
        r = ev({"term": "Int[x = -oo .. oo] 1/(1 + x^2)"})
        self.assertEqual((r["status"], r["value"]), ("proved", "pi"))
        self.assertAlmostEqual(r["numeric"]["value"], 3.141592653589793)

    def test_admissions_are_not_proved(self):
        """Review 6: P5 closes only modulo admissions: unverified."""
        r = ev({"term": "Int[x = 0 .. oo] 1/(1 + x^4)"})
        self.assertEqual(r["status"], "unverified")
        self.assertEqual(r["refusal"]["code"], "admissions")
        self.assertEqual(r["value"], "sqrt 2 * pi/4")

    def test_outside_the_grammar(self):
        r = ev({"term": "Int[x = 0 .. 1] exp(-x^2)"})
        self.assertEqual(r["status"], "outside-grammar")
        self.assertIn("erf", r["message"])
        self.assertNotIn("elementary", r["message"])  # §8.2 revision 2
        self.assertAlmostEqual(r["numeric"]["value"], 0.746824132812427)

    def test_maple_is_never_zero(self):
        r = ev({"term": "Int[x = -1 .. 1] sqrt(x^2)"})
        self.assertIn(r["status"], ("outside-grammar", "unverified"))
        self.assertEqual(r["value"], "1")
        self.assertIn("no single antiderivative", r["message"])

    def test_a_declared_function_is_unknown(self):
        r = ev({"term": "Int[x = 0 .. 1] f(x)", "functions": {"f": 1}})
        self.assertEqual(r["status"], "not-found")
        self.assertIn("declared function", r["message"])

    def test_parameters(self):
        s = api.handle("POST", "/session", {
            "goal": "Int[x = 0 .. 1] 1/(x + a) == ?A @ a > 0"})[1]
        r = ev({"session": s["session"], "node": "n0"})
        self.assertEqual(r["status"], "proved", r)
        self.assertIn("ftc ln(a + x)", r["sentences"][0])

    def test_the_goal_of_a_session(self):
        s = api.handle("POST", "/session", {"problem": "stage0.S1"})[1]
        r = ev({"session": s["session"], "node": "n0"})
        self.assertEqual((r["status"], r["node"]), ("proved", "n0"))


if __name__ == "__main__":
    unittest.main()
