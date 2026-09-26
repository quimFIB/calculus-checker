"""DX.md Done-when: the header, the REPL, the sentence fixture, and the
Emacs mode's ERT suite (when emacs is installed)."""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import dx  # noqa: E402
import script  # noqa: E402
from session import loader  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SERVER = os.path.join(HERE, "server.py")


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


class Repl(unittest.TestCase):
    def setUp(self):
        self.p = subprocess.Popen(
            [sys.executable, SERVER, "--repl", "--step-timeout", "60",
             "--work", tempfile.mkdtemp()],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
            encoding="utf-8", bufsize=1)
        self.assertEqual(self.read(), {"ready": True, "protocol": 1})
        self.n = 0

    def tearDown(self):
        self.p.stdin.close()
        self.p.wait(timeout=30)
        self.p.stdout.close()

    def read(self):
        return json.loads(self.p.stdout.readline())

    def send(self, method, path, body=None, raw=None):
        self.n += 1
        self.p.stdin.write((raw if raw is not None else json.dumps(
            {"id": self.n, "method": method, "path": path, "body": body}))
            + "\n")
        self.p.stdin.flush()
        return self.n

    def ask(self, method, path, body=None):
        rid = self.send(method, path, body)
        r = self.read()
        self.assertEqual(r["id"], rid)
        return r

    def test_s1(self):
        r = self.ask("POST", "/session", {"header": "problem stage0.S1."})
        sid = r["body"]["session"]
        r = self.ask("POST", "/tactic", {"session": sid, "node": "n0",
                                         "text": "ftc x^3 + x^2 by ring."})
        r = self.ask("POST", "/tactic", {"session": sid, "node": "n1",
                                         "text": "close 2."})
        self.assertEqual(r["body"]["report"], "Proved.")
        r = self.ask("GET", "/hint", {"session": sid, "node": "n0",
                                      "rung": "1"})
        self.assertEqual(r["status"], 200)
        r = self.ask("POST", "/untex", {"latex": "\\frac{1}{2}"})
        self.assertEqual(r["body"]["term"], "1/2")

    def test_bad_lines(self):
        self.send(None, None, raw="{nope")
        r = self.read()
        self.assertEqual((r["id"], r["status"], r["body"]["error"]["code"]),
                         (None, 400, "bad-json"))
        self.send(None, None, raw="[1, 2]")
        self.assertEqual(self.read()["status"], 400)
        r = self.ask("POST", "/session", {"header": "ftc x."})
        self.assertEqual(r["body"]["refusal"]["code"], "bad-header")
        r = self.ask("POST", "/session", {"header": "problem no.such."})
        self.assertEqual((r["status"], r["body"]["error"]["code"]),
                         (400, "unknown-problem"))

    def test_cancel_stops_a_slow_step_and_the_repl_goes_on(self):
        r = self.ask("POST", "/session", {"goal": "pi*sqrt 3/9 == ?A",
                                          "functions": {"f_dx": 1}})
        sid = r["body"]["session"]
        r = self.ask("POST", "/tactic", {"session": sid, "node": "n0",
                                         "text": "fact h := sqrt_sq_val "
                                                 "with a := 3."})
        slow = self.send("POST", "/tactic", {
            "session": sid, "node": "n1",
            "text": "close pi*sqrt 3/9 + (x + y + z + w + 1)^24 "
                    "- (x + y + z + w + 1)^24."})
        time.sleep(1.0)
        # a cancel aimed at another request stops nothing
        self.send(None, "/cancel", {"id": slow + 100})
        self.assertEqual(self.read()["body"], {"cancelled": False})
        self.send(None, "/cancel", {"id": slow})
        got = [self.read(), self.read()]
        by_id = {g["id"]: g for g in got}
        self.assertTrue(by_id[slow]["body"]["timeout"]["cancelled"])
        self.assertEqual(by_id[self.n]["body"], {"cancelled": True})
        r = self.ask("POST", "/tactic", {
            "session": sid, "node": "n1",
            "text": "close pi/(3*sqrt 3) by field using h."})
        self.assertEqual(r["body"]["report"], "Proved.")


@unittest.skipIf(shutil.which("emacs") is None, "emacs is not installed")
class Emacs(unittest.TestCase):
    def test_ert_suite(self):
        prob = loader.load(os.path.join(ROOT, "kernel", "problems", "taylor",
                                        "P3_LOWER.json"))
        d = tempfile.mkdtemp()
        p3 = os.path.join(d, "p3.dx")
        with open(p3, "w") as f:
            f.write("problem taylor.P3_LOWER.\n\n" + "\n".join(
                script.show(st["move"], st["args"])
                for st in prob.proofs["reference"]) + "\n")
        env = dict(os.environ, DX_SENTENCES=os.path.join(HERE, "sentences.json"),
                   DX_P3=p3)
        r = subprocess.run(
            ["emacs", "--batch", "-Q", "-L", ".", "-l", "dx-mode.el", "-l",
             "test-dx-mode.el", "-f", "ert-run-tests-batch-and-exit"],
            cwd=os.path.join(ROOT, "emacs"), env=env, capture_output=True,
            text=True, timeout=900)
        self.assertEqual(r.returncode, 0, r.stdout[-3000:] + r.stderr[-3000:])
        self.assertIn("0 unexpected", r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
