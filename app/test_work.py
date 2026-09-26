"""PERSIST.md Done-when 1 and 2: the work file, replay, and the routes."""

import json
import os
import re
import tempfile
import unittest
from unittest import mock

import api
import script
import work

PAGE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "page",
                    "index.html")


def call(method, path, args):
    status, out = api.handle(method, path, args)
    assert status == 200, (status, out)
    return out


class Work(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        api.WORK_DIR = self.dir

    def tearDown(self):
        api.WORK_DIR = None

    def tac(self, sid, node, text):
        return call("POST", "/tactic", {"session": sid, "node": node,
                                        "text": text})

    def build(self):
        """S1 with a dead end, a fact, a hint and a script."""
        s = call("POST", "/session", {"problem": "stage0.S1",
                                      "resume": True})
        sid = s["session"]
        dead = self.tac(sid, "n0", "ftc x^3 + x^2 by ring.")["node"]
        call("POST", "/retract", {"session": sid, "node": dead})
        f = self.tac(sid, "n0", "fact h := sin_zero.")["node"]
        a = self.tac(sid, f, "ftc x^3 + x^2 by ring.")["node"]
        call("GET", "/hint", {"session": sid, "node": "n0", "rung": "2"})
        text = ("fact h := sin_zero.\n(* then *) ftc x^3 + x^2 by ring.\n"
                "close 2.")
        call("POST", "/script", {"session": sid, "script": text,
                                 "path": ["n0", f, a]})
        return sid, text

    def tree(self, sid):
        t = call("GET", "/tree", {"session": sid})
        return [(n["node"], n["parent"], n["move"], n["retracted"],
                 n["report"], n["summary"]) for n in t["nodes"]]

    def resume(self):
        return call("POST", "/session", {"problem": "stage0.S1",
                                         "resume": True})

    def rewrite_file(self, fn):
        p = work.path_of(self.dir, "stage0.S1")
        with open(p, encoding="utf-8") as f:
            doc = json.load(f)
        fn(doc)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(doc, f)

    # ------------------------------------------------ round trip

    def test_round_trip(self):
        sid, text = self.build()
        before = self.tree(sid)
        r = self.resume()
        self.assertEqual(self.tree(r["session"]), before)
        got = r["resumed"]
        self.assertEqual((got["script"], got["path"], got["checked"],
                          got["dropped"], got["max_rung"]),
                         (text, ["n0", "n2", "n3"], 2, [], 2))
        t = call("GET", "/tree", {"session": r["session"]})
        self.assertEqual(t["max_rung"], 2)
        self.assertTrue(t["saved"]["file"].endswith("stage0.S1.json"))

    def test_the_file_holds_moves_only(self):
        self.build()
        with open(work.path_of(self.dir, "stage0.S1"), encoding="utf-8") as f:
            doc = json.load(f)
        self.assertEqual(set(doc), {"format", "version", "problem", "goal",
                                    "functions", "script", "path",
                                    "max_rung", "evaluations", "nodes",
                                    "saved"})
        for n in doc["nodes"]:
            self.assertEqual(set(n), {"node", "parent", "move", "args",
                                      "retracted"})

    def test_a_report_in_the_file_is_not_read(self):
        self.build()
        self.rewrite_file(lambda d: d.update(report="Proved.",
                                             theorem="1 == 2"))
        r = self.resume()
        self.assertTrue(r["report"].startswith("Open"))
        self.assertNotEqual(r["theorem"], "1 == 2")

    def test_the_problem_file_is_the_authority(self):
        self.build()
        self.rewrite_file(lambda d: d.update(goal="1 == ?A"))
        r = self.resume()
        self.assertIn("Int[x = 0 .. 1]", r["goal"])

    # ------------------------------------------------ dropping

    def test_a_refused_node_drops_with_its_descendants(self):
        self.build()

        def edit(d):
            d["nodes"][1]["args"] = {"entry": "no_such_entry"}
            d["nodes"][1]["move"] = "fact"
            d["nodes"][1]["args"]["bind"] = "h"
        self.rewrite_file(edit)
        r = self.resume()["resumed"]
        codes = [(d["node"], d["code"]) for d in r["dropped"]]
        self.assertEqual(codes[1], ("n3", "dropped"))
        self.assertEqual(r["path"], ["n0"])
        self.assertEqual(r["checked"], 0)
        self.assertEqual(r["ids"], {"n0": "n0", "n1": "n1"})

    def test_a_malformed_node_is_dropped(self):
        self.build()
        self.rewrite_file(lambda d: d["nodes"].insert(0, {"node": 7}))
        r = self.resume()["resumed"]
        self.assertEqual(r["dropped"][0]["code"], "bad-node")
        self.assertEqual(r["checked"], 2)

    def test_a_corrupt_file_is_set_aside(self):
        p = work.path_of(self.dir, "stage0.S1")
        with open(p, "w") as f:
            f.write("{not json")
        r = self.resume()
        self.assertIn("error", r["resumed"])
        with open(p, encoding="utf-8") as f:  # a fresh file in its place
            self.assertEqual(json.load(f)["nodes"], [])
        self.assertTrue(os.path.exists(
            os.path.join(self.dir, "stage0.S1.bad.json")))

    # ------------------------------------------------ the checked prefix

    def test_an_edited_script_checks_only_the_matching_prefix(self):
        self.build()
        self.rewrite_file(lambda d: d.update(
            script="fact h := sin_zero.\nftc x^3 + 2*x^2 by ring."))
        r = self.resume()["resumed"]
        self.assertEqual((r["checked"], r["path"]), (1, ["n0", "n2"]))

    def test_a_path_into_the_dead_end_is_cut(self):
        self.build()
        self.rewrite_file(lambda d: d.update(path=["n0", "n1"]))
        r = self.resume()["resumed"]
        self.assertEqual((r["checked"], r["path"]), (0, ["n0"]))

    # ------------------------------------------------ writing

    def test_a_failed_write_keeps_the_old_file(self):
        sid, _ = self.build()
        p = work.path_of(self.dir, "stage0.S1")
        with open(p, encoding="utf-8") as f:
            old = f.read()
        with mock.patch.object(work.json, "dump",
                               side_effect=OSError("disk full")):
            out = call("POST", "/script", {"session": sid, "script": "x.",
                                           "path": ["n0"]})
        self.assertEqual(out, {"saved": False})
        with open(p, encoding="utf-8") as f:
            self.assertEqual(f.read(), old)
        t = call("GET", "/tree", {"session": sid})
        self.assertIn("disk full", t["saved"]["error"])
        self.assertEqual([f for f in os.listdir(self.dir)
                          if f.endswith(".tmp")], [])

    def test_start_fresh_keeps_the_old_file_as_prev(self):
        self.build()
        call("POST", "/session", {"problem": "stage0.S1"})
        self.assertTrue(os.path.exists(
            os.path.join(self.dir, "stage0.S1.prev.json")))

    def test_the_newest_session_owns_the_file(self):
        """Two tabs on one goal: the older one stops saving, and says so."""
        sid, _ = self.build()
        newer = self.resume()["session"]
        old = call("POST", "/script", {"session": sid, "script": "",
                                       "path": ["n0"]})
        self.assertEqual(old, {"saved": False})
        t = call("GET", "/tree", {"session": sid})
        self.assertIn("superseded", t["saved"]["error"])
        self.assertEqual(self.resume()["resumed"]["checked"], 2)
        del newer

    def test_start_fresh_sticks_and_keeps_the_rung(self):
        self.build()
        r = call("POST", "/session", {"problem": "stage0.S1"})
        self.assertIsNone(r["resumed"])
        again = self.resume()
        self.assertEqual(self.tree(again["session"])[1:], [])
        self.assertEqual(again["resumed"]["max_rung"], 2)

    def test_no_work_directory_saves_nothing(self):
        api.WORK_DIR = None
        s = call("POST", "/session", {"problem": "stage0.S1",
                                      "resume": True})
        self.assertIsNone(s["resumed"])
        self.tac(s["session"], "n0", "ftc x^3 + x^2 by ring.")
        self.assertEqual(os.listdir(self.dir), [])
        t = call("GET", "/tree", {"session": s["session"]})
        self.assertIsNone(t["saved"])

    def test_spans_mark_exactly_the_checked_sentences(self):
        sid, text = self.build()
        r = self.resume()["resumed"]
        self.assertEqual([text[a:b] for a, b in r["spans"]],
                         ["fact h := sin_zero.", "ftc x^3 + x^2 by ring."])

    def test_own_goal_key(self):
        a = work.key(None, "x == ?A", {"f": 1})
        self.assertRegex(a, r"goal-[0-9a-f]{12}\Z")
        self.assertNotEqual(a, work.key(None, "x == ?A", {}))
        self.assertEqual(work.key("../etc", "g", {})[:5], "goal-")
        self.assertEqual(work.key("x.prev", "g", {})[:5], "goal-")

    # ------------------------------------------------ export and import

    def test_export_import(self):
        sid, _ = self.build()
        before = self.tree(sid)
        doc = call("GET", "/export", {"session": sid})
        os.unlink(work.path_of(self.dir, "stage0.S1"))
        r = call("POST", "/import", {"document": doc})
        self.assertEqual(self.tree(r["session"]), before)
        self.assertEqual(r["resumed"]["checked"], 2)
        self.assertTrue(os.path.exists(work.path_of(self.dir, "stage0.S1")))

    def test_import_refuses_what_is_not_a_work_file(self):
        for doc in ({"format": "other"},
                    {"format": "calc-work", "version": 1, "goal": 3},
                    {"format": "calc-work", "version": 1, "goal": "x == ?A",
                     "problem": "no.such"}):
            status, out = api.handle("POST", "/import", {"document": doc})
            self.assertEqual((status, out["error"]["code"]),
                             (400, "bad-document"), doc)

    def test_own_goal_round_trip(self):
        s = call("POST", "/session", {"goal": "Int[x = 0 .. 1] 2*x == ?A",
                                      "resume": True})
        self.assertIsNone(s["resumed"])
        self.tac(s["session"], "n0", "ftc x^2.")
        r = call("POST", "/session", {"goal": "Int[x = 0 .. 1] 2*x == ?A",
                                      "resume": True})
        self.assertEqual(len(self.tree(r["session"])), 2)


class Sentences(unittest.TestCase):
    SCRIPTS = ["ftc x^3 + x^2 by ring.\nclose 2.",
               "int_flip.\x1cint_flip.", "A.\x85B. C.", "A.\ufeffB. C.",
               "A.\u00a0B.\u2003C.",
               "(* a. comment *) close 1.  close 2.\n",
               "int_subst x := t as t from 0 to 1.\nInt[x = 0 .. 1].x.",
               "close 1 (* open", "", "...", "a.b. c.\td."]

    def test_agrees_with_the_page(self):
        """script.sentences against the page's own nextSentence, run in
        node when it is installed, else against the recorded splits."""
        with open(PAGE, encoding="utf-8") as f:
            src = f.read()
        m = re.search(r"function nextSentence\(text, from\) \{.*?\n\}\n",
                      src, re.S)
        self.assertIsNotNone(m)
        space = re.search(r"const SPACE = .*?;\n", src)
        import shutil
        import subprocess
        node = shutil.which("node")
        if node is None:
            self.skipTest("node is not installed")
        js = space.group(0) + m.group(0) + """
const out = JSON.parse(process.argv[1]).map((t) => {
  const r = []; let at = 0;
  for (;;) { const s = nextSentence(t, at); if (!s) break;
             r.push(t.slice(s.start, s.end)); at = s.end; }
  return r; });
console.log(JSON.stringify(out));"""
        got = subprocess.run([node, "-e", js, json.dumps(self.SCRIPTS)],
                             capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(got.stdout),
                         [script.sentences(t) for t in self.SCRIPTS])


if __name__ == "__main__":
    unittest.main()
