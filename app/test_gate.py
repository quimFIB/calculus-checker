"""GATE.md: the report over work files in a temporary directory."""

import json
import os
import shutil
import tempfile
import unittest

import api
import gate
import script

FIRES = [pid for pid, _ in gate.CORPUS]  # filtered in setUpClass


def _work(pid, max_rung, proof=True):
    """A work file for pid as ./calc saves it, made through the API: a
    session, the reference proof as tactics when `proof`, then max_rung."""
    code, out = api.handle("POST", "/session", {"problem": pid})
    sid = out["session"]
    node = out["node"]
    if proof:
        p = gate._problems()[pid]
        text = ""
        for st in p.proofs["reference"]:
            sentence = script.show(st["move"], st["args"])
            code, r = api.handle("POST", "/tactic", {"session": sid,
                                                     "node": node,
                                                     "text": sentence})
            node = r["node"]
            text += sentence + "\n"
        path = [f"n{i}" for i in range(len(p.proofs["reference"]) + 1)]
        api.handle("POST", "/script", {"session": sid, "script": text,
                                       "path": path})
    for rung in range(1, max_rung + 1):
        api.handle("GET", "/hint", {"session": sid, "node": node,
                                    "rung": str(rung)})


class Gate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        probs = gate._problems()
        cls.fires = [pid for pid, _ in gate.CORPUS if gate.fires(probs[pid])]
        cls.silent = [pid for pid, _ in gate.CORPUS
                      if not gate.fires(probs[pid])]

    def setUp(self):
        self.dir = tempfile.mkdtemp()
        api.WORK_DIR = self.dir

    def tearDown(self):
        api.WORK_DIR = None
        shutil.rmtree(self.dir)

    def test_every_corpus_problem_exists(self):
        probs = gate._problems()
        self.assertEqual([p for p, _ in gate.CORPUS if p not in probs], [])
        self.assertGreaterEqual(len(self.fires), gate.MIN_WORKED)

    def test_passes_when_the_rung_falls(self):
        n = len(self.fires)
        for i, pid in enumerate(self.fires):
            _work(pid, 3 if i < n // 3 else 0, proof=i < 2)
        rep = gate.report(self.dir)
        self.assertEqual(rep["verdict"], "passes")
        self.assertEqual((rep["first_third"], rep["last_third"]), (3, 0))
        self.assertEqual(rep["rows"][0]["proved"], "Proved.")
        self.assertIn("Verdict: passes.", gate.text(rep))

    def test_fails_when_it_does_not(self):
        for pid in self.fires:
            _work(pid, 2, proof=False)
        rep = gate.report(self.dir)
        self.assertEqual(rep["verdict"], "fails")
        self.assertIn(gate.FALSIFIER, gate.text(rep))
        self.assertEqual(rep["histogram"]["2"], len(self.fires))

    def test_too_little_data_and_no_row_kept_out(self):
        for pid in self.fires[:3]:
            _work(pid, 1, proof=False)
        _work(self.silent[0], 3, proof=False)
        rep = gate.report(self.dir)
        self.assertEqual((rep["verdict"], rep["n"]), ("not enough data", 3))
        self.assertEqual(rep["no_row"], [self.silent[0]])

    def test_a_file_that_does_not_replay_is_open(self):
        pid = self.fires[0]
        _work(pid, 1)
        path = os.path.join(self.dir, pid + ".json")
        with open(path) as f:
            doc = json.load(f)
        for n in doc["nodes"]:
            n["args"] = {"nonsense": 1}
        with open(path, "w") as f:
            json.dump(doc, f)
        row = gate.report(self.dir)["rows"][0]
        self.assertEqual((row["worked"], row["max_rung"], row["proved"]),
                         (True, 1, None))


if __name__ == "__main__":
    unittest.main()
