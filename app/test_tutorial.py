"""QUICKSTART.md and tutorial/*.dx: every example checks as the page says.

Each lesson file proves, sentence by sentence, through /session and
/tactic; each is quoted verbatim in QUICKSTART.md; every other ```dx block
there either proves or is refused with the code its `(* refused: CODE *)`
comment names; the entries tables list exactly the kernel's entries; and
no lesson is a gate problem (GATE.md), so the tutorial can be worked before
the gate without reading it.
"""

import glob
import os
import re
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import gate  # noqa: E402
import script  # noqa: E402
from session import K  # noqa: E402,F401  (puts kernel/ on the path)
import entries  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QUICKSTART = os.path.join(ROOT, "QUICKSTART.md")
LESSONS = sorted(glob.glob(os.path.join(ROOT, "tutorial", "*.dx")))
REFUSED = re.compile(r"\(\*\s*refused:\s*([a-z0-9-]+)\s*\*\)")


def _quickstart():
    with open(QUICKSTART, encoding="utf-8") as f:
        return f.read()


def _blocks(text):
    return re.findall(r"```dx\n(.*?)\n```", text, re.S)


def _run(text):
    """Check a .dx text: (reports of the accepted sentences, the refusal
    code or None). Stops at the first refusal."""
    sents = script.sentences(text)
    code, n = api.handle("POST", "/session", {"header": sents[0]})
    if code != 200:
        return [], n.get("code") or n.get("error")
    if "refusal" in n:
        return [], n["refusal"]["code"]
    reports = [n["report"]]
    for t in sents[1:]:
        code, n2 = api.handle("POST", "/tactic", {
            "session": n["session"], "node": n["node"], "text": t})
        if code != 200 or "refusal" in n2:
            return reports, (n2.get("refusal") or n2).get("code")
        n = n2
        reports.append(n["report"])
    return reports, None


class Lessons(unittest.TestCase):
    def test_there_are_twelve(self):
        self.assertEqual(len(LESSONS), 12)

    def test_every_lesson_proves(self):
        for path in LESSONS:
            with self.subTest(lesson=os.path.basename(path)):
                with open(path, encoding="utf-8") as f:
                    reports, refused = _run(f.read())
                self.assertIsNone(refused)
                self.assertEqual(reports[-1], "Proved.")

    def test_every_lesson_is_quoted_verbatim(self):
        blocks = _blocks(_quickstart())
        for path in LESSONS:
            with self.subTest(lesson=os.path.basename(path)):
                with open(path, encoding="utf-8") as f:
                    self.assertIn(f.read().rstrip("\n"), blocks)

    def test_no_lesson_is_a_gate_problem(self):
        corpus = {pid for pid, _ in gate.CORPUS}
        for text in _blocks(_quickstart()):
            head = script.sentences(text)[0]
            m = re.match(r"problem\s+(\S+)\.$", head)
            if m:
                self.assertNotIn(m.group(1), corpus, head)


class Blocks(unittest.TestCase):
    def test_every_block_does_what_the_page_says(self):
        blocks = _blocks(_quickstart())
        self.assertGreater(len(blocks), len(LESSONS))
        for text in blocks:
            with self.subTest(block=text.splitlines()[0]):
                reports, refused = _run(text)
                want = REFUSED.search(text)
                if want:
                    self.assertEqual(refused, want.group(1))
                else:
                    self.assertIsNone(refused)
                    self.assertEqual(reports[-1], "Proved.")


class Entries(unittest.TestCase):
    def test_tables_list_exactly_the_kernels_entries(self):
        text = _quickstart().split("## The entries", 1)[1]
        text = text.split("\n## ", 1)[0]
        rows = dict(re.findall(r"^\| `([a-z0-9_]+)` \| `(.*)` \|$", text,
                               re.M))
        self.assertEqual(set(rows), set(entries.STATEMENTS))
        for name, (stmt, _) in entries.STATEMENTS.items():
            self.assertEqual(rows[name], stmt, name)


if __name__ == "__main__":
    unittest.main()
