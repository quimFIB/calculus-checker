"""QUICKSTART.md and tutorial/: every example checks as the page says.

- Each lesson proves, sentence by sentence, through /session and /tactic,
  and is quoted verbatim on the page.
- Each exercise is a header alone, shown on the page, and its solution
  proves from the same header.
- Every other ```dx block proves, or, when it carries
  `(* refused: CODE "text" ... *)`, has every sentence accepted up to its
  last, which is refused with CODE and says each quoted text.
- The terms tables parse and refuse as they say; the entries tables list
  exactly the kernel's entries.
- No lesson, exercise or example is a gate problem (GATE.md), compared
  by goal with variables renamed, not only by id.
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
TUTORIAL = os.path.join(ROOT, "tutorial")
LESSONS = sorted(glob.glob(os.path.join(TUTORIAL, "*.dx")))
EXERCISES = sorted(glob.glob(os.path.join(TUTORIAL, "exercises", "*.dx")))
MARKER = re.compile(r"\(\*\s*refused:\s*([A-Za-z0-9-]+)((?:\s+\"[^\"]*\")*)\s*\*\)")
RESERVED = {"sin", "cos", "tan", "asin", "acos", "atan", "exp", "ln", "sqrt",
            "abs", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "pi",
            "e_const", "Int", "D", "in", "oo", "true", "C"}


def _read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def _blocks(text):
    return re.findall(r"^```dx\n(.*?)\n```$", text, re.M | re.S)


def _section(text, heading):
    return text.split(f"\n## {heading}\n", 1)[1].split("\n## ", 1)[0]


def _ok(test, code, body, what):
    test.assertEqual(code, 200, f"{what}: {body}")


def _run(test, text):
    """Check a .dx text: (the session's first node, reports of the
    accepted sentences, the refusal or None). Stops at the first refusal;
    a non-200 answer fails the test."""
    sents = script.sentences(text)
    code, n = api.handle("POST", "/session", {"header": sents[0]})
    _ok(test, code, n, sents[0])
    if "refusal" in n:
        return None, [], n["refusal"]
    first, reports = n, [n["report"]]
    for t in sents[1:]:
        code, n2 = api.handle("POST", "/tactic", {
            "session": n["session"], "node": n["node"], "text": t})
        _ok(test, code, n2, t)
        if "refusal" in n2:
            return first, reports, n2["refusal"]
        n = n2
        reports.append(n["report"])
    return first, reports, None


def _says(refusal):
    """Every text a refusal shows: message, headline, lines, suggestions."""
    stuck = refusal.get("stuck") or {}
    return [refusal.get("message") or "", stuck.get("headline") or ""] \
        + list(stuck.get("lines") or []) + list(stuck.get("suggest") or [])


def _shape(goal):
    """A goal with every name but the grammar's own renamed in order of
    first appearance, so that renaming a variable does not hide a copy."""
    names = {}

    def rename(m):
        w = m.group(0)
        if w in RESERVED:
            return w
        return names.setdefault(w, f"v{len(names)}")
    return re.sub(r"[A-Za-z][A-Za-z0-9_]*", rename, re.sub(r"\s+", "", goal))


def _gate_shapes(test):
    shapes = {}
    for pid, _ in gate.CORPUS:
        code, n = api.handle("POST", "/session", {"problem": pid})
        _ok(test, code, n, pid)
        shapes[_shape(n["goal"])] = pid
    return shapes


class Lessons(unittest.TestCase):
    def test_there_are_twelve(self):
        self.assertEqual(len(LESSONS), 12)

    def test_every_lesson_proves(self):
        for path in LESSONS:
            with self.subTest(lesson=os.path.basename(path)):
                _, reports, refused = _run(self, _read(path))
                self.assertIsNone(refused)
                self.assertEqual(reports[-1], "Proved.")

    def test_every_lesson_is_quoted_verbatim(self):
        blocks = _blocks(_read(QUICKSTART))
        for path in LESSONS:
            with self.subTest(lesson=os.path.basename(path)):
                self.assertIn(_read(path).rstrip("\n"), blocks)


class Exercises(unittest.TestCase):
    def test_one_per_lesson(self):
        self.assertEqual([os.path.basename(p) for p in EXERCISES],
                         [os.path.basename(p) for p in LESSONS])

    def test_each_is_a_header_shown_on_the_page(self):
        page = _read(QUICKSTART)
        for path in EXERCISES:
            with self.subTest(exercise=os.path.basename(path)):
                sents = script.sentences(_read(path))
                self.assertEqual(len(sents), 1, "an exercise holds no tactics")
                rel = os.path.relpath(path, ROOT)
                self.assertIn(f"`{rel}`,\n`{sents[0]}`", page)

    def test_each_solution_proves_from_the_same_header(self):
        for path in EXERCISES:
            name = os.path.basename(path)
            with self.subTest(exercise=name):
                sol = os.path.join(TUTORIAL, "solutions", name)
                text = _read(sol)
                self.assertEqual(script.sentences(text)[0],
                                 script.sentences(_read(path))[0])
                self.assertIn(os.path.relpath(sol, ROOT), _read(path))
                _, reports, refused = _run(self, text)
                self.assertIsNone(refused)
                self.assertEqual(reports[-1], "Proved.")


class Blocks(unittest.TestCase):
    def test_every_fence_is_seen(self):
        text = _read(QUICKSTART)
        openers = re.findall(r"^(?:```|~~~)(.*)$", text, re.M)[::2]
        self.assertTrue(all(o in ("", "dx") for o in openers), openers)
        self.assertEqual(openers.count("dx"), len(_blocks(text)))

    def test_every_block_does_what_the_page_says(self):
        blocks = _blocks(_read(QUICKSTART))
        for text in blocks:
            with self.subTest(block=text.splitlines()[0]):
                _, reports, refused = _run(self, text)
                markers = MARKER.findall(text)
                self.assertLessEqual(len(markers), 1)
                if not markers:
                    self.assertIsNone(refused)
                    self.assertEqual(reports[-1], "Proved.")
                    continue
                code, quoted = markers[0]
                sents = script.sentences(text)
                self.assertIsNotNone(refused)
                self.assertEqual(refused["code"], code)
                # the refused sentence is the last: all before it checked
                self.assertEqual(len(reports), len(sents) - 1)
                said = _says(refused)
                for q in re.findall(r"\"([^\"]*)\"", quoted):
                    self.assertTrue(any(q in s for s in said),
                                    f"{q!r} not in {said}")


class Terms(unittest.TestCase):
    def _parse(self, text):
        code, r = api.handle("POST", "/parse", {"text": text})
        _ok(self, code, r, text)
        return r

    def test_write_parses_and_not_is_refused(self):
        sec = _section(_read(QUICKSTART), "Writing terms")
        rows = re.findall(r"^\| (`[^|]*`) \| (`[^|]*`) \| .* \|$", sec, re.M)
        self.assertGreaterEqual(len(rows), 8)
        for write, nope in rows:
            for t in re.findall(r"`([^`]+)`", write):
                with self.subTest(write=t):
                    self.assertIn("term", self._parse(t))
            for t in re.findall(r"`([^`]+)`", nope):
                with self.subTest(refused=t):
                    self.assertIn("refusal", self._parse(t))

    def test_reads_as_the_table_says(self):
        sec = _section(_read(QUICKSTART), "Writing terms")
        rows = re.findall(r"^\| `([^`]+)` \| `([^`]+)` \|$", sec, re.M)
        self.assertGreaterEqual(len(rows), 4)
        for typed, reads in rows:
            with self.subTest(typed=typed):
                self.assertEqual(self._parse(typed).get("term"), reads)


class Entries(unittest.TestCase):
    def test_tables_list_exactly_the_kernels_entries(self):
        sec = _section(_read(QUICKSTART), "The entries")
        rows = []
        for line in sec.splitlines():
            if not line.startswith("|") or line.startswith("|---") \
                    or line.startswith("| Entry |"):
                continue
            m = re.fullmatch(r"\| `([a-z0-9_]+)` \| `(.*)` \|", line)
            self.assertIsNotNone(m, line)
            rows.append(m.groups())
        names = [r[0] for r in rows]
        self.assertEqual(len(names), len(set(names)), "a row is repeated")
        self.assertEqual(set(names), set(entries.STATEMENTS))
        for name, stmt in rows:
            self.assertEqual(stmt, entries.STATEMENTS[name][0], name)
        for name in entries.FAMILIES:  # E163, in prose: a family per n
            self.assertIn(f"`{name}`", sec)


class Gate(unittest.TestCase):
    def test_nothing_is_a_gate_problem(self):
        corpus = {pid for pid, _ in gate.CORPUS}
        shapes = _gate_shapes(self)
        texts = _blocks(_read(QUICKSTART)) + [
            _read(p) for p in LESSONS + EXERCISES] + [
            _read(p) for p in glob.glob(
                os.path.join(TUTORIAL, "solutions", "*.dx"))]
        for text in texts:
            head = script.sentences(text)[0]
            with self.subTest(header=head[:60]):
                m = re.fullmatch(r"problem\s+(\S+)\.", head)
                if m:
                    self.assertNotIn(m.group(1), corpus)
                first, _, _ = _run(self, text)
                if first is not None:
                    self.assertNotIn(_shape(first["goal"]), shapes)


if __name__ == "__main__":
    unittest.main()
