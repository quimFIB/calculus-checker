"""PAGE.md Done-when item 2: the check-mode page in a headless browser.

Skipped when Playwright is not installed (it is not part of the standard
library, so it is never required). Revision 2 (rocq-mode): proves S1 by
stepping a typed script, refuses a wrong F with nothing checked, keeps an
undone node, retracts on an edit inside the checked region, and proves
COS_SQ with To cursor.
"""

import os
import sys
import tempfile
import threading
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import server  # noqa: E402

try:
    from playwright.sync_api import sync_playwright
except ImportError:  # pragma: no cover
    sync_playwright = None

CHROMIUM = "/opt/pw-browsers/chromium"  # when the pinned build is absent


@unittest.skipIf(sync_playwright is None, "Playwright is not installed")
class Page(unittest.TestCase):
    SERVER = server.HTTPServer

    @classmethod
    def setUpClass(cls):
        cls.srv = cls.SERVER(("127.0.0.1", 0), server.Handler)
        cls.srv.verbose = False
        cls.base = f"http://127.0.0.1:{cls.srv.server_address[1]}/"
        threading.Thread(target=cls.srv.serve_forever, daemon=True).start()
        cls.pw = sync_playwright().start()
        try:
            cls.browser = cls.pw.chromium.launch()
        except Exception:
            cls.browser = cls.pw.chromium.launch(executable_path=CHROMIUM)

    @classmethod
    def tearDownClass(cls):
        cls.browser.close()
        cls.pw.stop()
        cls.srv.shutdown()
        cls.srv.server_close()

    def setUp(self):
        server.api.WORK_DIR = tempfile.mkdtemp()  # PERSIST.md: per test
        self.page = self.browser.new_page()
        self.errors = []
        self.page.on("pageerror", lambda e: self.errors.append(str(e)))
        self.page.goto(self.base)
        self.page.wait_for_selector("#problem-select option[value='stage0.S1']",
                                    state="attached")

    def tearDown(self):
        self.page.close()
        self.assertEqual(self.errors, [])

    def start(self, pid="stage0.S1"):
        p = self.page
        p.select_option("#problem-select", pid)
        p.click("#start-problem")
        p.wait_for_selector(".node.current[data-node='n0']")
        if p.is_visible("#script"):
            p.fill("#script", "")

    def type_script(self, text):
        self.page.fill("#script", text)

    def report(self):
        return self.page.inner_text("#status-report")

    def nodes(self):
        return self.page.eval_on_selector_all(".node", "es => es.length")

    def wait_idle(self):
        self.page.wait_for_function(
            "() => !document.querySelector('#backdrop mark.pending')")
        self.page.wait_for_function(
            "() => !document.getElementById('to-cursor').disabled")

    def test_s1_proved_by_stepping(self):
        p = self.page
        self.start()
        self.assertIn("Int[x = 0 .. 1]", p.inner_text("#problem-info"))
        self.type_script("ftc x^3 + x^2 by ring.\nclose 2.\n")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        p.keyboard.press("Alt+ArrowDown")
        p.wait_for_selector(".node.current[data-node='n2']")
        p.wait_for_function(  # the status pane redraws after the tree
            "() => document.getElementById('status-report')"
            ".innerText === 'Proved.'")
        self.assertEqual(self.report(), "Proved.")
        self.assertEqual(p.inner_text("#report"), "Proved.")
        self.assertIn("0 machine-checked", p.inner_text("#status-line"))
        self.assertEqual(p.inner_text("#backdrop mark.checked"),
                         "ftc x^3 + x^2 by ring.\nclose 2.")

    @unittest.skipIf(server.integrate.find_python() is None, "no SymPy")
    def test_evaluate_proves_and_inserts(self):
        """EVAL.md: Evaluate on S1's goal shows 2 with a check mark, and
        Insert puts sentences in the script that check to Proved."""
        p = self.page
        old = server.PROPOSER
        server.PROPOSER = server.integrate.Proposer(
            server.integrate.find_python(), 30)
        try:
            self.start()
            p.click("#evaluate")
            p.wait_for_selector("#evaluation")
            self.assertIn("Proved by the kernel", p.inner_text("#evaluation"))
            self.assertIn("= 2", p.inner_text("#eval-value"))
            p.click("#eval-insert")
            self.assertEqual(p.input_value("#script").strip(),
                             "ftc x^3 + x^2 by ring.\nclose 2 by ring.")
            p.click("#to-cursor")
            p.wait_for_function(
                "() => document.getElementById('status-report')"
                ".innerText === 'Proved.'")
            # a typed integral, no session needed for it
            p.fill("#eval-term", "Int[x = 0 .. oo] exp(-x)")
            p.click("#eval-go")
            p.wait_for_function("() => document.getElementById('eval-value')"
                                " && document.getElementById('eval-value')"
                                ".innerText.includes('= 1')")
        finally:
            server.PROPOSER = old

    def test_wrong_F_is_refused_and_checks_nothing(self):
        p = self.page
        self.start()
        self.type_script("ftc 3*x^3 + 2*x^2 by ring.")
        p.click("#next")
        p.wait_for_selector("#refusal")
        self.assertIn("ftc-check-failed", p.inner_text("#refusal"))
        self.assertIn("residual", p.inner_text("#refusal"))
        self.assertEqual(self.nodes(), 1)
        self.assertEqual(p.query_selector_all("#backdrop mark.checked"), [])
        self.assertEqual(len(p.query_selector_all("#backdrop mark.error")), 1)

    def test_stuck_explains_and_its_suggestion_steps(self):
        """STUCK.md: a refusal shows its kind of stuck, and "Use this" puts
        the kernel-accepted suggestion in place of the refused sentence."""
        p = self.page
        self.start()
        self.type_script("ftc 2*x^3 + 2*x^2 by ring.\n")
        p.click("#next")
        p.wait_for_selector("#stuck")
        self.assertEqual(p.get_attribute("#stuck", "data-kind"), "algebra")
        self.assertIn("2 times the integrand", p.inner_text("#stuck"))
        p.click("#use-suggestion")
        self.assertIn("ftc (2*x^3 + 2*x^2)/2 by ring.",
                      p.input_value("#script"))
        self.assertNotIn("ftc 2*x^3", p.input_value("#script"))
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")

    def test_work_survives_a_reload_and_round_trips(self):
        """PERSIST.md: step S1 halfway, reload, start S1 again: the script
        and checked region come back and the next step closes it. Export
        then Import gives the same tree."""
        p = self.page
        self.start()
        self.type_script("ftc x^3 + x^2 by ring.\nclose 2.\n")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        p.wait_for_selector("#saved")
        p.reload()
        p.wait_for_selector("#problem-select option[value='stage0.S1']",
                            state="attached")
        p.select_option("#problem-select", "stage0.S1")
        p.click("#start-problem")
        p.wait_for_selector(".node.current[data-node='n1']")
        self.assertEqual(p.input_value("#script"),
                         "ftc x^3 + x^2 by ring.\nclose 2.\n")
        self.assertEqual(p.inner_text("#backdrop mark.checked"),
                         "ftc x^3 + x^2 by ring.")
        with p.expect_download() as dl:
            p.click("#export")
        path = dl.value.path()
        self.assertEqual(dl.value.suggested_filename, "stage0.S1.calc.json")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n2']")
        self.assertEqual(self.report(), "Proved.")
        p.set_input_files("#import-file", path)
        p.wait_for_selector(".node.current[data-node='n1']")
        self.assertEqual(self.nodes(), 2)
        self.assertEqual(p.inner_text("#backdrop mark.checked"),
                         "ftc x^3 + x^2 by ring.")

    def test_partial_fractions_on_p5(self):
        """FACTOR.md: the palette's Partial fractions on readiness P5 falls
        back to ℝ and shows the decomposition with its check."""
        p = self.page
        self.start("improper.P5")
        p.wait_for_selector("#partial-fractions")
        p.click("#partial-fractions")
        p.wait_for_selector("#factor-result")
        out = p.inner_text("#factor-result")
        self.assertIn("Partial fractions over ℝ", out)
        self.assertIn("checked by field using sqrt_sq_val with a := 2", out)
        self.assertEqual(p.query_selector_all("#factor-result .katex-error"),
                         [])
        self.assertEqual(p.input_value("#script"), "")

    def test_undo_keeps_the_node(self):
        p = self.page
        self.start()
        self.type_script("ftc x^3 + x^2 by ring.")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        p.click("#undo")
        p.wait_for_selector(".node.current[data-node='n0']")
        self.assertEqual(self.nodes(), 2)
        row = p.query_selector(".node[data-node='n1']")
        self.assertIn("retracted", row.get_attribute("class"))
        self.assertEqual(row.query_selector(".mark").inner_text(), "✗")

    def test_editing_the_checked_region_retracts(self):
        p = self.page
        self.start()
        self.type_script("ftc x^3 + x^2 by ring.\nclose 2.")
        p.click("#script")
        p.keyboard.press("Control+End")
        p.keyboard.press("Control+Enter")
        p.wait_for_selector(".node.current[data-node='n2']")
        # put the caret inside the first sentence and type
        p.evaluate("() => { const t = document.getElementById('script');"
                   " t.focus(); t.setSelectionRange(5, 5); }")
        p.keyboard.type(" ")
        p.wait_for_selector(".node.current[data-node='n0']")
        self.wait_idle()
        self.assertEqual(p.query_selector_all("#backdrop mark.checked"), [])
        self.assertEqual(
            p.eval_on_selector_all(".node.retracted", "es => es.length"), 2)

    def test_hint_buttons(self):
        p = self.page
        self.start("parts.P1_PARTS")
        p.click("#hint-1")
        p.wait_for_selector("#hint")
        self.assertIn("A substitution.", p.inner_text("#hint"))
        p.click("#hint-3")
        p.wait_for_selector("#hint >> text=inside sin")
        self.assertIn("Costs: u ≥ 0", p.inner_text("#hint"))
        self.type_script("ftc x by ring.\n")  # refused: the hint stays usable
        p.click("#next")
        p.wait_for_selector("#refusal")
        p.click("#hint-2")
        p.wait_for_selector("#hint")
        self.assertIn("u = t²", p.inner_text("#hint"))

    def test_every_goal_renders_in_katex(self):
        p = self.page
        ids = p.eval_on_selector_all("#problem-select option",
                                     "os => os.map(o => o.value)")
        self.assertGreater(len(ids), 8)
        for pid in ids:
            with self.subTest(pid):
                self.start(pid)
                p.wait_for_selector("#goal .katex")
                self.assertEqual(p.eval_on_selector_all(
                    ".katex-error", "es => es.length"), 0)
                self.assertTrue(p.query_selector("#formal-goal .katex"))
                if not pid.startswith("taylor."):  # order goals (E96)
                    self.assertIn("?A", p.inner_text("#goal .plain"))

    def test_palette_card_progress_probe(self):
        p = self.page
        self.start("parts.P1_PARTS")
        p.wait_for_selector("#palette-moves button")
        self.assertIn("int_subst", p.inner_text("#palette-moves"))
        self.assertIn("0 admissions", p.inner_text("#status-line"))
        self.type_script("int_subst x := t^2 as t from 0 to pi/2.\n")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        p.wait_for_selector("#progress")
        self.assertIn("rule now matches", p.inner_text("#progress"))
        self.assertIn("12 digits agree", p.inner_text("#probe"))
        self.assertTrue(p.inner_text("#probe").startswith("~"))
        p.wait_for_selector("#palette-rewrites button")
        p.click("#palette-rewrites button")
        self.assertIn("rewrite sqrt_sq with u := t at sqrt(t^2).",
                      p.input_value("#script"))
        p.keyboard.press("Alt+ArrowDown")
        p.wait_for_selector(".node.current[data-node='n2']")
        self.assertIn("2 rules", p.inner_text("#status-line"))
        p.click("#hint-2")
        p.wait_for_selector("#hint")
        self.assertIn("max rung 2", p.inner_text("#status-line"))

    def test_card_marks_s1(self):
        p = self.page
        self.start()
        p.wait_for_selector("#card")
        p.click("#card summary")
        self.assertIn("1 match", p.inner_text("#card summary"))
        self.assertEqual(p.eval_on_selector_all(
            "#card tr.match", "rs => rs.map(r => r.dataset.card)"), ["power"])

    def test_cos_sq_to_cursor(self):
        p = self.page
        self.start("trig.COS_SQ")
        self.type_script(
            "(* DESIGN.md §8.9's first example *)\n"
            "ftc t/2 + sin(2*t)/4 by field.\n"
            "rewrite sin_pi at sin(2*(pi/2)).\n"
            "rewrite sin_zero at sin(2*0).\n"
            "close pi/4.\n")
        p.click("#script")
        p.keyboard.press("Control+End")
        p.click("#to-cursor")
        p.wait_for_selector(".node.current[data-node='n4']")
        self.assertEqual(self.report(), "Proved.")
        self.assertIn("pi/4", p.inner_text("#theorem"))

    def test_p3_lower_bound_to_cursor(self):
        """Readiness P3 part 1, the lower bound, typed as the problem file's
        reference proof and checked to the cursor."""
        import loader
        import script
        here = os.path.dirname(os.path.abspath(__file__))
        prob = loader.load(os.path.join(here, "..", "kernel", "problems",
                                        "taylor", "P3_LOWER.json"))
        text = "\n".join(script.show(st["move"], st["args"])
                         for st in prob.proofs["reference"]) + "\n"
        p = self.page
        self.start("taylor.P3_LOWER")
        self.type_script(text)
        p.click("#script")
        p.keyboard.press("Control+End")
        p.click("#to-cursor")
        p.wait_for_selector(".node.current[data-node='n4']", timeout=120000)
        self.assertEqual(self.report(), "Proved.")
        self.assertIn("(5/16)*b^6 <=", p.inner_text("#theorem"))

    # ------------------------------------------------ pretty mode (PRETTY.md)

    def pretty_on(self):
        p = self.page
        p.click("#pretty-toggle")
        p.wait_for_selector(".prow.open .seg-text")
        self.assertTrue(p.is_hidden("#script"))

    def type_open(self, text):
        p = self.page
        p.click(".prow.open .seg-text")
        p.keyboard.type(text)
        p.keyboard.press("Escape")  # the autocomplete list, if any
        p.keyboard.press("Enter")

    def read_settled(self):
        """The script once the field reads in flight have landed."""
        p = self.page
        p.wait_for_timeout(300)
        p.wait_for_function("() => P.reads.size === 0")
        return p.input_value("#script")

    def test_pretty_proves_s1(self):
        p = self.page
        self.start()
        self.pretty_on()
        self.type_open("ftc _.")
        p.wait_for_selector(".prow.sentence math-field")
        p.wait_for_function("() => document.activeElement.tagName === 'MATH-FIELD'")
        p.wait_for_timeout(200)  # MathLive's keyboard sink settles
        p.keyboard.type("x^3")
        p.keyboard.press("ArrowRight")
        p.keyboard.type("+x^2")
        self.assertEqual(self.read_settled(), "ftc x^3 + x^2.")
        self.assertEqual(p.inner_text(".prow.sentence .echo"), "x^3 + x^2")
        self.type_open("close 2.")
        p.wait_for_selector(".prow.sentence:nth-child(3) math-field")
        p.click("#to-cursor")
        p.wait_for_selector(".node.current[data-node='n2']")
        p.wait_for_function("() => document.getElementById('status-report')"
                            ".innerText === 'Proved.'")
        self.assertEqual(p.eval_on_selector_all(".prow.checked", "rs => rs.length"), 2)
        self.assertTrue(p.eval_on_selector_all(
            ".prow.checked math-field", "fs => fs.every(f => f.hasAttribute('read-only'))"))
        p.click("#pretty-toggle")
        self.assertTrue(p.is_visible("#script"))
        self.assertEqual(p.input_value("#script"), "ftc x^3 + x^2.\nclose 2.")
        self.assertEqual(p.inner_text("#backdrop mark.checked"),
                         "ftc x^3 + x^2.\nclose 2.")

    def test_pretty_fraction_and_bad_field(self):
        p = self.page
        self.start()
        self.pretty_on()
        self.type_open("close _.")
        p.wait_for_function("() => document.activeElement.tagName === 'MATH-FIELD'")
        p.wait_for_timeout(200)  # MathLive's keyboard sink settles
        p.keyboard.type("4/2")
        self.assertEqual(self.read_settled(), "close 4/2.")
        p.keyboard.press("ArrowRight")
        p.keyboard.type("ab")
        self.read_settled()
        p.wait_for_selector(".seg-term.bad")
        p.click("#next")
        p.wait_for_selector("#refusal")
        self.assertIn("bad-tex", p.inner_text("#refusal"))
        self.assertEqual(self.nodes(), 1)

    def test_pretty_keeps_text_set_from_outside(self):
        """Rows never overwrite text the page set itself: a resumed script,
        a palette sentence, a new problem's script."""
        p = self.page
        self.start()
        self.type_script("ftc x^3 + x^2 by ring.\n")
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        self.pretty_on()
        p.wait_for_selector(".prow.checked math-field")
        self.assertEqual(p.input_value("#script"), "ftc x^3 + x^2 by ring.\n")
        p.wait_for_selector("#palette-moves button")
        p.click("#palette-moves button")  # close's template
        p.wait_for_function("() => document.getElementById('script').value.includes('close')")
        p.wait_for_selector(".prow.sentence:not(.checked) math-field")
        self.assertTrue(p.input_value("#script").startswith("ftc x^3 + x^2 by ring.\n"))
        self.start("trig.COS_SQ")
        p.wait_for_selector(".prow.open .seg-text")
        self.assertEqual(p.input_value("#script"), "")
        p.select_option("#problem-select", "stage0.S1")  # its work comes back
        p.click("#start-problem")
        p.wait_for_selector(".prow.checked")
        self.assertIn("ftc x^3 + x^2 by ring.", p.input_value("#script"))

    def test_autocomplete_takes_int_subst(self):
        p = self.page
        self.start("parts.P1_PARTS")
        self.pretty_on()
        p.click(".prow.open .seg-text")
        p.keyboard.type("int_s")
        p.wait_for_selector("#complete .item")
        self.assertIn("int_subst x := _ as t from _ to _", p.inner_text("#complete"))
        p.keyboard.press("Enter")
        p.wait_for_selector(".prow.sentence math-field")
        self.assertEqual(p.eval_on_selector_all(".prow.sentence math-field", "fs => fs.length"), 3)
        self.assertEqual(p.eval_on_selector_all(".prow.sentence .seg-name",
                                                "ns => ns.map(n => n.textContent)"), ["x", "t"])
        p.wait_for_function("() => document.activeElement.tagName === 'MATH-FIELD'")
        p.wait_for_timeout(200)  # MathLive's keyboard sink settles
        p.keyboard.type("t^2")
        for k, text in ((1, "0"), (2, "pi/2")):
            p.wait_for_timeout(200)
            p.query_selector_all(".prow.sentence math-field")[k].click()
            p.wait_for_timeout(200)
            p.keyboard.type(text)
        self.assertEqual(self.read_settled(),
                         "int_subst x := t^2 as t from 0 to pi/2 by ring.")
        p.select_option(".prow.sentence .seg-choice", "field")
        self.assertIn("by field.", p.input_value("#script"))
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")

    def test_page_splitter_matches_the_fixture(self):
        """DX.md review 4: nextSentence gives sentences.json's spans."""
        import json
        here = os.path.dirname(os.path.abspath(__file__))
        with open(os.path.join(here, "sentences.json")) as f:
            cases = json.load(f)["cases"]
        got = self.page.evaluate("""(cases) => cases.map((c) => {
            const out = []; let at = 0, s;
            while ((s = nextSentence(c.text, at))) { out.push([s.start, s.end]); at = s.end; }
            return out; })""", cases)
        for c, g in zip(cases, got):
            self.assertEqual(g, c["spans"], c["text"])

    def test_mathlive_output_matches_the_fixture(self):
        """PRETTY.md review 8: the captured LaTeX in untex_cases.json is
        still what MathLive gives for those keys, with the page's shortcuts."""
        import json
        here = os.path.dirname(os.path.abspath(__file__))
        with open(os.path.join(here, "untex_cases.json")) as f:
            cases = [c for c in json.load(f)["cases"] if "keys" in c]
        p = self.page
        self.start()
        self.pretty_on()
        for c in cases:
            with self.subTest(c["keys"]):
                # a fresh field each time: MathLive keeps recent keystrokes
                # for its shortcuts, whatever its value is set to
                p.evaluate("""() => { document.getElementById('probe-field')?.remove();
                    const m = document.createElement('math-field');
                    m.id = 'probe-field'; document.getElementById('pretty').append(m);
                    m.addEventListener('mount', () => { m.inlineShortcuts = SHORTCUTS; }); }""")
                p.wait_for_timeout(200)
                p.click("#probe-field")
                p.wait_for_timeout(150)
                for k in c["keys"]:
                    if k[:1].isupper() and k.isalpha():
                        p.keyboard.press(k)
                    else:
                        p.keyboard.type(k)
                self.assertEqual(p.evaluate(
                    "() => document.getElementById('probe-field').value"), c["latex"])


if __name__ == "__main__":
    unittest.main()


@unittest.skipIf(sync_playwright is None, "Playwright is not installed")
class Timeout(Page):
    """TIMEOUT.md Done-when 2: the page over a worker with a 3 s timeout,
    served on threads as ./calc serves it, so /cancel is heard."""
    SERVER = server.ThreadingHTTPServer
    SLOW = ("close pi*sqrt 3/9 + (x + y + z + w + 1)^24 "
            "- (x + y + z + w + 1)^24.")
    GOOD = "close pi/(3*sqrt 3) by field using h."

    @classmethod
    def setUpClass(cls):
        import backend
        cls.saved_backend = server.BACKEND
        server.BACKEND = backend.Worker(3.0, tempfile.mkdtemp())
        super().setUpClass()

    @classmethod
    def tearDownClass(cls):
        super().tearDownClass()
        server.BACKEND.close()
        server.BACKEND = cls.saved_backend

    def start_slow(self):
        p = self.page
        p.click("summary")
        p.fill("#own-goal", "pi*sqrt 3/9 == ?A")
        # one work file per test: the key hashes the functions too
        p.fill("#own-functions", "f_" + self._testMethodName[5:9] + "/1")
        p.click("#start-own")
        p.wait_for_selector(".node.current[data-node='n0']")
        text = "fact h := sqrt_sq_val with a := 3.\n" + self.SLOW + "\n"
        p.fill("#script", text)
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n1']")
        self.wait_idle()
        return text

    def replace_slow_with_good(self, text):
        p = self.page
        a = text.index(self.SLOW)
        p.evaluate(f"() => {{ const t = document.getElementById('script'); "
                   f"t.focus(); t.setSelectionRange({a}, "
                   f"{a + len(self.SLOW)}); }}")
        p.keyboard.insert_text(self.GOOD)
        p.click("#next")
        p.wait_for_selector(".node.current[data-node='n2']")
        self.assertEqual(self.report(), "Proved.")

    def test_a_slow_step_times_out(self):
        p = self.page
        text = self.start_slow()
        p.click("#next")
        p.wait_for_selector("#timeout", timeout=15000)
        self.assertIn("ran out of time after 3", p.inner_text("#timeout"))
        self.assertEqual(len(p.query_selector_all("#backdrop mark.timeout")), 1)
        self.assertEqual(p.query_selector_all("#refusal"), [])
        self.replace_slow_with_good(text)

    def test_cancel_stops_a_slow_step(self):
        p = self.page
        text = self.start_slow()
        p.click("#next")
        p.wait_for_function("() => !document.getElementById('cancel').disabled")
        p.wait_for_timeout(300)
        p.click("#cancel")
        p.wait_for_selector("#timeout", timeout=2500)
        self.assertEqual(p.inner_text("#timeout"),
                         "Cancelled. Nothing changed.")
        self.wait_idle()
        self.replace_slow_with_good(text)

    # the in-process tests are not repeated over the worker
    for _name in [n for n in dir(Page) if n.startswith("test_")]:
        locals()[_name] = None
    del _name
