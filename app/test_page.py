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
        self.assertEqual(self.report(), "Proved.")
        self.assertEqual(p.inner_text("#report"), "Proved.")
        self.assertIn("0 machine-checked", p.inner_text("#status-line"))
        self.assertEqual(p.inner_text("#backdrop mark.checked"),
                         "ftc x^3 + x^2 by ring.\nclose 2.")

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
