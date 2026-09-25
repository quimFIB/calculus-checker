"""PAGE.md Done-when item 2: the check-mode page in a headless browser.

Skipped when Playwright is not installed (it is not part of the standard
library, so it is never required). Proves S1 through the page, checks that
a wrong F is refused with no node added, and that a retracted node is kept.
"""

import os
import sys
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
    @classmethod
    def setUpClass(cls):
        cls.srv = server.HTTPServer(("127.0.0.1", 0), server.Handler)
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
        self.page = self.browser.new_page()
        self.errors = []
        self.page.on("pageerror", lambda e: self.errors.append(str(e)))
        self.page.goto(self.base)
        self.page.wait_for_selector("#problem-select option[value='stage0.S1']",
                                    state="attached")

    def tearDown(self):
        self.page.close()
        self.assertEqual(self.errors, [])

    def start_s1(self):
        p = self.page
        p.select_option("#problem-select", "stage0.S1")
        p.click("#start-problem")
        p.wait_for_selector(".node.selected[data-node='n0']")

    def move(self, name, **args):
        p = self.page
        p.select_option("#move-select", name)
        for k, v in args.items():
            sel = f"#arg-{k}"
            if p.eval_on_selector(sel, "e => e.tagName") == "SELECT":
                p.select_option(sel, v)
            else:
                p.fill(sel, v)
        p.click("#check")

    def nodes(self):
        return self.page.eval_on_selector_all(".node", "es => es.length")

    def test_s1_proved_through_the_page(self):
        p = self.page
        self.start_s1()
        self.assertIn("Int[x = 0 .. 1]", p.inner_text("#problem-info"))
        self.move("ftc", F="x^3 + x^2", check="ring")
        p.wait_for_selector(".node.selected[data-node='n1']")
        self.move("close", value="2", check="ring")
        p.wait_for_selector(".node.selected[data-node='n2']")
        self.assertEqual(p.inner_text("#status-report"), "Proved.")
        self.assertEqual(p.inner_text("#report"), "Proved.")
        self.assertIn("0 machine-checked", p.inner_text("#status-line"))

    def test_wrong_F_is_refused_and_adds_nothing(self):
        p = self.page
        self.start_s1()
        self.move("ftc", F="3*x^3 + 2*x^2", check="ring")
        p.wait_for_selector(".refusal")
        self.assertIn("ftc-check-failed", p.inner_text("#refusal"))
        self.assertIn("residual", p.inner_text("#refusal"))
        self.assertEqual(self.nodes(), 1)

    def test_retract_keeps_the_node(self):
        p = self.page
        self.start_s1()
        self.move("ftc", F="x^3 + x^2", check="ring")
        p.wait_for_selector(".node.selected[data-node='n1']")
        p.click("#retract")
        p.wait_for_selector(".node.selected[data-node='n0']")
        self.assertEqual(self.nodes(), 2)
        row = p.query_selector(".node[data-node='n1']")
        self.assertIn("retracted", row.get_attribute("class"))
        self.assertEqual(row.query_selector(".mark").inner_text(), "✗")


if __name__ == "__main__":
    unittest.main()
