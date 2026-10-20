import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
REPO = TOOLS.parent
SPEC = importlib.util.spec_from_file_location("config_deviation_lint", TOOLS / "config_deviation_lint.py")
lint = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint)

CONFIG = REPO / "model" / "sail-config-rv64d.json"


def read(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


MINI = """\
// xv6iris config
// with these deviations from upstream's defaults, each marked "xv6iris" inline:
//   1. `a` := false -- why.
//   2. `b` := 1, with a second
//      line of explanation.
//
// Original file header from sail-riscv/config/config.json.in follows:
//
//   1. an upstream numbered list is not ours
{
  // xv6iris: false (upstream default: true) -- deviation 1
  "a": false,
  // xv6iris: DEVIATION from the template
  // (deviation 2 in the header).
  "b": 1
}
"""


class RealFileTests(unittest.TestCase):
    def test_the_checked_in_configuration_passes(self):
        probs, items, markers = lint.check(read(CONFIG))
        self.assertEqual(probs, [])
        # the count is the file's business (7 since item 8's withdrawal, 2026-10-20); the
        # invariant is that the items are 1..N and every item has a marker
        self.assertGreaterEqual(len(items), 1)
        self.assertEqual(items, list(range(1, len(items) + 1)))
        self.assertEqual(sorted(markers), items)

    def test_the_cli_passes_on_it(self):
        p = subprocess.run([sys.executable, str(TOOLS / "config_deviation_lint.py")], capture_output=True,
                           text=True)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("header items, each marked inline", p.stdout)

    def test_a_header_item_removed_fails(self):
        s = read(CONFIG)
        _, items, _ = lint.check(s)
        n = len(items)  # remove the second-to-last item: its markers become orphans
        i = s.index("//   %d. " % (n - 1))
        j = s.index("//   %d. " % n)
        probs, _, _ = lint.check(s[:i] + s[j:])
        self.assertTrue(any("not 1..%d" % (n - 1) in p for p in probs), probs)
        self.assertTrue(any("deviation %d, which the header does not list" % (n - 1) in p for p in probs), probs)

    def test_a_marker_naming_item_9_fails(self):
        s = read(CONFIG).replace("-- deviation 4", "-- deviation 9", 1)
        probs, _, _ = lint.check(s)
        self.assertTrue(any("deviation 9, which the header does not list" in p for p in probs), probs)
        self.assertTrue(any("header item 4 has no inline" in p for p in probs), probs)

    def test_the_cli_fails_on_a_bad_copy(self):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "c.json")
            with open(p, "w", encoding="utf-8") as f:
                f.write(read(CONFIG).replace("-- deviation 4", "-- deviation 9", 1))
            r = subprocess.run([sys.executable, str(TOOLS / "config_deviation_lint.py"), p],
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)
            self.assertIn("deviation 9", r.stdout)


class MiniatureTests(unittest.TestCase):
    def test_a_multi_line_marker_and_the_upstream_header_are_read_right(self):
        probs, items, markers = lint.check(MINI)
        self.assertEqual(probs, [])
        self.assertEqual(items, [1, 2])
        self.assertEqual(sorted(markers), [1, 2])

    def test_a_marker_naming_no_item_fails(self):
        probs, _, _ = lint.check(MINI.replace("-- deviation 1", "-- see the header"))
        self.assertTrue(any("names no deviation" in p for p in probs), probs)
        self.assertTrue(any("header item 1 has no inline" in p for p in probs), probs)

    def test_a_gap_in_the_header_fails(self):
        probs, _, _ = lint.check(MINI.replace("//   2. `b`", "//   3. `b`"))
        self.assertTrue(any("not 1..2" in p for p in probs), probs)


if __name__ == "__main__":
    unittest.main()
