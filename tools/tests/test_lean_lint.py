import importlib.util
import unittest
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "lean_lint.py"
SPEC = importlib.util.spec_from_file_location("lean_lint", PATH)
lint = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lint)


def lints(src):
    return [(l, line) for l, _p, line, _m in lint.lint_text("Xv6/X.lean", src)]


class BlankingTests(unittest.TestCase):
    def test_offsets_are_preserved(self):
        src = 'a -- c\n/- x\n y -/ b "s\\"t" c\n'
        out = lint.blank_comments_and_strings(src)
        self.assertEqual(len(out), len(src))
        self.assertEqual(out.count("\n"), src.count("\n"))
        self.assertEqual(out.split(), ["a", "b", "c"])

    def test_nested_block_comments(self):
        out = lint.blank_comments_and_strings("/- a /- b -/ sorry -/ keep")
        self.assertEqual(out.split(), ["keep"])


class TokenLintTests(unittest.TestCase):
    def test_sorry_in_code_is_found_with_its_line(self):
        self.assertEqual(lints("theorem t : True := by\n  sorry\n"), [("sorry", 2)])

    def test_sorry_in_comments_and_strings_is_not(self):
        src = ('/-- `kwait_proof` is `sorry`-free. -/\n'
               '-- no sorry here\n'
               'def s := "sorry"\n'
               'theorem t : True := trivial\n')
        self.assertEqual(lints(src), [])

    def test_identifiers_containing_the_word_are_not_tokens(self):
        self.assertEqual(lints("def sorry_free := 1\ndef x := no_sorry'\ndef admitted := 2\n"), [])

    def test_admit_native_decide_axiom_autoimplicit(self):
        src = ("theorem a : P := by admit\n"
               "theorem b : P := by native_decide\n"
               "axiom c : P\n"
               "private axiom d : P\n"
               "set_option autoImplicit true\n"
               "def axiomatic := 1  -- axiom in a name or a comment is fine\n")
        self.assertEqual(lints(src), [("sorry", 1), ("native", 2), ("axiom", 3), ("axiom", 4),
                                      ("options", 5)])

    def test_quoted_identifiers_are_skipped(self):
        self.assertEqual(lints("def «sorry» : Nat := 0\n"), [])


class SideTreeTests(unittest.TestCase):
    def test_vtest_gets_sorry_but_not_native_or_drift(self):
        import os, tempfile
        with tempfile.TemporaryDirectory() as d:
            for rel, text in {
                    "Xv6.lean": "import Xv6.A\n", "MachCSL.lean": "", "Xv6/A.lean": "",
                    "vtest-lean/Vtest/Ok.lean": "theorem t : P := by native_decide\n",
                    "vtest-lean/Vtest/Bad.lean": "theorem t : P := by sorry\n"}.items():
                os.makedirs(os.path.dirname(os.path.join(d, rel)), exist_ok=True)
                with open(os.path.join(d, rel), "w", encoding="utf-8") as f:
                    f.write(text)
            found, n = lint.run(d)
        self.assertEqual([(l, p) for l, p, _, _ in found], [("sorry", "vtest-lean/Vtest/Bad.lean")])
        self.assertEqual(n, 3)


class ImportTests(unittest.TestCase):
    def test_header_imports_only(self):
        src = ("/-\nimport Xv6.InAComment\n-/\n"
               "import Xv6.A\n"
               "import MachCSL.B -- trailing\n"
               "\n"
               "namespace Xv6\n"
               "-- import Xv6.NotAnImport\n"
               "import Xv6.AfterTheHeader\n")
        self.assertEqual(lint.imports_of(src), ["Xv6.A", "MachCSL.B"])


class DriftTests(unittest.TestCase):
    def srcs(self, **extra):
        s = {"Xv6.lean": "import Xv6.A\n", "MachCSL.lean": "import MachCSL.M\n",
             "Xv6/A.lean": "import Xv6.B\nimport MachCSL.M\n", "Xv6/B.lean": "",
             "MachCSL/M.lean": ""}
        s.update(extra)
        return s

    def drift(self, sources, allow=()):
        return [(p, m) for l, p, _line, m in lint.lint_drift("/nonexistent", sources, list(allow))]

    def test_a_reached_tree_is_clean(self):
        self.assertEqual(self.drift(self.srcs()), [])

    def test_an_unimported_file_is_drift(self):
        got = self.drift(self.srcs(**{"Xv6/Orphan.lean": "import Xv6.B\n"}))
        self.assertEqual(len(got), 1)
        self.assertEqual(got[0][0], "Xv6/Orphan.lean")
        self.assertIn("no build compiles it", got[0][1])

    def test_a_file_reached_only_from_an_orphan_is_drift_too(self):
        got = self.drift(self.srcs(**{"Xv6/Orphan.lean": "import Xv6.Leaf\n", "Xv6/Leaf.lean": ""}))
        self.assertEqual(sorted(p for p, _ in got), ["Xv6/Leaf.lean", "Xv6/Orphan.lean"])

    def test_an_allow_row_declares_a_deliberate_omission(self):
        s = self.srcs(**{"Xv6/Orphan.lean": ""})
        self.assertEqual(self.drift(s, ["Xv6/Orphan.lean"]), [])

    def test_stale_and_lying_allow_rows_are_errors(self):
        got = self.drift(self.srcs(), ["Xv6/Gone.lean"])
        self.assertIn("no such file exists", got[0][1])
        got = self.drift(self.srcs(), ["Xv6/B.lean"])
        self.assertIn("a lie about the build", got[0][1])

    def test_missing_and_duplicate_imports(self):
        got = self.drift(self.srcs(**{"Xv6/A.lean": "import Xv6.B\nimport Xv6.B\nimport Xv6.Nope\n"
                                                    "import MachCSL.M\nimport Iris.Whatever\n"}))
        msgs = sorted(m for _, m in got)
        self.assertEqual(msgs, ["imports Xv6.B twice", "imports Xv6.Nope, which has no file"])


if __name__ == "__main__":
    unittest.main()
