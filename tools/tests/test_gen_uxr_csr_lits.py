import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
REPO = TOOLS.parent
SPEC = importlib.util.spec_from_file_location("gen_uxr_csr_lits", TOOLS / "gen_uxr_csr_lits.py")
gen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gen)
SPEC_CG = importlib.util.spec_from_file_location("check_gen", TOOLS / "check_gen.py")
cg = importlib.util.module_from_spec(SPEC_CG)
SPEC_CG.loader.exec_module(cg)

MODEL = REPO / gen.MODEL_REL
TARGET = REPO / gen.TARGET_REL


def read(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


def write(p, s):
    with open(p, "w", encoding="utf-8") as f:
        f.write(s)


class LiteralTests(unittest.TestCase):
    """The walk of the generated model's `is_CSR_accessible` chain."""

    def test_the_chain_has_distinct_literals_in_the_models_order(self):
        lits = gen.literals(str(MODEL))
        self.assertEqual(len(lits), len(set(lits)))
        self.assertEqual(lits[:2], [0x301, 0x300])           # misa, mstatus: the chain's head
        self.assertIn(0x7A0, lits)                          # tselect (Sdtrig)
        self.assertNotIn(0x3A0, lits)                       # pmpcfg0: a range guard, not a literal

    def test_the_block_spells_the_list_and_its_mask(self):
        lits = [0x001, 0x300, 0xC00]
        b = gen.block(lits)
        self.assertTrue(b.startswith(gen.BEGIN) and b.endswith(gen.END))
        self.assertIn("[0x001, 0x300, 0xC00]", b)
        self.assertIn(str((1 << 0x001) | (1 << 0x300) | (1 << 0xC00)), b)

    def test_the_checked_in_block_is_current(self):
        p = subprocess.run([sys.executable, str(TOOLS / "gen_uxr_csr_lits.py")], capture_output=True,
                           text=True)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)


class MiniTreeTests(unittest.TestCase):
    """The generator and its check_gen entry on a copy of the two files it reads."""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.repo = os.path.join(self.d.name, "repo")
        for rel in (gen.MODEL_REL, gen.TARGET_REL):
            os.makedirs(os.path.dirname(os.path.join(self.repo, rel)), exist_ok=True)
            shutil.copy(REPO / rel, os.path.join(self.repo, rel))
        os.makedirs(os.path.join(self.repo, "tools"))
        shutil.copy(TOOLS / "gen_uxr_csr_lits.py", os.path.join(self.repo, "tools"))

    def tearDown(self):
        self.d.cleanup()

    def gen_check(self):
        return subprocess.run([sys.executable, str(TOOLS / "gen_uxr_csr_lits.py"), "--root", self.repo],
                              capture_output=True, text=True)

    def run_check(self):
        work = os.path.join(self.d.name, "work")
        os.makedirs(work, exist_ok=True)
        c = cg.Ctx(self.repo, work, "no-such-objdump", None, False)
        return cg.run_checks(c, only=["uxr-csr-lits"])

    def stale(self):
        p = os.path.join(self.repo, gen.TARGET_REL)
        s = read(p).replace("[0x301, 0x300,", "[0x301, 0x300, 0x7FF,")
        write(p, s)
        return p, s

    def test_an_untouched_copy_passes(self):
        self.assertEqual(self.gen_check().returncode, 0)
        c = self.run_check()
        self.assertEqual([(n, s) for n, s, _ in c.results], [("uxr-csr-lits", cg.OK)])

    def test_a_hand_edit_of_the_block_fails_both_checks_and_is_not_written(self):
        p, s = self.stale()
        self.assertEqual(self.gen_check().returncode, 1)
        c = self.run_check()
        self.assertEqual(c.results[0][1], cg.FAIL)
        self.assertIn("0x7FF", c.diffs[0][1])
        self.assertEqual(read(p), s)

    def test_write_restores_the_block(self):
        self.stale()
        subprocess.run([sys.executable, str(TOOLS / "gen_uxr_csr_lits.py"), "--root", self.repo,
                        "--write"], check=True, capture_output=True)
        self.assertEqual(read(os.path.join(self.repo, gen.TARGET_REL)), read(TARGET))

    def edit_model(self, old, new):
        p = os.path.join(self.repo, gen.MODEL_REL)
        s = read(p)
        self.assertIn(old, s)
        write(p, s.replace(old, new))

    def test_a_moved_range_guard_is_an_error_not_a_literal(self):
        self.edit_model("(0x3E#8 : (BitVec 8))", "(0x3A#8 : (BitVec 8))")
        r = self.gen_check()
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("range guards moved", r.stderr)
        c = self.run_check()
        self.assertEqual(c.results[0][1], cg.FAIL)
        self.assertIn("gen_uxr_csr_lits.py failed", c.results[0][2])

    def test_a_new_kind_of_guard_is_an_error(self):
        self.edit_model("(0x3E#8 : (BitVec 8))", "(0x3F#8 : (BitVec 8))")
        r = self.gen_check()
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("unexpected guard", r.stderr)


if __name__ == "__main__":
    unittest.main()
