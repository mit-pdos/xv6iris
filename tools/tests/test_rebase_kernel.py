import importlib.util
import os
import tempfile
import unittest
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "rebase_kernel.py"
SPEC = importlib.util.spec_from_file_location("rebase_kernel", PATH)
rk = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rk)

# A synthetic two-image kernel.  `f` moves 0x100 and gains an instruction at
# old +0x10 (interval f:+0x10:+4); its auipc materialises `buf` from a new
# distance; `g` (the jal target) moves 0x140; `kv` is a size-0 assembler
# label; the process table `proc` (2 slots) grows its stride 368 -> 376 with
# the fields from +344 on shifted 8; `h` differs only in an immediate.
OLD_F = (0x80001000, [
    (0x80001000, "addi", "sp,sp,-16", None),
    (0x80001004, "auipc", "a0,0x5", None),
    (0x80001008, "addi", "a0,a0,16", "80006014 <buf>"),
    (0x8000100c, "jal", "80001200 <g>", None),
    (0x80001010, "ld", "a5,368(s1)", None),
    (0x80001014, "ret", "", None),
])
NEW_F = (0x80001100, [
    (0x80001100, "addi", "sp,sp,-16", None),
    (0x80001104, "auipc", "a0,0x6", None),
    (0x80001108, "addi", "a0,a0,24", "80007120 <buf>"),
    (0x8000110c, "jal", "80001340 <g>", None),
    (0x80001110, "nop", "", None),
    (0x80001114, "ld", "a5,376(s1)", None),
    (0x80001118, "ret", "", None),
])
OLD = {"f": OLD_F,
       "g": (0x80001200, [(0x80001200, "ret", "", None)]),
       "h": (0x80001300, [(0x80001300, "addi", "a0,a0,368", None), (0x80001304, "ret", "", None)]),
       "kv": (0x80001400, [(0x80001400, "addi", "sp,sp,-256", None), (0x80001404, "jal", "80001200 <g>", None)])}
NEW = {"f": NEW_F,
       "g": (0x80001340, [(0x80001340, "ret", "", None)]),
       "h": (0x80001400, [(0x80001400, "addi", "a0,a0,376", None), (0x80001404, "ret", "", None)]),
       "kv": (0x80001500, [(0x80001500, "addi", "sp,sp,-256", None), (0x80001504, "jal", "80001340 <g>", None)])}
SYM_OLD = {"f": (0x80001000, 0x16, ".text"), "g": (0x80001200, 2, ".text"), "h": (0x80001300, 6, ".text"),
           "kv": (0x80001400, 0, ".text"), "buf": (0x80006014, 64, ".bss"), "proc": (0x80010000, 2 * 368, ".bss")}
SYM_NEW = {"f": (0x80001100, 0x1a, ".text"), "g": (0x80001340, 2, ".text"), "h": (0x80001400, 6, ".text"),
           "kv": (0x80001500, 0, ".text"), "buf": (0x80007120, 64, ".bss"), "proc": (0x80010100, 2 * 376, ".bss")}
RO = (0x80008000, b"")

SRC = """\
def fAddr : BitVec 64 := KA.«f»
abbrev fPc (o : BitVec 64) : BitVec 64 := KA.«f» + o
theorem f_br_200 : KA.«f» + 0x200#64 = KA.«g» := by decide
theorem s1 : P := k_step_e (wp_s_ld cpu _ (KA.«f» + 0x10#64) true 368#12 15#5 9#5 (by decide))
theorem s2 : P := k_step_e (wp_s_jal cpu _ (KA.«f» + 0xc#64) true 500#21) with [f_br_200]
theorem s3 : KA.«f» + 0x4#64 + (BitVec.signExtend 64 (5#20 ++ 0#12) + 16#64) = KA.«buf» := by decide
theorem s4 : KA.«f» + 0x5004#64 = Q := rfl
theorem s5 : fAddr + 0x10#64 = fPc 0x10#64 := rfl
theorem s6 : KA.«proc» + 0x178#64 = KA.«proc» + 0x158#64 := rfl
theorem s7 : KernelSyms.«proc» + 376 = 0 := rfl
theorem s8 : P := k_step_e (wp_s_jal cpu _ (KA.«kv» + 0x4#64) true 2096636#21)
theorem s9 : P := k_step_e (wp_s_ld cpu _ (KA.«f» + 0x10#64) true 360#12 15#5 9#5 (by decide))
"""

WANT = """\
def fAddr : BitVec 64 := KA.«f»
abbrev fPc (o : BitVec 64) : BitVec 64 := KA.«f» + o
theorem f_br_240 : KA.«f» + 0x240#64 = KA.«g» := by decide
theorem s1 : P := k_step_e (wp_s_ld cpu _ (KA.«f» + 0x14#64) true 376#12 15#5 9#5 (by decide))
theorem s2 : P := k_step_e (wp_s_jal cpu _ (KA.«f» + 0xc#64) true 564#21) with [f_br_240]
theorem s3 : KA.«f» + 0x4#64 + (BitVec.signExtend 64 (6#20 ++ 0#12) + 24#64) = KA.«buf» := by decide
theorem s4 : KA.«f» + 0x6004#64 = Q := rfl
theorem s5 : fAddr + 0x14#64 = fPc 0x14#64 := rfl
theorem s6 : KA.«proc» + 0x180#64 = KA.«proc» + 0x160#64 := rfl
theorem s7 : KernelSyms.«proc» + 384 = 0 := rfl
theorem s8 : P := k_step_e (wp_s_jal cpu _ (KA.«kv» + 0x4#64) true 2096700#21)
theorem s9 : P := k_step_e (wp_s_ld cpu _ (KA.«f» + 0x14#64) true 360#12 15#5 9#5 (by decide))
"""


def rebase(old, new, iv):
    return rk.Rebase(None, None, iv, tables=(SYM_OLD if old is OLD else SYM_NEW, SYM_NEW if new is NEW else SYM_OLD,
                                              old, new, RO, RO))


class Symbolic(unittest.TestCase):
    def run_pass(self, rb, fields):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "A.lean")
            with open(p, "w") as fh:
                fh.write(SRC)
            sp = rk.Symbolic(rb, "proc:2", fields)
            srcs, out = sp.run([p])
            return out[p], rb.report

    def test_intervals(self):
        with tempfile.NamedTemporaryFile("w", suffix=".iv", delete=False) as fh:
            fh.write("# comment\nf:+0x10:+4\nnamex:+0x4a:x,+0x4c:+4\n")
        try:
            iv = rk.parse_intervals(fh.name)
        finally:
            os.unlink(fh.name)
        self.assertEqual(iv, {"f": [(0x10, 4)], "namex": [(0x4a, None), (0x4c, 4)]})
        rb = rebase(OLD, NEW, iv)
        self.assertEqual([rb.newoff("namex", o) for o in (0x48, 0x4a, 0x4c)], [0x48, None, 0x50])
        self.assertEqual(rb.newoff("f", 0xc), 0xc)
        self.assertEqual(rb.map_addr(0x80001010, "t"), 0x80001114)

    def test_symbolic(self):
        rb = rebase(OLD, NEW, {"f": [(0x10, 4)]})
        out, report = self.run_pass(rb, "+344:+8")
        self.assertEqual(out, WANT)
        # the guarded immediate (s9: 360 is not the old 368) is reported, not rewritten
        self.assertTrue(any("neither the old 368 nor the new 376" in r for r in report), report)

    def test_unchanged_image_is_a_no_op(self):
        rb = rebase(OLD, OLD, None)
        out, _ = self.run_pass(rb, None)
        self.assertEqual(out, SRC)

    def test_immediates_only(self):
        rb = rebase(OLD, NEW, {"f": [(0x10, 4)]})
        self.assertEqual(rb.changed, {"f"})
        self.assertEqual(rb.imm_only, {"h"})


if __name__ == "__main__":
    unittest.main()
