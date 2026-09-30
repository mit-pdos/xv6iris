import importlib.util
import unittest
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "text_coverage.py"
SPEC = importlib.util.spec_from_file_location("text_coverage", PATH)
tc = importlib.util.module_from_spec(SPEC)
import sys
sys.modules[SPEC.name] = tc
SPEC.loader.exec_module(tc)

# A miniature program:
#   main:  0x00 jal write ; 0x04 bnez a0,err ; 0x06 jal exit ; 0x0a (err:) jal die ; 0x0e ret
#   start: 0x10 jal main ; 0x14 jal exit
#   write: 0x18 li a7 ; 0x1a ecall ; 0x1e ret
#   exit:  0x20 li a7 ; 0x22 ecall ; 0x26 ret
#   die:   0x28 jal write ; 0x2c j die
#   lib:   0x2e ret                       (nothing calls it)
#   pad:   0x30 unimp
IMAGE = """\
def textChunk0 : List UInstr := [
  -- jal\t18 <write>
  ⟨0x0, 4, 0x018000ef⟩,
  -- bnez\ta0,a <main+0xa>
  ⟨0x4, 2, 0xe119⟩,
  -- jal\t20 <exit>
  ⟨0x6, 4, 0x01a000ef⟩,
  -- jal\t28 <die>
  ⟨0xa, 4, 0x01e000ef⟩,
  -- ret
  ⟨0xe, 2, 0x8082⟩,
  -- jal\t0 <main>
  ⟨0x10, 4, 0xff1ff0ef⟩,
  -- jal\t20 <exit>
  ⟨0x14, 4, 0x00c000ef⟩,
  -- li\ta7,16
  ⟨0x18, 2, 0x48c1⟩,
  -- ecall
  ⟨0x1a, 4, 0x00000073⟩,
  -- ret
  ⟨0x1e, 2, 0x8082⟩,
  -- li\ta7,2
  ⟨0x20, 2, 0x4889⟩,
  -- ecall
  ⟨0x22, 4, 0x00000073⟩,
  -- ret
  ⟨0x26, 2, 0x8082⟩,
  -- jal\t18 <write>
  ⟨0x28, 4, 0xff1ff0ef⟩,
  -- j\t28 <die>
  ⟨0x2c, 2, 0xbff5⟩,
  -- ret
  ⟨0x2e, 2, 0x8082⟩,
  -- unimp
  ⟨0x30, 2, 0x0000⟩
]
"""
FUNCS = [("main", 0x0, 0x10), ("start", 0x10, 8), ("write", 0x18, 8), ("exit", 0x20, 8),
         ("die", 0x28, 6), ("lib", 0x2e, 4)]
# what a sound cone steps: start -> main -> write -> the branch falls through -> exit's ecall
SOUND = {0x10, 0x0, 0x18, 0x1a, 0x1e, 0x4, 0x6, 0x20, 0x22}


def text():
    return tc.Text(tc.parse_text(IMAGE), FUNCS, 0x10)


def by_name(fns):
    return {f.name: f for f in fns}


class ParseTests(unittest.TestCase):
    def test_kinds_and_targets(self):
        t = text()
        kinds = {i.addr: (i.kind, i.target) for i in t.instrs}
        self.assertEqual(kinds[0x0], ("call", 0x18))
        self.assertEqual(kinds[0x4], ("cond", 0xa))
        self.assertEqual(kinds[0x2c], ("jump", 0x28))
        self.assertEqual(kinds[0x1a], ("ecall", None))
        self.assertEqual(kinds[0xe], ("ret", None))
        self.assertEqual(kinds[0x30], ("pad", None))

    def test_operand_comments_are_not_targets(self):
        self.assertEqual(tc.classify_asm("addi\ta1,a1,606 # 1270 <malloc+0x100>"), ("plain", None))
        self.assertEqual(tc.classify_asm("jr\ta5"), ("ijump", None))

    def test_call_graph_and_reachability(self):
        t = text()
        g = t.call_graph()
        self.assertEqual(g["main"], {"write", "exit", "die"})
        self.assertEqual(g["start"], {"main", "exit"})
        self.assertEqual(t.reachable(), {"start", "main", "write", "exit", "die"})


class AnalyzeTests(unittest.TestCase):
    def test_every_byte_of_a_sound_cone_is_explained(self):
        fns, probs = tc.analyze(text(), SOUND)
        self.assertEqual(probs, [])
        f = by_name(fns)
        self.assertEqual(f["write"].status, "covered")
        # main: the error arm behind the branch, entered only through it
        self.assertEqual(f["main"].status, "partial")
        self.assertEqual([(r.lo, r.hi, r.why) for r in f["main"].runs], [(0xa, 0x10, "branch")])
        self.assertIn("never taken", f["main"].runs[0].detail)
        # start: the instruction after the call to main, which does not return
        self.assertEqual([(r.lo, r.why) for r in f["start"].runs], [(0x14, "noreturn")])
        # exit: the ret after its ecall
        self.assertEqual([(r.lo, r.why) for r in f["exit"].runs], [(0x26, "noreturn")])
        # die: reachable in the call graph, but only from main's dead arm
        self.assertEqual((f["die"].status, f["die"].why), ("never", "uncalled"))
        # lib: nothing calls it
        self.assertEqual((f["lib"].status, f["lib"].why), ("never", "unreachable"))
        s = tc.summarize(fns)
        self.assertEqual(s["covered"] + s["branch"] + s["noreturn"] + s["uncalled"]
                         + s["unreachable"], s["total"])
        self.assertNotIn("FINDING", s)

    def test_a_stepped_call_into_an_unstepped_function_is_a_finding(self):
        # the call at 0x0 is stepped, write is not
        fns, _ = tc.analyze(text(), SOUND - {0x18, 0x1a, 0x1e})
        f = by_name(fns)
        self.assertEqual((f["write"].status, f["write"].why), ("never", "FINDING"))
        self.assertIn("0x0 in main", f["write"].detail)

    def test_a_plain_fallthrough_into_unstepped_code_is_a_finding(self):
        # `li a7` at 0x18 is stepped, the ecall after it is not
        fns, _ = tc.analyze(text(), SOUND - {0x1a, 0x1e})
        r = by_name(fns)["write"].runs[0]
        self.assertEqual((r.lo, r.why), (0x1a, "FINDING"))
        self.assertIn("falls through", r.detail)

    def test_a_stepped_jump_to_unstepped_code_is_a_finding(self):
        # die's `j die` is stepped, die's first instruction is not
        fns, _ = tc.analyze(text(), SOUND | {0x2c})
        r = by_name(fns)["die"].runs[0]
        self.assertEqual((r.lo, r.why), (0x28, "FINDING"))

    def test_a_fact_off_an_instruction_is_a_problem(self):
        _, probs = tc.analyze(text(), SOUND | {0x2})
        self.assertEqual(len(probs), 1)
        self.assertIn("0x2", probs[0])

    def test_switch_arms(self):
        img = ("def textChunk0 : List UInstr := [\n"
               "  -- jr\ta5\n  ⟨0x0, 2, 0x8782⟩,\n"
               "  -- li\ta0,1\n  ⟨0x2, 2, 0x4505⟩,\n"
               "  -- ret\n  ⟨0x4, 2, 0x8082⟩,\n"
               "  -- li\ta0,2\n  ⟨0x6, 2, 0x4509⟩,\n"
               "  -- ret\n  ⟨0x8, 2, 0x8082⟩\n]\n")
        t = tc.Text(tc.parse_text(img), [("f", 0, 10)], 0)
        fns, _ = tc.analyze(t, {0x0, 0x2, 0x4})
        self.assertEqual([(r.lo, r.why) for r in fns[0].runs], [(0x6, "switch")])
        self.assertEqual(len(t.indirect()), 1)

    def test_padding_does_not_make_a_function_partial(self):
        t = tc.Text(tc.parse_text(IMAGE), [("lib", 0x2e, 4)], 0x2e)
        fns, _ = tc.analyze(t, {0x2e})
        self.assertEqual(fns[0].status, "covered")
        self.assertEqual([r.why for r in fns[0].runs], ["padding"])


if __name__ == "__main__":
    unittest.main()
