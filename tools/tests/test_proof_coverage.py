import importlib.util
import sys
import unittest
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "proof_coverage.py"
SPEC = importlib.util.spec_from_file_location("proof_coverage", PATH)
cov = importlib.util.module_from_spec(SPEC)
# Registered BEFORE exec: the module declares `@dataclass`es, and dataclasses
# resolves annotations through `sys.modules[cls.__module__]`.
sys.modules[SPEC.name] = cov
SPEC.loader.exec_module(cov)


KERNEL_IMAGE = """\
namespace Xv6.Kernel
def textChunk0 : List KInstr := [
  -- jal\t80000008 <start>
  ⟨0x80000000, 4, 0x008000ef⟩,
  -- j\t80000004 <spin>
  ⟨0x80000004, 2, 0xa001⟩,
  -- nop
  ⟨0x80000006, 2, 0x0001⟩,
  -- ret
  ⟨0x80000008, 2, 0x8082⟩,
  -- addi\tsp,sp,-16
  ⟨0x8000000a, 2, 0x1141⟩,
  -- ret
  ⟨0x8000000c, 2, 0x8082⟩
]
end Xv6.Kernel

namespace MachCSL.KernelSyms

def «_entry» : Nat := 0x80000000
def «spin» : Nat := 0x80000004
def «start» : Nat := 0x80000008
def «helper» : Nat := 0x8000000a

-- data symbols (.data, .bss, .rodata, .got)
def «stack0» : Nat := 0x80000008  -- size 0x1000

end MachCSL.KernelSyms
"""


def images():
    syms, instrs = cov.parse_kernel_image(KERNEL_IMAGE)
    fs = cov.build_functions("kernel", syms, instrs)
    calls = cov.call_sites(KERNEL_IMAGE)
    for f in fs:
        f.callers = calls.get(f.name, 0)
    return {"kernel": fs}


def facts(lines):
    f = cov.Facts()
    f.roots = [("Xv6.top", "top")]
    f.cone = 5000
    for l in lines:
        p = l.split("\t")
        if p[0] == "I":
            f.ifaces[p[1]].append((p[2], cov.parse_pins(p[3]),
                                   {int(x, 16) for x in (p[4].split() if len(p) > 4 else [])}))
        elif p[0] == "L":
            f.links[p[4]].append((p[1], p[2], int(p[3])))
        elif p[0] == "T":
            f.direct.append((p[1], p[2], int(p[3]), cov.parse_pins(p[4])))
        elif p[0] == "C":
            f.decls[p[2]] = (p[1], p[3], int(p[5]))
    return f


def status(imgs, name):
    return next(f for f in imgs["kernel"] if f.name == name).status


class ImageTests(unittest.TestCase):
    def test_functions_are_text_symbols_sized_to_the_next_entry(self):
        fs = {f.name: f for f in images()["kernel"]}
        # the data symbol after the marker is not a function, even though an
        # instruction starts at its address
        self.assertEqual(sorted(fs), ["_entry", "helper", "spin", "start"])
        self.assertEqual((fs["_entry"].size, fs["spin"].size, fs["start"].size, fs["helper"].size),
                         (4, 4, 2, 4))

    def test_call_sites_count_exact_entry_targets(self):
        fs = {f.name: f for f in images()["kernel"]}
        self.assertEqual((fs["start"].callers, fs["spin"].callers, fs["helper"].callers), (1, 1, 0))

    def test_trampoline_addresses_map_to_the_trampoline_page(self):
        f = cov.Func("kernel", "_trampoline", 0x80006000, size=156)
        g = cov.Func("kernel", "userret", 0x8000609c, size=138)
        m = cov.AddrMap([f, g], trampoline=True)
        self.assertEqual(m.find(cov.TRAMPOLINE + 0x9c), (g, 0))
        self.assertEqual(m.find(cov.TRAMPOLINE), (f, 0))
        self.assertIsNone(m.find(0x80007000))


class ClassifyTests(unittest.TestCase):
    def test_linked_and_reached_is_proven(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.START\twp_start\tpcIs:-:sym:c pcIs:-:0x80000008:e pcIs:-:ret:c",
            "L\tXv6.Start\tXv6.LinkStart\t1\tXv6.START"]))
        self.assertEqual(status(imgs, "start"), cov.PROVEN)

    def test_linked_but_not_reached_is_unreached(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.START\twp_start\tpcIs:-:0x80000008:e pcIs:-:ret:c",
            "L\tXv6.Start\tXv6.LinkStart\t0\tXv6.START"]))
        self.assertEqual(status(imgs, "start"), cov.UNREACHED)

    def test_proved_outside_a_link_module_is_unlinked(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.START\twp_start\tpcIs:-:0x80000008:e pcIs:-:ret:c",
            "L\tXv6.start_proof\tXv6.ProofStart\t1\tXv6.START"]))
        self.assertEqual(status(imgs, "start"), cov.UNLINKED)

    def test_stated_only_is_assumed(self):
        imgs = images()
        cov.classify(imgs, facts(["I\tXv6.START\twp_start\tpcIs:-:0x80000008:e pcIs:-:ret:c"]))
        self.assertEqual(status(imgs, "start"), cov.ASSUMED)

    def test_a_continuation_pin_is_not_an_entry(self):
        # _entry's contract continues at start: that credits _entry, not start
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.ENTRY\twp_entry\tpcIs:-:0x80000000:e pcIs:-:0x80000008:c",
            "L\tXv6.Entry\tXv6.LinkEntry\t1\tXv6.ENTRY"]))
        self.assertEqual(status(imgs, "_entry"), cov.PROVEN)
        self.assertEqual(status(imgs, "start"), cov.NONE)

    def test_a_contract_that_stops_inside_the_function_is_a_fragment(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.HELPER_PRO\twp\tpcIs:-:0x8000000a:e pcIs:-:0x8000000c:c",
            "L\tXv6.HelperPro\tXv6.LinkHelper\t1\tXv6.HELPER_PRO"]))
        self.assertEqual(status(imgs, "helper"), cov.PARTIAL)

    def test_an_entry_pin_off_the_function_entry_is_a_fragment(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.HELPER_EPI\twp\tpcIs:-:0x8000000c:e pcIs:-:ret:c",
            "L\tXv6.HelperEpi\tXv6.LinkHelper\t1\tXv6.HELPER_EPI"]))
        self.assertEqual(status(imgs, "helper"), cov.PARTIAL)

    def test_lemma_pins_make_a_function_partial(self):
        imgs = images()
        cov.classify(imgs, facts(["T\tXv6.helper_step\tXv6.ProofHelper\t1\tpcIs:-:0x8000000c:e"]))
        self.assertEqual(status(imgs, "helper"), cov.PARTIAL)

    def test_link_suffix_modules_are_link_modules(self):
        self.assertTrue(cov.is_link_module("Xv6.LinkKfree"))
        self.assertTrue(cov.is_link_module("Xv6.CatPrintfLink"))
        self.assertFalse(cov.is_link_module("Xv6.ProofKfree"))


class UserContractTests(unittest.TestCase):
    """The Link discipline is the kernel's: a user contract that is proved and
    reached is proven, with the missing Link file as a note."""

    def run_user(self, module):
        imgs = images()
        imgs["Cat"] = [cov.Func("Cat", "main", 0x7e, size=10)]
        cov.classify(imgs, facts([
            "I\tXv6.CAT_MAIN\twp_catMain\turun:Cat:0x7e:e",
            f"L\tXv6.catMain_holds\t{module}\t1\tXv6.CAT_MAIN"]))
        return imgs["Cat"][0]

    def test_proved_without_a_link_file_counts_with_a_note(self):
        f = self.run_user("Xv6.ProofCatMain")
        self.assertEqual((f.status, f.nolink), (cov.PROVEN, True))
        self.assertIn("(no Link file)", f.evidence[0]["how"])
        self.assertIn("(no Link file)", cov.contract_of(f))

    def test_proved_through_a_link_file_has_no_note(self):
        f = self.run_user("Xv6.LinkCat")
        self.assertEqual((f.status, f.nolink), (cov.PROVEN, False))

    def test_the_kernel_still_needs_the_link_file(self):
        imgs = images()
        cov.classify(imgs, facts([
            "I\tXv6.START\twp_start\tpcIs:-:0x80000008:e pcIs:-:ret:c",
            "L\tXv6.start_proof\tXv6.ProofStart\t1\tXv6.START"]))
        self.assertEqual(status(imgs, "start"), cov.UNLINKED)


class FactTests(unittest.TestCase):
    def test_only_facts_in_the_cone_are_stepped(self):
        import os, tempfile
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "envfacts.tsv")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write("X\tXv6.a\tXv6.M\t1\tCat\t0x0 0x2\n"
                         "X\tXv6.b\tXv6.M\t0\tCat\t0x2 0x4\n"
                         "X\tXv6.c\tXv6.M\t1\tSh\t0x10\n"
                         "XU\tXv6.bridge\tXv6.M\t1\tXv6.uinstrIs_of_text\n")
            f = cov.load_facts(p)
        self.assertEqual(f.stepped["Cat"], {0x0, 0x2})
        self.assertEqual(f.unstepped["Cat"], {0x2, 0x4})
        self.assertEqual(f.stepped["Sh"], {0x10})
        self.assertEqual(f.open_uses, [("Xv6.bridge", "Xv6.M", 1, "Xv6.uinstrIs_of_text")])


class ManifestTests(unittest.TestCase):
    FACTS = ["I\tXv6.KV\thandler\tpcIs:-:sym:c\t0x80000008",
             "L\tXv6.Kv\tXv6.LinkKv\t1\tXv6.KV",
             "C\tXv6.LinkKv\tXv6.Kv\tthm\t10\t1\t"]

    def test_a_verified_declaration_is_proven(self):
        imgs = images()
        _, errs = cov.classify(imgs, facts(self.FACTS), {"kernel:start": ("Xv6.Kv", "a vector")})
        self.assertEqual(errs, [])
        self.assertEqual(status(imgs, "start"), cov.PROVEN)

    def test_the_interface_must_name_the_entry_address(self):
        imgs = images()
        _, errs = cov.classify(imgs, facts(self.FACTS), {"kernel:helper": ("Xv6.Kv", "a vector")})
        self.assertEqual(len(errs), 1)
        self.assertIn("does not name the entry address", errs[0])
        self.assertEqual(status(imgs, "helper"), cov.NONE)

    def test_a_missing_theorem_is_an_error(self):
        _, errs = cov.classify(images(), facts(self.FACTS), {"kernel:start": ("Xv6.Gone", "x")})
        self.assertIn("is not a theorem of the tree", errs[0])

    def test_a_stale_function_is_an_error(self):
        _, errs = cov.classify(images(), facts(self.FACTS), {"kernel:gone": ("Xv6.Kv", "x")})
        self.assertIn("not a function of the image", errs[0])


class FloorTests(unittest.TestCase):
    def proven(self, names):
        imgs = images()
        imgs["Cat"] = [cov.Func("Cat", "main", 0x7e, size=10)]
        for f in imgs["kernel"]:
            if f.name in names:
                f.status = cov.PROVEN
        return imgs

    def fx(self):
        f = facts(["I\tXv6.X\tf\tpcIs:-:0x80000000:e"])
        return f

    def test_every_kernel_function_must_be_proven_or_allowlisted(self):
        imgs = self.proven({"_entry", "start", "helper"})
        errs = cov.check_floor(imgs, self.fx(), {}, {})
        self.assertEqual(len(errs), 1)
        self.assertIn("`spin` is none", errs[0])
        self.assertEqual(cov.check_floor(imgs, self.fx(), {"kernel:spin": "never reached"}, {}), [])

    def test_a_stale_allow_row_is_an_error(self):
        imgs = self.proven({"_entry", "start", "helper", "spin"})
        errs = cov.check_floor(imgs, self.fx(), {"kernel:spin": "never reached"}, {})
        self.assertIn("proven and linked now", errs[0])
        errs = cov.check_floor(imgs, self.fx(), {"kernel:nosuch": "x"}, {})
        self.assertIn("not a function of the image", errs[0])

    def test_an_allow_row_needs_a_reason(self):
        imgs = self.proven({"_entry", "start", "helper"})
        errs = cov.check_floor(imgs, self.fx(), {"kernel:spin": ""}, {})
        self.assertIn("has no reason", errs[0])

    def test_a_baselined_user_function_may_not_regress(self):
        imgs = self.proven({"_entry", "start", "helper", "spin"})
        errs = cov.check_floor(imgs, self.fx(), {}, {"Cat:main": ""})
        self.assertIn("had a proved, reached contract (baseline) and is now none", errs[0])
        imgs["Cat"][0].status = cov.PROVEN
        self.assertEqual(cov.check_floor(imgs, self.fx(), {}, {"Cat:main": ""}), [])

    def utext(self, covered, finding=False):
        fc = cov.tc.FnCov("main", 0x7e, 10, covered=covered, status="partial")
        if finding:
            fc.runs.append(cov.tc.Run(0x80, 0x84, 4, "FINDING", "0x7e (`li a0,1`) is stepped and "
                                                                 "falls through to 0x80, which is not"))
        return {"Cat": dict(fns=[fc], summary=cov.tc.summarize([fc]), problems=[], indirect=0, outside=0)}

    def test_stepped_bytes_may_not_drop_below_the_baseline(self):
        imgs = self.proven({"_entry", "start", "helper", "spin"})
        self.assertEqual(cov.check_floor(imgs, self.fx(), {}, {"bytes Cat 6": ""}, self.utext(6)), [])
        errs = cov.check_floor(imgs, self.fx(), {}, {"bytes Cat 8": ""}, self.utext(6))
        self.assertEqual(len(errs), 1)
        self.assertIn("6 text bytes are stepped by the proofs, the baseline has 8", errs[0])

    def test_a_finding_fails_the_check(self):
        imgs = self.proven({"_entry", "start", "helper", "spin"})
        errs = cov.check_floor(imgs, self.fx(), {}, {}, self.utext(6, finding=True))
        self.assertEqual(len(errs), 1)
        self.assertIn("is never stepped although", errs[0])

    def test_empty_facts_fail_instead_of_reporting_nothing(self):
        imgs = self.proven({"_entry", "start", "helper", "spin"})
        empty = cov.Facts()
        errs = cov.check_floor(imgs, empty, {}, {})
        self.assertTrue(any("no top theorem" in e for e in errs))
        self.assertTrue(any("looks empty" in e for e in errs))


if __name__ == "__main__":
    unittest.main()
