"""tools/vtest/vtest.py: the capture rendering, the generated tree, the table.

The last class is the conformance suite's `check-gen`: every generated file
under vtest-lean/ must be exactly what the generator writes from the captures
and the cases' `vtest:` directives, so a hand edit to a capture or a proof
(or a directive changed without regenerating) is caught without Lean."""
import contextlib
import importlib.util
import io
import os
import shutil
import tempfile
import unittest
import warnings
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PATH = ROOT / "tools" / "vtest" / "vtest.py"
SPEC = importlib.util.spec_from_file_location("vtest", PATH)
vtest = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(vtest)


def setUpModule():
    # the tool reads and writes with bare `open(...)`, as the Rocq one does
    warnings.simplefilter("ignore", ResourceWarning)


class Sandbox:
    """Point vtest.py at a scratch copy of vtest-lean/ (and an empty build)."""

    def __enter__(self):
        self.d = tempfile.mkdtemp(prefix="vtest-test-")
        self.saved = (vtest.LEANROOT, vtest.LEANDIR, vtest.PROJECT, vtest.OLEANDIR)
        vtest.LEANROOT = os.path.join(self.d, "vtest-lean")
        vtest.LEANDIR = os.path.join(vtest.LEANROOT, "Vtest")
        vtest.PROJECT = os.path.join(vtest.LEANROOT, "Vtest.lean")
        vtest.OLEANDIR = os.path.join(self.d, "olean", "Vtest")
        return self

    def __exit__(self, *a):
        vtest.LEANROOT, vtest.LEANDIR, vtest.PROJECT, vtest.OLEANDIR = self.saved
        shutil.rmtree(self.d, ignore_errors=True)

    def touch_olean(self, pl, mod):
        p = vtest.olean(mod, pl)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w").close()


class HexTests(unittest.TestCase):
    def test_round_trip(self):
        for bs in ([], [0], [255, 0, 16], list(range(256)) * 17):
            self.assertEqual(vtest.unhex(vtest.hexlit(bs).split('"')[1]), bs)

    def test_a_region_is_wrapped_and_one_literal(self):
        lit = vtest.hexlit([7] * 100)
        self.assertEqual(lit.count('"'), 2)
        self.assertIn("\n", lit)
        self.assertEqual(vtest.hexlits(lit), [[7] * 100])


class CaptureTests(unittest.TestCase):
    CAP = dict(case="core_smoke", hart=1, regions="dmaRegions",
               uart_input=[(0, 0x41), (1, 0x50)], text=[0x13, 0, 0, 0] * 9,
               serials=[[0x68, 0x69], []], disk=[(5, [1, 2, 3] * 170 + [4, 5])],
               results=[[0x45, 0x4e, 0x4f, 0x44] + [0] * 4092, [9] * 4096])

    def test_emit_then_read_back(self):
        with Sandbox():
            c = self.CAP
            vtest.emit_capture("qemu", "CoreSmokeHart1", c["case"], c["hart"], c["text"],
                               c["results"], c["serials"], c["disk"],
                               regions=c["regions"], uart_input=c["uart_input"])
            back = vtest.read_capture(vtest.rp("CoreSmokeHart1Test.lean", "qemu"),
                                      vtest.rp("CoreSmokeHart1Run.lean", "qemu"))
            self.assertEqual(back, c)

    def test_a_run_that_observed_nothing_is_not_written(self):
        with Sandbox():
            c = self.CAP
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertIsNone(vtest.emit_capture("qemu", "X", c["case"], 0, c["text"], [],
                                                     c["serials"], []))
            self.assertFalse(os.path.exists(vtest.rp("XRun.lean", "qemu")))

    def test_a_recapture_adds_unless_the_image_changed(self):
        with Sandbox():
            c = self.CAP
            vtest.emit_capture("qemu", "M", c["case"], 0, c["text"], c["results"][:1],
                               c["serials"], [])
            t, r = vtest.rp("MTest.lean", "qemu"), vtest.rp("MRun.lean", "qemu")
            alts, _ = vtest.merge_observations(r, t, c["text"], [c["results"][1]])
            self.assertEqual(len(alts), 2)
            alts, note = vtest.merge_observations(r, t, c["text"] + [1], [c["results"][1]])
            self.assertEqual(len(alts), 1)
            self.assertIn("image changed", note)


class ScheduleTests(unittest.TestCase):
    def test_csched(self):
        self.assertEqual(
            vtest.parse_csched("2*0,3*1;1*0s"),
            ["List.replicate 2 (false, false) ++ List.replicate 3 (true, false)",
             "List.replicate 1 (false, true)"])


class TableTests(unittest.TestCase):
    def test_the_olean_is_the_evidence(self):
        with Sandbox() as sb:
            c = CaptureTests.CAP
            vtest.emit_capture("qemu", "CoreSmoke", "core_smoke", 0, c["text"],
                               c["results"][:1], [[], []], [])
            vtest.emit_passes()
            # listed in the project, nothing built anywhere: "unbuilt"
            open(vtest.PROJECT, "w").write("import Vtest.QEMU.CoreSmokePass\n")
            self.assertEqual(vtest._run_state("core_smoke", "qemu"), "unbuilt")
            # something else was built and this one was not: no proof
            sb.touch_olean("qemu", "OtherPass")
            vtest.emit_capture("qemu", "Other", "core_smoke", 0, c["text"],
                               c["results"][:1], [[], []], [])
            self.assertEqual(vtest._run_state("core_smoke", "qemu"), "no-proof")
            sb.touch_olean("qemu", "CoreSmokePass")
            self.assertEqual(vtest._run_state("core_smoke", "qemu"), "agree")
            # a case that does not declare the platform
            self.assertEqual(vtest._run_state("disk_rw", "jh7110"), "excluded")

    def test_flip_and_project_from_build(self):
        with Sandbox() as sb:
            c = CaptureTests.CAP
            for m in ("CoreSmoke", "CoreCsrwide"):
                vtest.emit_capture("qemu", m, "core_smoke" if m == "CoreSmoke" else "core_csrwide",
                                   0, c["text"], c["results"][:1], [[], []], [])
            vtest.emit_passes()
            self.assertEqual(vtest.verdict_of_file("CoreCsrwide", "qemu"), "agree")
            # only CoreSmoke compiled: the other is re-emitted in the other form
            vtest.emit_passes(built={"QEMU/CoreSmoke"})
            self.assertEqual(vtest.verdict_of_file("CoreSmoke", "qemu"), "agree")
            self.assertEqual(vtest.verdict_of_file("CoreCsrwide", "qemu"), "stuck")
            sb.touch_olean("qemu", "CoreSmokePass")
            _, _, passes = vtest.write_project(from_build=True)
            self.assertEqual(passes, ["QEMU/CoreSmokePass"])
            mods = vtest.project_modules()
            self.assertIn("Vtest.QEMU.CoreCsrwideRun", mods)
            self.assertNotIn("Vtest.QEMU.CoreCsrwidePass", mods)


class GeneratedTreeTests(unittest.TestCase):
    """vtest-lean/ is what the generator writes: re-render a copy and diff."""

    def test_captures_proofs_and_project_are_regenerable(self):
        real = ROOT / "vtest-lean"
        with Sandbox():
            shutil.copytree(real, vtest.LEANROOT)
            before = {p.relative_to(vtest.LEANROOT): p.read_text()
                      for p in Path(vtest.LEANROOT).rglob("*.lean")}
            self.assertTrue(len(before) > 400)
            vtest.reshape_captures()
            vtest.emit_passes()
            vtest.write_project()
            after = {p.relative_to(vtest.LEANROOT): p.read_text()
                     for p in Path(vtest.LEANROOT).rglob("*.lean")}
            self.assertEqual(sorted(before), sorted(after))
            moved = [str(k) for k in before if before[k] != after[k]]
            self.assertEqual(moved, [], "generated files differ from the generator's output "
                             "(run `tools/ci/vtest.sh runs`, or undo the hand edit)")

    def test_every_case_with_a_capture_has_its_source(self):
        for pl in vtest.PLATFORMS:
            for m in vtest.run_modules(pl):
                n = vtest.case_of_module(m, pl)
                self.assertTrue((ROOT / "tools" / "vtest" / "tests" / (n + ".S")).exists(), m)
                self.assertIn(pl, vtest.platforms_of(n), "%s/%s" % (pl, m))


if __name__ == "__main__":
    unittest.main()
