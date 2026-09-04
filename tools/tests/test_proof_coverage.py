import importlib.util
import sys
import unittest
from pathlib import Path


COVERAGE_PATH = Path(__file__).resolve().parents[1] / "proof_coverage.py"
SPEC = importlib.util.spec_from_file_location("proof_coverage", COVERAGE_PATH)
coverage = importlib.util.module_from_spec(SPEC)
# Registered BEFORE exec: proof_coverage.py declares `@dataclass`es, and
# dataclasses resolves a field's annotation through `sys.modules[cls.__module__]`
# -- which is None, and an AttributeError, for a module loaded by path alone.
sys.modules[SPEC.name] = coverage
SPEC.loader.exec_module(coverage)


# The shape that made sys_open / sys_unlink / sys_mknod read as `assumed`: the
# `_body` is one line over a FRAME predicate, and the entry pin lives there.
FRAME = """
Definition wp_sys_open_au_frame
    (m : regfile) (EXTRA : iProp Sigma) (ARMS : ustate -> iProp Sigma) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_open in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  kernel_text -* pc_is pcE -* EXTRA -*
    WP Loop {{ pc_is ret_tgt -* ARMS }}.
"""

BODY = """
Definition wp_sys_open_au_plain_body (m : regfile) :=
  om_create vom = false ->
  wp_sys_open_au_frame m (open_au_pre_plain P) (open_arms_plain P).
"""


class EntryViaFrameTests(unittest.TestCase):
    def local_defs(self, *texts):
        out = {}
        for t in texts:
            name = coverage.re.search(r"Definition\s+(\w+)", t).group(1)
            out[name] = t
        return out

    def test_pin_is_read_out_of_the_applied_frame(self):
        pins, wtext = coverage.entry_via_frame(BODY, self.local_defs(FRAME))
        self.assertEqual(pins, {("sys_open", 0): "wp_sys_open_au_frame"})
        # and the frame's ra-derived continuation makes it a WHOLE function,
        # not a fragment -- the combined text is what carries the `pc_is
        # ret_tgt` that decides it.
        self.assertTrue(coverage.runs_to_end(wtext, "sys_open", {}))

    def test_frame_the_body_does_not_apply_is_not_read(self):
        unapplied = FRAME.replace("wp_sys_open_au_frame", "wp_other_frame")
        pins, _ = coverage.entry_via_frame(BODY, self.local_defs(unapplied))
        self.assertEqual(pins, {})

    def test_a_frame_with_no_pin_contributes_nothing(self):
        pinless = FRAME.replace(
            "let pcE : mword 64 := mword_of_int KernelSyms.sys_open in", "")
        pins, _ = coverage.entry_via_frame(BODY, self.local_defs(pinless))
        self.assertEqual(pins, {})

    def test_a_nonzero_offset_stays_a_fragment_pin(self):
        frag = FRAME.replace("KernelSyms.sys_open", "KernelSyms.sys_open + 0x28")
        pins, _ = coverage.entry_via_frame(BODY, self.local_defs(frag))
        self.assertEqual(pins, {("sys_open", 0x28): "wp_sys_open_au_frame"})

    def test_disagreeing_frames_are_reported_not_chosen_between(self):
        second = (FRAME.replace("wp_sys_open_au_frame", "wp_sys_open_au_frame2")
                       .replace("KernelSyms.sys_open", "KernelSyms.sys_unlink"))
        body = BODY.replace(
            "wp_sys_open_au_frame m (open_au_pre_plain P)",
            "wp_sys_open_au_frame m (open_au_pre_plain P) "
            "/\\ wp_sys_open_au_frame2 m (open_au_pre_plain P)")
        pins, _ = coverage.entry_via_frame(body, self.local_defs(FRAME, second))
        self.assertEqual(len(pins), 2)


class ModuleInstanceTests(unittest.TestCase):
    def test_plain_instance(self):
        m = coverage.MODINST_DECL.match(
            "Module Kfree := KfreeProof Acquire MemsetPage Release.")
        self.assertEqual(m.group(1), "Kfree")
        self.assertEqual(m.group(2), "KfreeProof")
        self.assertEqual(m.group(3).split(),
                         ["Acquire", "MemsetPage", "Release"])

    def test_import_modifier_is_an_instance_not_an_unrecognized_form(self):
        # ProofSysExec.v / ProofSysExecAU.v both open their shared part-functor
        # this way; before it was recognized the line reached the catch-all as
        # a consistency error on a legal declaration.
        m = coverage.MODINST_DECL.match(
            "Module Import Parts :=\n  SysExecParts Argaddr Argstr Memset.")
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), "Parts")
        self.assertEqual(m.group(2), "SysExecParts")

    def test_export_modifier_too(self):
        m = coverage.MODINST_DECL.match("Module Export P := F A.")
        self.assertEqual((m.group(1), m.group(2)), ("P", "F"))

    def test_an_ascribed_instance_is_still_not_an_instance(self):
        # `Module W : WALK := WalkProof.` is rejected elsewhere by
        # MODASCINST_DECL, which is matched first; MODINST_DECL must not
        # swallow the import-modifier spelling of it either.
        self.assertIsNone(
            coverage.MODINST_DECL.match("Module Import W : WALK := WalkProof."))


if __name__ == "__main__":
    unittest.main()
