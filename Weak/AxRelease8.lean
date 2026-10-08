/-
Weak: **the COMPRESSED decode halves `dc_XX` of release's `rli_*` facts (second half of
`AxRelease7`)** in `AxRelease.instr4` form: at each of the five compressed release words handled
here (0x84aa c.mv, 0x60e2/0x6442/0x64a2 c.ldsp, 0x6105 c.addi16sp), `ext_decode_compressed`
yields an `i0` at EVERY `ctrlOkSW` state, and `execute i0` yields `ExecuteAs ins` at any image.

Rocq: `iris/AxRelease8.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. TYPES / SPELLING (as `AxSymEngine2` / `AxSpineOk6`): `mword n` ↦ `BitVec n`,
   `RiscvLang.mstate` ↦ `ExecSt`, `t.(sregs)` ↦ `t.regs`, `zero_extend' 12 (concat_vec u 'b"000")`
   ↦ `zero_extend (m := 12) (u +++ 0b000#3)`, `caddi16sp_imm` ↦ `caddi16spImm` (ExecSC);
   the `EvA` error type is `Sail.Error exception`.
2. DECODE PROOFS: Rocq's `kd_XXXX` lemmas (KernelDecode10/19/…, `rvc_oneshot`) are not ported;
   each decode is one kernel walk `runRead drefMisa (ext_decode_compressed h) = some (i0, true)`
   (`ax_epi_ledger_krfl`) turned into an `exec` fact by `execOfRunRead` (the `AxSymCtl3`
   recipe), using the `misa = misaC` conjunct of `ctrlOkS`.  The `rfF` footprint of each decode
   is the `AxSymCtl3.rfFDecodePH` script (Rocq `rfF_auto`).  The witness `i0` is given
   explicitly (Rocq `eexists`).

**Rocq → Lean name map.**  `dc_0a` `dc0a`, `dc_22` `dc22`, `dc_24` `dc24`, `dc_26` `dc26`,
`dc_28` `dc28` (none in the duplicated-name table).  Lean-only (file-qualified):
`AxRelease8.misaOfSW`.

**Dropped:** nothing (Rocq 5 lemmas; Lean 5 + 1 Lean-only).
-/
import Weak.AxDataX4
import Weak.AxSpineOk7
import Weak.AxSymCtl3

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only) the `misa` conjunct of the S-mode regime. -/
theorem AxRelease8.misaOfSW {T : PTree} {satp0 : BitVec 64} {rs : RegFile} :
    ctrlOkSW T satp0 rs → rs .misa = misaC := fun h => h.1.2.2.1

/-- One decode: `rfF` and the kernel walk at `drefMisa` give the regime-wide `EvA` fact. -/
local macro "ax_release8_dec" : tactic => `(tactic| (
  intro T satp0 σ t Hc;
  refine EvAOfRfF _ _ ?_ t _ t ?_;
  · unfold ext_decode_compressed encdec_compressed_backwards;
    simp (config := { decide := true }) only [↓reduceIte];
    rff_auto
  · refine execOfRunRead drefMisa _ t _ true ?_ (by ax_epi_ledger_krfl);
    intro r v hv;
    unfold drefMisa at hv;
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv;
    subst hv;
    exact AxRelease8.misaOfSW Hc))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `dc_0a`: `c.mv s1, a0`. -/
theorem dc0a : ∃ i0 : instruction,
    (∀ T satp0 (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x84aa#16) t) ∧
    (∀ img (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .ExecuteAs (.RTYPE (.Regidx 10#5, zreg, .Regidx 9#5, .ADD)) ∧ t' = t)
      (execute i0) t) := by
  refine ⟨.C_MV (.Regidx 9#5, .Regidx 10#5), ?_, ?_⟩
  · ax_release8_dec
  · intro img t
    refine EvAOfRfF img _ ?_ t _ t (execExecuteCMV _ _ t)
    exact True.intro

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `dc_22`: `c.ldsp ra, 24(sp)`. -/
theorem dc22 : ∃ i0 : instruction,
    (∀ T satp0 (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x60e2#16) t) ∧
    (∀ img (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .ExecuteAs (.LOAD (zero_extend (m := 12) ((3#6 : BitVec 6) +++ 0b000#3),
          sp, .Regidx 1#5, false, 8)) ∧ t' = t)
      (execute i0) t) := by
  refine ⟨.C_LDSP (3#6, .Regidx 1#5), ?_, ?_⟩
  · ax_release8_dec
  · intro img t
    refine EvAOfRfF img _ ?_ t _ t (execExecuteCLDSP _ _ t)
    exact True.intro

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `dc_24`: `c.ldsp s0, 16(sp)`. -/
theorem dc24 : ∃ i0 : instruction,
    (∀ T satp0 (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x6442#16) t) ∧
    (∀ img (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .ExecuteAs (.LOAD (zero_extend (m := 12) ((2#6 : BitVec 6) +++ 0b000#3),
          sp, .Regidx 8#5, false, 8)) ∧ t' = t)
      (execute i0) t) := by
  refine ⟨.C_LDSP (2#6, .Regidx 8#5), ?_, ?_⟩
  · ax_release8_dec
  · intro img t
    refine EvAOfRfF img _ ?_ t _ t (execExecuteCLDSP _ _ t)
    exact True.intro

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `dc_26`: `c.ldsp s1, 8(sp)`. -/
theorem dc26 : ∃ i0 : instruction,
    (∀ T satp0 (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x64a2#16) t) ∧
    (∀ img (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .ExecuteAs (.LOAD (zero_extend (m := 12) ((1#6 : BitVec 6) +++ 0b000#3),
          sp, .Regidx 9#5, false, 8)) ∧ t' = t)
      (execute i0) t) := by
  refine ⟨.C_LDSP (1#6, .Regidx 9#5), ?_, ?_⟩
  · ax_release8_dec
  · intro img t
    refine EvAOfRfF img _ ?_ t _ t (execExecuteCLDSP _ _ t)
    exact True.intro

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `dc_28`: `c.addi16sp sp, 32`. -/
theorem dc28 : ∃ i0 : instruction,
    (∀ T satp0 (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x6105#16) t) ∧
    (∀ img (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .ExecuteAs (.ITYPE (caddi16spImm 2#6, sp, sp, .ADDI)) ∧ t' = t)
      (execute i0) t) := by
  refine ⟨.C_ADDI16SP 2#6, ?_, ?_⟩
  · ax_release8_dec
  · intro img t
    refine EvAOfRfF img _ ?_ t _ t (execExecuteCADDI16SP _ t)
    exact True.intro

end Weak
