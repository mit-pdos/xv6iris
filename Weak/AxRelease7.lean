/-
Weak: **the COMPRESSED decode halves `dc_XX` of release's `rli_*` facts in `instr4` form** (first
half; `AxRelease8` the second): at each of these five compressed release words,
`ext_decode_compressed` yields `i0` (at EVERY `ctrlOkSW` state, any image) and `execute i0` yields
`ExecuteAs ins` (at any state, any image), as `EvA` facts with no failure outcome.

Rocq: `iris/AxRelease7.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. SPELLING (as `AxSymCtl3` deviation 1): `mword n` ↦ `BitVec n`, `mword_of_int k : mword n` ↦
   `k#n`, `RiscvLang.mstate` ↦ `ExecSt`, `t.(sregs)` ↦ `t.regs`, `img_S` ↦ `imgS`, `ctrl_ok_SW` ↦
   `ctrlOkSW`, `sign_extend' 12` ↦ `sign_extend (m := 12)`, `zero_extend' 12 (concat_vec u 'b"000")`
   ↦ `zero_extend (m := 12) (u +++ 0b000#3)`, `caddi4spn_imm` ↦ `caddi4spnImm` (`ExecSC`), the
   failure predicate's `exception` ↦ `Sail.Error exception`.
2. The DECODE halves (Rocq: `kd_XXXX` = `rvc_oneshot` + `vm_compute` on the misa C bit) go, as
   `AxSymCtl3.execDecodePH`, through the decoder's READ-ONLY WALK (`runRead`, kernel-evaluated by
   `ax_epi_ledger_krfl`) at the reference map `MachCSL.drefMisa` and `execOfRunRead`; the misa
   fact is `ctrlOkSW`'s `rs .misa = misaC` conjunct.  The register-only footprint of each decode
   (`rfF`) is `rff_auto` after pruning the decoder's pattern tests on the literal (as
   `AxSymCtl3.rfFDecodePH`).  The witness `i0` is given explicitly (Rocq `eexists`).
3. The Lean-only `AxRelease7.dcOf` packages the common proof (Rocq repeats the script inline).

**Rocq → Lean name map.**  `dc_00` `dc00`, `dc_02` `dc02`, `dc_04` `dc04`, `dc_06` `dc06`,
`dc_08` `dc08` (none in the duplicated-name table).  Lean-only (file-qualified):
`AxRelease7.dcOf`, `AxRelease7.rfFDec1101`/`rfFDecEc06`/`rfFDecE822`/`rfFDecE426`/`rfFDec1000`.

**Dropped:** nothing.  Rocq 5 lemmas; Lean 5 + 6 Lean-only.
-/
import Weak.AxDataX4
import Weak.AxSymCtl3

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only) the common shape of a `dc_XX` fact: a register-only decode whose read-only walk
at `drefMisa` yields `i0`, and a register-only `execute i0` that returns `ExecuteAs ins`. -/
theorem AxRelease7.dcOf (h : BitVec 16) (i0 ins : instruction)
    (hrf : rfF (ext_decode_compressed h))
    (hw : runRead drefMisa (ext_decode_compressed h) = some (i0, true))
    (hrfe : rfF (execute i0))
    (hex : ∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s)) :
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs ins ∧ t' = t) (execute i0) t) := by
  refine ⟨?_, ?_⟩
  · intro T satp0 σ t Hc
    refine EvAOfRfF _ _ hrf t i0 t ?_
    refine execOfRunRead drefMisa _ t _ true ?_ hw
    intro r v hv
    unfold drefMisa at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
    subst hv
    exact Hc.1.2.2.1
  · intro img t
    exact EvAOfRfF _ _ hrfe t _ t (hex t)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxRelease7.rfFDec1101 : rfF (ext_decode_compressed 0x1101#16) := by
  unfold ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxRelease7.rfFDecEc06 : rfF (ext_decode_compressed 0xec06#16) := by
  unfold ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxRelease7.rfFDecE822 : rfF (ext_decode_compressed 0xe822#16) := by
  unfold ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxRelease7.rfFDecE426 : rfF (ext_decode_compressed 0xe426#16) := by
  unfold ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem AxRelease7.rfFDec1000 : rfF (ext_decode_compressed 0x1000#16) := by
  unfold ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

/-- Rocq `dc_00`: `c.addi sp, -32` (0x1101). -/
theorem dc00 : ∃ i0 : instruction,
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x1101#16) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs (.ITYPE (sign_extend (m := 12) (32#6), .Regidx 2#5, .Regidx 2#5,
          .ADDI)) ∧ t' = t) (execute i0) t) :=
  ⟨_, AxRelease7.dcOf _ (.C_ADDI (32#6, .Regidx 2#5)) _ AxRelease7.rfFDec1101
    (by ax_epi_ledger_krfl) True.intro (execExecuteCADDI _ _)⟩

/-- Rocq `dc_02`: `c.sdsp ra, 24(sp)` (0xec06). -/
theorem dc02 : ∃ i0 : instruction,
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0xec06#16) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs (.STORE (zero_extend (m := 12) (3#6 +++ 0b000#3), .Regidx 1#5,
          sp, 8)) ∧ t' = t) (execute i0) t) :=
  ⟨_, AxRelease7.dcOf _ (.C_SDSP (3#6, .Regidx 1#5)) _ AxRelease7.rfFDecEc06
    (by ax_epi_ledger_krfl) True.intro (execExecuteCSDSP _ _)⟩

/-- Rocq `dc_04`: `c.sdsp s0, 16(sp)` (0xe822). -/
theorem dc04 : ∃ i0 : instruction,
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0xe822#16) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs (.STORE (zero_extend (m := 12) (2#6 +++ 0b000#3), .Regidx 8#5,
          sp, 8)) ∧ t' = t) (execute i0) t) :=
  ⟨_, AxRelease7.dcOf _ (.C_SDSP (2#6, .Regidx 8#5)) _ AxRelease7.rfFDecE822
    (by ax_epi_ledger_krfl) True.intro (execExecuteCSDSP _ _)⟩

/-- Rocq `dc_06`: `c.sdsp s1, 8(sp)` (0xe426). -/
theorem dc06 : ∃ i0 : instruction,
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0xe426#16) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs (.STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 9#5,
          sp, 8)) ∧ t' = t) (execute i0) t) :=
  ⟨_, AxRelease7.dcOf _ (.C_SDSP (1#6, .Regidx 9#5)) _ AxRelease7.rfFDecE426
    (by ax_epi_ledger_krfl) True.intro (execExecuteCSDSP _ _)⟩

/-- Rocq `dc_08`: `c.addi4spn s0, sp, 32` (0x1000). -/
theorem dc08 : ∃ i0 : instruction,
    (∀ (T : PTree) (satp0 : BitVec 64) (σ t : ExecSt), ctrlOkSW T satp0 t.regs →
      EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed 0x1000#16) t) ∧
    (∀ (img : Image) (t : ExecSt), EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
        (fun x t' => x = .ExecuteAs (.ITYPE (caddi4spnImm 8#8, sp, creg2reg_idx (.Cregidx 0#3),
          .ADDI)) ∧ t' = t) (execute i0) t) :=
  ⟨_, AxRelease7.dcOf _ (.C_ADDI4SPN (.Cregidx 0#3, 8#8)) _ AxRelease7.rfFDec1000
    (by ax_epi_ledger_krfl) True.intro (execExecuteCADDI4SPN _ _)⟩

end Weak
