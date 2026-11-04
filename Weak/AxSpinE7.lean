/-
Weak: **PHASE 5, stage 2 prerequisites: the INSTRUCTION FACTS of xv6's REAL `mycpu`** (14
instructions at `KernelSyms.mycpu`) for the positional engine (`AxSpinE`).

Rocq: `iris/AxSpinE7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `mycpuText σi T`: the 14 words are text at their pcs (`textAtS` for the 12 compressed ones —
   mycpu + 0x00 … 0x1e, `textAt4S` for the two 4-byte ones at + 0x0e (auipc) and + 0x12
   (addi)) — a fact about the IMAGE and the page table, discharged concretely elsewhere.
§2 `tokR` / `tokB`: `textOkB` of an instruction from its text fact, the decode and (compressed)
   the expansion as read-free `EvA` facts at every regime state.  The expanded instructions are
   `ins00` … `ins1e`.  The two 4-byte decodes `rfFDec0e`/`rfFDec12`, `dec0e`/`dec12` are here;
   the 14 `tok_xx` are in AxSpinE7b/7g/7e/7f.
§3 the `CertC` (SC exec) facts of the register-only instructions with SYMBOLIC register values
   (`certAddi`, `certAdd`, `certAddiw`, `certSlli`, `certAuipc`; c.ret is
   `AxSymCtl2.certJALR`).

## Deviations from Rocq

1. KERNEL DRIFT: this tree's kernel has `mycpu` at 0x8000195c (`KernelSyms.«mycpu»`), and its
   `addi a0,a0,…` at mycpu + 0x12 is `0xbc650513` (Rocq `0xa8450513`): `W12 = 0xbc650513#32` and
   `ins12`'s immediate is `0xbc6#12` (Rocq `2692` = 0xa84).  The other 13 words match Rocq (see
   `AxSpinSpikeRun.mycpuInstrs`).
2. TYPES / SPELLING (as `AxRelease7` deviation 1): `mword n` ↦ `BitVec n`,
   `mword_of_int k : mword n` ↦ `k#n`, `mstate` ↦ `ExecSt`, `img_S` ↦ `imgS`, `ctrl_ok_SW` ↦
   `ctrlOkSW`, `text_at_S`/`text_at4_S` ↦ `textAtS`/`textAt4S`, `sign_extend' 12` ↦
   `sign_extend (m := 12)`, `zero_extend' 12 (concat_vec u 'b"000")` ↦
   `zero_extend (m := 12) (u +++ 0b000#3)`, `zeros' 12` ↦ `zeros (n := 12)`, `caddi4spn_imm` ↦
   `caddi4spnImm`, `add_vec` ↦ `+`, `subrange_vec_dec x 31 0` ↦ `Sail.BitVec.extractLsb x 31 0`,
   `Z.sub log2_xlen 1` ↦ `Functions.log2_xlen -i 1`, `gpr_val` ↦ `gprVal`, `auipc_off` ↦
   `auipcOff`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `cfg_ok` ↦ `cfgOk`, `MISA_C` ↦ `misaC`.
   `W0e`/`W12` are `BitVec 32` constants (Rocq `Z`, used only as `mword_of_int W : mword 32`).
   `pcm off` is `BitVec.ofInt 64 (mycpu + off)` (`off : Int`); Rocq `hw` is `AxSpinE7.hw`
   (file-qualified: `hw` is a ubiquitous hypothesis name).
3. `tokR`'s decode premise is stated at the states with `misa = misaC` (Rocq: at the states whose
   misa C bit is set).  `misaC_of` is ported as stated, but every `ctrlOkSW` state has
   `misa = misaC`, so `tokR` is MORE general; this is the premise the Lean decode walks
   (`runRead drefMisa …`, `AxRelease7.dcOf`) deliver.
4. Q7 (`AxSpinE` deviation 2): `textOkB`'s base arm carries `sfAnnB 32 w = false`, so `tokB`
   takes `sfAnnB 32 w = false` after the text fact.
5. DECODE PROOFS (as `WkEntryNew`/`AxRelease8`): Rocq's `kd_00011517`/`kd_a8450513`
   (KernelDecode*) are not ported; `dec0e`/`dec12` are the kernel walks of the decoder on the
   machine and supervisor reference maps (`AxSpinE7.walk0eM/S`, `walk12M/S`, `kernel_rfl`)
   combined by `WkEntryNew.execAnyCfg`.  `rfFDec0e`/`rfFDec12` are `rff_auto` after pruning the
   decoder's pattern tests on the literal (the `AxSymCtl3.rfFDecodePH` recipe).
6. Section variables (`σi T satp0`, `ctrlOk`) are explicit arguments; the section notations
   `img`/`ctrl_ok`/`EvM` are unfolded.

**Rocq → Lean name map.**  `pcm` `pcm`, `hw` `AxSpinE7.hw`, `W0e` `W0e`, `W12` `W12`,
`ins00` … `ins1e` same, `mycpu_text` `mycpuText`, `misaC_of` `misaCOf`, `cfg_of` `cfgOf`,
`tokR` `tokR`, `tokB` `tokB`, `rfF_dec0e` `rfFDec0e`, `rfF_dec12` `rfFDec12`, `dec0e` `dec0e`,
`dec12` `dec12`, `cert_addi` `certAddi`, `cert_add` `certAdd`, `cert_addiw` `certAddiw`,
`cert_slli` `certSlli`, `cert_auipc` `certAuipc` (none in the duplicated-name table).
Lean-only (file-qualified): `AxSpinE7.walk0eM`, `AxSpinE7.walk0eS`, `AxSpinE7.walk12M`,
`AxSpinE7.walk12S`.

**Dropped:** nothing (Rocq 32 definitions/lemmas; Lean 32 + 4 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE
import Weak.WkEntryNew

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pcm`: the address `mycpu + off`. -/
def pcm (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«mycpu» : Int) + off)
/-- Rocq `hw`: a halfword literal. -/
def AxSpinE7.hw (h : Int) : BitVec 16 := BitVec.ofInt 16 h
/-- Rocq `W0e`: the 4-byte word at mycpu + 0x0e (`auipc a0, 0x11`). -/
def W0e : BitVec 32 := 0x00011517#32
/-- Rocq `W12`: the 4-byte word at mycpu + 0x12 (`addi a0, a0, …`; deviation 1). -/
def W12 : BitVec 32 := 0xbc650513#32

/-! The expanded instructions (Rocq `CodeMycpu.myi_xx`). -/

/-- Rocq `ins00`: `c.addi sp, -16`. -/
def ins00 : instruction := .ITYPE (sign_extend (m := 12) (48#6), .Regidx 2#5, .Regidx 2#5, .ADDI)
/-- Rocq `ins02`: `c.sdsp ra, 8(sp)`. -/
def ins02 : instruction := .STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 1#5, sp, 8)
/-- Rocq `ins04`: `c.sdsp s0, 0(sp)`. -/
def ins04 : instruction := .STORE (zero_extend (m := 12) (0#6 +++ 0b000#3), .Regidx 8#5, sp, 8)
/-- Rocq `ins06`: `c.addi4spn s0, sp, 16`. -/
def ins06 : instruction := .ITYPE (caddi4spnImm 4#8, sp, creg2reg_idx (.Cregidx 0#3), .ADDI)
/-- Rocq `ins08`: `c.mv a5, tp`. -/
def ins08 : instruction := .RTYPE (.Regidx 4#5, zreg, .Regidx 15#5, .ADD)
/-- Rocq `ins0a`: `c.addiw a5, 0` (sext.w). -/
def ins0a : instruction := .ADDIW (sign_extend (m := 12) (0#6), .Regidx 15#5, .Regidx 15#5)
/-- Rocq `ins0c`: `c.slli a5, 7`. -/
def ins0c : instruction := .SHIFTIOP (7#6, .Regidx 15#5, .Regidx 15#5, .SLLI)
/-- Rocq `ins0e`: `auipc a0, 0x11`. -/
def ins0e : instruction := .UTYPE (17#20, .Regidx 10#5, .AUIPC)
/-- Rocq `ins12`: `addi a0, a0, …` (deviation 1: immediate `0xbc6`). -/
def ins12 : instruction := .ITYPE (0xbc6#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
/-- Rocq `ins16`: `c.add a0, a5`. -/
def ins16 : instruction := .RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 10#5, .ADD)
/-- Rocq `ins18`: `c.ldsp ra, 8(sp)`. -/
def ins18 : instruction := .LOAD (zero_extend (m := 12) (1#6 +++ 0b000#3), sp, .Regidx 1#5, false, 8)
/-- Rocq `ins1a`: `c.ldsp s0, 0(sp)`. -/
def ins1a : instruction := .LOAD (zero_extend (m := 12) (0#6 +++ 0b000#3), sp, .Regidx 8#5, false, 8)
/-- Rocq `ins1c`: `c.addi sp, 16`. -/
def ins1c : instruction := .ITYPE (sign_extend (m := 12) (16#6), .Regidx 2#5, .Regidx 2#5, .ADDI)
/-- Rocq `ins1e`: `c.ret`. -/
def ins1e : instruction := .JALR (zeros (n := 12), .Regidx 1#5, zreg)

section mfacts
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-! # 1. The text -/

/-- Rocq `mycpu_text`. -/
def mycpuText : Prop :=
  textAtS σi T (pcm 0x00) (AxSpinE7.hw 0x1141) ∧ textAtS σi T (pcm 0x02) (AxSpinE7.hw 0xe406) ∧
  textAtS σi T (pcm 0x04) (AxSpinE7.hw 0xe022) ∧ textAtS σi T (pcm 0x06) (AxSpinE7.hw 0x0800) ∧
  textAtS σi T (pcm 0x08) (AxSpinE7.hw 0x8792) ∧ textAtS σi T (pcm 0x0a) (AxSpinE7.hw 0x2781) ∧
  textAtS σi T (pcm 0x0c) (AxSpinE7.hw 0x079e) ∧
  textAt4S σi T (pcm 0x0e) W0e ∧
  textAt4S σi T (pcm 0x12) W12 ∧
  textAtS σi T (pcm 0x16) (AxSpinE7.hw 0x953e) ∧
  textAtS σi T (pcm 0x18) (AxSpinE7.hw 0x60a2) ∧ textAtS σi T (pcm 0x1a) (AxSpinE7.hw 0x6402) ∧
  textAtS σi T (pcm 0x1c) (AxSpinE7.hw 0x0141) ∧ textAtS σi T (pcm 0x1e) (AxSpinE7.hw 0x8082)

/-! # 2. `textOkB` of every instruction -/

/-- Rocq `misaC_of`. -/
theorem misaCOf (t : ExecSt) : ctrlOkSW T satp0 t.regs → (_get_Misa_C (t.regs .misa) == 1#1) = true := by
  intro Hc
  rw [Hc.1.2.2.1]
  decide

/-- Rocq `cfg_of`. -/
theorem cfgOf (t : ExecSt) : ctrlOkSW T satp0 t.regs → t.regs .misa = misaC ∧ cfgOk t :=
  fun Hc => ⟨Hc.1.2.2.1, .inr ⟨Hc.1.1, Hc.1.2.2.2.1⟩⟩

/-- Rocq `tokR` (deviation 3: the decode premise at the `misa = misaC` states). -/
theorem tokR (pc : BitVec 64) (h : BitVec 16) (i0 ins : instruction) :
    textAtS σi T pc h → rfF (ext_decode_compressed h) →
    (∀ s : ExecSt, s.regs .misa = misaC → exec (ext_decode_compressed h) s = some (i0, s)) →
    rfF (execute i0) → (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s)) →
    textOkB σi T satp0 pc true ins := by
  intro Hat Hrd Hdec Hre Hexp
  rw [textOkB, if_pos rfl]
  exact ⟨h, i0, Hat, fun t Hc => EvAOfRfF _ _ Hrd t i0 t (Hdec t Hc.1.2.2.1), nrdOfRfF _ Hrd,
    fun t => EvAOfRfF _ _ Hre t _ t (Hexp t), nrdOfRfF _ Hre⟩

/-- Rocq `tokB` (deviation 4: the word is not an sfence word). -/
theorem tokB (pc : BitVec 64) (w : BitVec 32) (ins : instruction) :
    textAt4S σi T pc w → sfAnnB 32 w = false → rfF (ext_decode w) →
    (∀ s : ExecSt, s.regs .misa = misaC → cfgOk s → exec (ext_decode w) s = some (ins, s)) →
    textOkB σi T satp0 pc false ins := by
  intro Hat Hsf Hrd Hdec
  rw [textOkB, if_neg Bool.false_ne_true]
  refine ⟨w, Hat, Hsf, fun t Hc => ?_, nrdOfRfF _ Hrd⟩
  obtain ⟨Hm, Hcfg⟩ := cfgOf T satp0 t Hc
  exact EvAOfRfF _ _ Hrd t ins t (Hdec t Hm Hcfg)

end mfacts

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec0e`. -/
theorem rfFDec0e : rfF (ext_decode W0e) := by
  unfold W0e ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec12`. -/
theorem rfFDec12 : rfF (ext_decode W12) := by
  unfold W12 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 5) the decode walk of `W0e` on the machine reference map. -/
theorem AxSpinE7.walk0eM : runRead drefM (ext_decode W0e) = some (ins0e, false) := by kernel_rfl
/-- (Lean-only, deviation 5) the decode walk of `W0e` on the supervisor reference map. -/
theorem AxSpinE7.walk0eS : runRead WkEntryNew.drefS0 (ext_decode W0e) = some (ins0e, false) := by
  kernel_rfl
/-- (Lean-only, deviation 5) the decode walk of `W12` on the machine reference map. -/
theorem AxSpinE7.walk12M : runRead drefM (ext_decode W12) = some (ins12, false) := by kernel_rfl
/-- (Lean-only, deviation 5) the decode walk of `W12` on the supervisor reference map. -/
theorem AxSpinE7.walk12S : runRead WkEntryNew.drefS0 (ext_decode W12) = some (ins12, false) := by
  kernel_rfl

end walks

/-- Rocq `dec0e` (deviation 5). -/
theorem dec0e (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode W0e) s = some (ins0e, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinE7.walk0eM AxSpinE7.walk0eS s

/-- Rocq `dec12` (deviation 5). -/
theorem dec12 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode W12) s = some (ins12, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinE7.walk12M AxSpinE7.walk12S s

/-! # 3. The SC exec (`CertC`) facts, symbolic register values -/

section certs
variable (ctrlOk : RegFile → Prop)

/-- Rocq `cert_addi`. -/
theorem certAddi (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (imm : BitVec 12) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) none
      (some (rd, gprVal rs rs1 + sign_extend (m := 64) imm)) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteITYPEADDIGpr]
  unfold gprAddiVal
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

/-- Rocq `cert_add`. -/
theorem certAdd (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs2 rs1 rd : BitVec 5) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) none
      (some (rd, gprVal rs rs1 + gprVal rs rs2)) := by
  intro _ s_pc _ _ _ Hag
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD) s_pc = _
  rw [execExecuteRTYPEADDGpr]
  unfold gprRdVal
  have h1 : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  have h2 : s_pc.gpr rs2 = gprVal rs rs2 := gprValAgree _ _ rs2 Hag
  rw [h1, h2]
  rfl

/-- Rocq `cert_addiw`. -/
theorem certAddiw (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (imm : BitVec 12) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.ADDIW (imm, .Regidx rs1, .Regidx rd)) none
      (some (rd, sign_extend (m := 64)
        (Sail.BitVec.extractLsb (gprVal rs rs1 + sign_extend (m := 64) imm) 31 0))) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteADDIWGpr]
  unfold gprAddiwVal
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

/-- Rocq `cert_slli`. -/
theorem certSlli (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI)) none
      (some (rd, shift_bits_left (gprVal rs rs1)
        (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteSHIFTIOPSLLIGpr]
  unfold gprSlliVal gprSrc
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

/-- Rocq `cert_auipc`. -/
theorem certAuipc (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5)
    (imm : BitVec 20) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.UTYPE (imm, .Regidx rd, .AUIPC)) none (some (rd, pc + auipcOff imm)) := by
  intro _ s_pc _ HPC _ _
  rw [execExecuteUTYPEAUIPCGpr, HPC]
  rfl

end certs

end Weak
