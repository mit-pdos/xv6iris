/-
Weak: **PHASE 5, allocpid's OWN code: the INSTRUCTION FACTS of Rocq's `allocpid`** (22
instructions, 62 bytes) for the positional engine — template `AxSpinE7` (mycpu).

Rocq: `iris/AxSpinAp.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `allocpidText σi T`: the 22 words are text at their pcs (`textAtS` for the 13 compressed
   ones, `textAt4S` for the nine 4-byte ones) — a fact about the IMAGE and the page table, like
   `mycpuText`.
§2 the expanded instructions `ap00` … `ap3c` (Rocq `CodeAllocpid.apdi_XX`'s ASTs).  The two
   `auipc a0,0x11` (+0x0a, +0x26) have the SAME word as mycpu's +0x0e (`W0e`); their decode is
   `dec0e` (`ap0aIns0e`, `ap26Ins0e`).
§3 `TokC h ins`: the pc-INDEPENDENT half of a compressed instruction's `textOkB` (decode +
   expansion footprints, `tokR`'s last four premises) and `tokC` (text + `TokC` ⇒ `textOkB`);
   the `TokC` facts of the 13 halfwords are in AxSpinAp3/Ap4/Ap5, three 4-byte decodes here,
   four in AxSpinAp2, the `textOkB` facts in AxSpinAp6.

## Deviations from Rocq

1. KERNEL DRIFT, NOT CONNECTED TO THE IMAGE (orchestrator ruling, owner question Q18): this
   tree's kernel has NO `allocpid` symbol — gcc inlines it into `allocproc`
   (`allocproc + 0x38 .. + 0x94`, 0x80001baa .. 0x80001c06), a different instruction sequence
   (no frame, a pid-collision scan over `proc`, `p->pid` stored inside the critical section; see
   `AxSpinSpike`'s kernel-image notes).  Of Rocq's 22 words only `W0e` occurs there.  So the
   file is ported LITERALLY with the function base as a PARAMETER: `pca base off`
   (Rocq `pca off = allocpid + off`), and `allocpidText` takes `base`.  The words, instructions
   and decodes are Rocq's; the text facts cannot be discharged against the Lean image (the
   AxSpinAp line is not connected to it).
2. TYPES / SPELLING as `AxSpinE7` deviation 2 (`mword_of_int k : mword n` ↦ `k#n`, `text_at_S`
   ↦ `textAtS`, `sign_extend' 12` ↦ `sign_extend (m := 12)`, `zero_extend' 12 (concat_vec u
   'b"000")` ↦ `zero_extend (m := 12) (u +++ 0b000#3)`, `zeros' 12` ↦ `zeros (n := 12)`,
   `caddi16sp_imm` ↦ `caddi16spImm`, `hw` ↦ `AxSpinE7.hw`).  The `WA*` constants are
   `BitVec 32` (Rocq `Z`, used only as `mword_of_int W : mword 32`).
3. `TokC`'s decode premise is at the states with `misa = misaC` (Rocq: misa C bit set), as
   `AxSpinE7.tokR` (its deviation 3); `tokC` is then `tokR`.
4. DECODE PROOFS (as `AxSpinE7` deviation 5): Rocq's `kd_96050513`/`kd_00009797`/
   `kd_80078793` (KernelDecode*) are not ported; `decA0e`/`decA16`/`decA1a` are kernel walks
   of the decoder on the machine and supervisor reference maps (`AxSpinAp.walkA*M/S`) combined
   by `WkEntryNew.execAnyCfg`; the `rfF` facts are `rff_auto` after pruning the decoder's
   pattern tests on the literal.
5. Section variables (`σi T satp0`) are explicit arguments.

**Rocq → Lean name map.**  `pca` `pca` (+ `base`), `WA0e` … `WA2e` same, `ap00` … `ap3c` same,
`ap0a_ins0e` `ap0aIns0e`, `ap26_ins0e` `ap26Ins0e`, `allocpid_text` `allocpidText`, `tokC`
`tokC`, `TokC` `TokC`, `rfF_decA0e`/`A16`/`A1a` `rfFDecA0e`/`rfFDecA16`/`rfFDecA1a`,
`decA0e`/`decA16`/`decA1a` same (none in the duplicated-name table).  Lean-only
(file-qualified): `AxSpinAp.walkA0eM/S`, `AxSpinAp.walkA16M/S`, `AxSpinAp.walkA1aM/S`.

**Dropped:** nothing (Rocq 34 definitions/lemmas; Lean 34 + 6 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pca` (deviation 1: the function base is a parameter). -/
def pca (base : Nat) (off : Int) : BitVec 64 := BitVec.ofInt 64 ((base : Int) + off)

/-- Rocq `WA0e`: `addi a0,a0,-1696` at + 0x0e. -/
def WA0e : BitVec 32 := 0x96050513#32
/-- Rocq `WA12`: `jal acquire` at + 0x12. -/
def WA12 : BitVec 32 := 0xa18ff0ef#32
/-- Rocq `WA16`: `auipc a5,0x9` at + 0x16. -/
def WA16 : BitVec 32 := 0x00009797#32
/-- Rocq `WA1a`: `addi a5,a5,-2048` at + 0x1a. -/
def WA1a : BitVec 32 := 0x80078793#32
/-- Rocq `WA20`: `addiw a4,s1,1` at + 0x20. -/
def WA20 : BitVec 32 := 0x0014871b#32
/-- Rocq `WA2a`: `addi a0,a0,-1724` at + 0x2a. -/
def WA2a : BitVec 32 := 0x94450513#32
/-- Rocq `WA2e`: `jal release` at + 0x2e. -/
def WA2e : BitVec 32 := 0xa84ff0ef#32

/-! # 2. The expanded instructions (Rocq `CodeAllocpid.apdi_XX`) -/

/-- Rocq `ap00`: `c.addi sp,-32`. -/
def ap00 : instruction := .ITYPE (sign_extend (m := 12) (32#6), .Regidx 2#5, .Regidx 2#5, .ADDI)
/-- Rocq `ap02`: `c.sdsp ra,24(sp)`. -/
def ap02 : instruction := .STORE (zero_extend (m := 12) (3#6 +++ 0b000#3), .Regidx 1#5, sp, 8)
/-- Rocq `ap04`: `c.sdsp s0,16(sp)`. -/
def ap04 : instruction := .STORE (zero_extend (m := 12) (2#6 +++ 0b000#3), .Regidx 8#5, sp, 8)
/-- Rocq `ap06`: `c.sdsp s1,8(sp)`. -/
def ap06 : instruction := .STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 9#5, sp, 8)
/-- Rocq `ap08`: `c.addi4spn s0,sp,32`. -/
def ap08 : instruction := .ITYPE (caddi4spnImm 8#8, sp, creg2reg_idx (.Cregidx 0#3), .ADDI)
/-- Rocq `ap0a`: `auipc a0,0x11`. -/
def ap0a : instruction := .UTYPE (17#20, .Regidx 10#5, .AUIPC)
/-- Rocq `ap0e`: `addi a0,a0,…`. -/
def ap0e : instruction := .ITYPE (2400#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
/-- Rocq `ap12`: `jal acquire`. -/
def ap12 : instruction := .JAL (2093592#21, .Regidx 1#5)
/-- Rocq `ap16`: `auipc a5,0x9`. -/
def ap16 : instruction := .UTYPE (9#20, .Regidx 15#5, .AUIPC)
/-- Rocq `ap1a`: `addi a5,a5,-2048`. -/
def ap1a : instruction := .ITYPE (2048#12, .Regidx 15#5, .Regidx 15#5, .ADDI)
/-- Rocq `ap1e`: `c.lw s1,0(a5)`. -/
def ap1e : instruction := .LOAD (0#12, .Regidx 15#5, .Regidx 9#5, false, 4)
/-- Rocq `ap20`: `addiw a4,s1,1`. -/
def ap20 : instruction := .ADDIW (1#12, .Regidx 9#5, .Regidx 14#5)
/-- Rocq `ap24`: `c.sw a4,0(a5)`. -/
def ap24 : instruction := .STORE (0#12, .Regidx 14#5, .Regidx 15#5, 4)
/-- Rocq `ap26`: `auipc a0,0x11`. -/
def ap26 : instruction := .UTYPE (17#20, .Regidx 10#5, .AUIPC)
/-- Rocq `ap2a`: `addi a0,a0,…`. -/
def ap2a : instruction := .ITYPE (2372#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
/-- Rocq `ap2e`: `jal release`. -/
def ap2e : instruction := .JAL (2093700#21, .Regidx 1#5)
/-- Rocq `ap32`: `c.mv a0,s1`. -/
def ap32 : instruction := .RTYPE (.Regidx 9#5, zreg, .Regidx 10#5, .ADD)
/-- Rocq `ap34`: `c.ldsp ra,24(sp)`. -/
def ap34 : instruction := .LOAD (zero_extend (m := 12) (3#6 +++ 0b000#3), sp, .Regidx 1#5, false, 8)
/-- Rocq `ap36`: `c.ldsp s0,16(sp)`. -/
def ap36 : instruction := .LOAD (zero_extend (m := 12) (2#6 +++ 0b000#3), sp, .Regidx 8#5, false, 8)
/-- Rocq `ap38`: `c.ldsp s1,8(sp)`. -/
def ap38 : instruction := .LOAD (zero_extend (m := 12) (1#6 +++ 0b000#3), sp, .Regidx 9#5, false, 8)
/-- Rocq `ap3a`: `c.addi16sp sp,32`. -/
def ap3a : instruction := .ITYPE (caddi16spImm 2#6, sp, sp, .ADDI)
/-- Rocq `ap3c`: `c.ret`. -/
def ap3c : instruction := .JALR (zeros (n := 12), .Regidx 1#5, zreg)

/-- Rocq `ap0a_ins0e`. -/
theorem ap0aIns0e : ap0a = ins0e := rfl
/-- Rocq `ap26_ins0e`. -/
theorem ap26Ins0e : ap26 = ins0e := rfl

section afacts
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-! # 1. The text -/

/-- Rocq `allocpid_text` (deviation 1: at the base `base`). -/
def allocpidText (base : Nat) : Prop :=
  textAtS σi T (pca base 0x00) (AxSpinE7.hw 0x1101) ∧ textAtS σi T (pca base 0x02) (AxSpinE7.hw 0xec06) ∧
  textAtS σi T (pca base 0x04) (AxSpinE7.hw 0xe822) ∧ textAtS σi T (pca base 0x06) (AxSpinE7.hw 0xe426) ∧
  textAtS σi T (pca base 0x08) (AxSpinE7.hw 0x1000) ∧
  textAt4S σi T (pca base 0x0a) W0e ∧
  textAt4S σi T (pca base 0x0e) WA0e ∧
  textAt4S σi T (pca base 0x12) WA12 ∧
  textAt4S σi T (pca base 0x16) WA16 ∧
  textAt4S σi T (pca base 0x1a) WA1a ∧
  textAtS σi T (pca base 0x1e) (AxSpinE7.hw 0x4384) ∧
  textAt4S σi T (pca base 0x20) WA20 ∧
  textAtS σi T (pca base 0x24) (AxSpinE7.hw 0xc398) ∧
  textAt4S σi T (pca base 0x26) W0e ∧
  textAt4S σi T (pca base 0x2a) WA2a ∧
  textAt4S σi T (pca base 0x2e) WA2e ∧
  textAtS σi T (pca base 0x32) (AxSpinE7.hw 0x8526) ∧ textAtS σi T (pca base 0x34) (AxSpinE7.hw 0x60e2) ∧
  textAtS σi T (pca base 0x36) (AxSpinE7.hw 0x6442) ∧ textAtS σi T (pca base 0x38) (AxSpinE7.hw 0x64a2) ∧
  textAtS σi T (pca base 0x3a) (AxSpinE7.hw 0x6105) ∧ textAtS σi T (pca base 0x3c) (AxSpinE7.hw 0x8082)

/-! # 3. The pc-independent half of a compressed `textOkB` -/

/-- Rocq `tokC` (deviation 3: the decode premise at the `misa = misaC` states). -/
theorem tokC (pc : BitVec 64) (h : BitVec 16) (ins : instruction) :
    textAtS σi T pc h →
    (∃ i0, rfF (ext_decode_compressed h) ∧
      (∀ s : ExecSt, s.regs .misa = misaC → exec (ext_decode_compressed h) s = some (i0, s)) ∧
      rfF (execute i0) ∧ (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s))) →
    textOkB σi T satp0 pc true ins := by
  intro Hat ⟨i0, H1, H2, H3, H4⟩
  exact tokR σi T satp0 pc h i0 ins Hat H1 H2 H3 H4

end afacts

/-- Rocq `TokC` (deviation 3). -/
def TokC (h : BitVec 16) (ins : instruction) : Prop :=
  ∃ i0, rfF (ext_decode_compressed h) ∧
    (∀ s : ExecSt, s.regs .misa = misaC → exec (ext_decode_compressed h) s = some (i0, s)) ∧
    rfF (execute i0) ∧ (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs ins, s))

/-! # 3'. Three of the 4-byte decodes -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA0e`. -/
theorem rfFDecA0e : rfF (ext_decode WA0e) := by
  unfold WA0e ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA16`. -/
theorem rfFDecA16 : rfF (ext_decode WA16) := by
  unfold WA16 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA1a`. -/
theorem rfFDecA1a : rfF (ext_decode WA1a) := by
  unfold WA1a ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 4) the decode walk of `WA0e` on the machine reference map. -/
theorem AxSpinAp.walkA0eM : runRead drefM (ext_decode WA0e) = some (ap0e, true) := by kernel_rfl
/-- (Lean-only, deviation 4) the decode walk of `WA0e` on the supervisor reference map. -/
theorem AxSpinAp.walkA0eS : runRead WkEntryNew.drefS0 (ext_decode WA0e) = some (ap0e, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) the decode walk of `WA16` on the machine reference map. -/
theorem AxSpinAp.walkA16M : runRead drefM (ext_decode WA16) = some (ap16, true) := by kernel_rfl
/-- (Lean-only, deviation 4) the decode walk of `WA16` on the supervisor reference map. -/
theorem AxSpinAp.walkA16S : runRead WkEntryNew.drefS0 (ext_decode WA16) = some (ap16, true) := by
  kernel_rfl
/-- (Lean-only, deviation 4) the decode walk of `WA1a` on the machine reference map. -/
theorem AxSpinAp.walkA1aM : runRead drefM (ext_decode WA1a) = some (ap1a, true) := by kernel_rfl
/-- (Lean-only, deviation 4) the decode walk of `WA1a` on the supervisor reference map. -/
theorem AxSpinAp.walkA1aS : runRead WkEntryNew.drefS0 (ext_decode WA1a) = some (ap1a, true) := by
  kernel_rfl

end walks

/-- Rocq `decA0e` (deviation 4). -/
theorem decA0e (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA0e) s = some (ap0e, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA0eM AxSpinAp.walkA0eS s

/-- Rocq `decA16` (deviation 4). -/
theorem decA16 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA16) s = some (ap16, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA16M AxSpinAp.walkA16S s

/-- Rocq `decA1a` (deviation 4). -/
theorem decA1a (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA1a) s = some (ap1a, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp.walkA1aM AxSpinAp.walkA1aS s

end Weak
