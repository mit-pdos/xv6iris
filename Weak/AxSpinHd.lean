/-
Weak: **PHASE 5, stage 3 prerequisites: the INSTRUCTION FACTS of xv6's REAL `holding`** (21
instructions, 44 bytes at `KernelSyms.holding`) for the positional engine — the template is
`AxSpinE7` (mycpu).

Rocq: `iris/AxSpinHd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `holdingText σi T`: the 21 words are text at their pcs (`textAtS` for the 18 compressed ones,
   `textAt4S` for the three 4-byte ones at + 0x16 (jal mycpu), + 0x1a (sub), + 0x1e
   (seqz = sltiu)) — a fact about the IMAGE and the page table, like `AxSpinE7.mycpuText`.
§2 the expanded instructions `hxx` (Rocq `CodeHolding.hi_xx`'s ASTs) and the three 4-byte decode
   facts with their read-free footprints.  The `textOkB` facts `htok_xx` are in
   AxSpinHd2/Hd2b/Hd2c/Hd3/Hd4/Hd5 (built with `tokR` / `tokB` of AxSpinE7); the execute
   footprints `rfF_hxx` in AxSpinHd6/Hd6b/Hd6c.
§3 the new `CertC` (SC exec) facts with SYMBOLIC register values: `certSub`, `certSltiu`.
   (c.bnez = `AxSymCtl2.certBTYPE`, jal = `AxSymCtl2.certJAL`, c.ret = `AxSymCtl2.certJALR`,
   c.li / c.addi / c.addi4spn / c.addi16sp = `certAddi`, c.mv = `certAdd`, both AxSpinE7.)

## Deviations from Rocq

1. KERNEL DRIFT: this tree's kernel has `holding` at 0x80000bf2 (`KernelSyms.«holding»`), and
   `mycpu` lies 0xd6a past it (Xv6/ProofHolding `holding_br_d6a`), so the `jal ra, mycpu` at
   holding + 0x16 is `0x555000ef` (Rocq `0x52f000ef`): `W16 = 0x555000ef#32` and `h16`'s
   immediate is `3412#21` (= 0xd54; Rocq `3374`).  The other 20 words match Rocq (checked
   against `Xv6/KernelImage.lean`'s text listing, 0x80000bf2 … 0x80000c1c).
2. TYPES / SPELLING (as `AxSpinE7` deviation 2): `mword n` ↦ `BitVec n`, `mword_of_int k :
   mword n` ↦ `k#n`, `mstate` ↦ `ExecSt`, `ptree` ↦ `PTree`, `text_at_S`/`text_at4_S` ↦
   `textAtS`/`textAt4S`, `sign_extend' n` ↦ `sign_extend (m := n)`, `zero_extend' 12` ↦
   `zero_extend (m := 12)`, `concat_vec u 'b"0…"` ↦ `u +++ 0b0…#k`, `zeros' 12` ↦
   `zeros (n := 12)`, `caddi4spn_imm`/`caddi16sp_imm` ↦ `caddi4spnImm`/`caddi16spImm`,
   `sub_vec` ↦ `-`, `gpr_val` ↦ `gprVal`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `cfg_ok` ↦ `cfgOk`,
   `MISA_C` ↦ `misaC`, `register_lookup misa s.(sregs)` ↦ `s.regs .misa`.  `W16`/`W1a`/`W1e`
   are `BitVec 32` constants (Rocq `Z`, used only as `mword_of_int W : mword 32`).  `pch off`
   is `BitVec.ofInt 64 (holding + off)` (`off : Int`); Rocq `hw` is `AxSpinE7.hw`.
3. DECODE PROOFS (as `AxSpinE7` deviation 5): Rocq's `kd_52f000ef`/`kd_40a48533`/`kd_00153513`
   (KernelDecode05/25/28) are not ported; `dec16`/`dec1a`/`dec1e` are the kernel walks of the
   decoder on the machine and supervisor reference maps (`AxSpinHd.walk16M/S`, `walk1aM/S`,
   `walk1eM/S`, `kernel_rfl`) combined by `WkEntryNew.execAnyCfg`.  `rfFDec16`/`rfFDec1a`/
   `rfFDec1e` are `rff_auto` after pruning the decoder's pattern tests on the literal (the
   `AxSymCtl3.rfFDecodePH` recipe).
4. Section variables (`σi T satp0`, `ctrlOk`) are explicit arguments (`satp0` is unused by
   `holdingText`, as in Rocq, and is not a binder of it).

**Rocq → Lean name map.**  `pch` `pch`, `W16` `W16`, `W1a` `W1a`, `W1e` `W1e`, `h00` … `h2a`
same, `holding_text` `holdingText`, `rfF_dec16` `rfFDec16`, `rfF_dec1a` `rfFDec1a`,
`rfF_dec1e` `rfFDec1e`, `dec16` `dec16`, `dec1a` `dec1a`, `dec1e` `dec1e`, `cert_sub`
`certSub`, `cert_sltiu` `certSltiu` (none in the duplicated-name table; none defined elsewhere
in the tree).  Lean-only (file-qualified): `AxSpinHd.walk16M`, `AxSpinHd.walk16S`,
`AxSpinHd.walk1aM`, `AxSpinHd.walk1aS`, `AxSpinHd.walk1eM`, `AxSpinHd.walk1eS`.

**Dropped:** nothing (Rocq 32 definitions/lemmas; Lean 32 + 6 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pch`: the address `holding + off`. -/
def pch (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«holding» : Int) + off)
/-- Rocq `W16`: the 4-byte word at holding + 0x16 (`jal ra, mycpu`; deviation 1). -/
def W16 : BitVec 32 := 0x555000ef#32
/-- Rocq `W1a`: the 4-byte word at holding + 0x1a (`sub a0, s1, a0`). -/
def W1a : BitVec 32 := 0x40a48533#32
/-- Rocq `W1e`: the 4-byte word at holding + 0x1e (`seqz a0, a0` = `sltiu a0, a0, 1`). -/
def W1e : BitVec 32 := 0x00153513#32

/-! # 2. The expanded instructions (Rocq `CodeHolding.hi_xx`) -/

/-- Rocq `h00`: `c.lw a5, 0(a0)`. -/
def h00 : instruction := .LOAD (0#12, .Regidx 10#5, .Regidx 15#5, false, 4)
/-- Rocq `h02`: `c.bnez a5, +6`. -/
def h02 : instruction :=
  .BTYPE (sign_extend (m := 13) (3#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BNE)
/-- Rocq `h04`: `c.li a0, 0`. -/
def h04 : instruction := .ITYPE (sign_extend (m := 12) (0#6), zreg, .Regidx 10#5, .ADDI)
/-- Rocq `h06`: `c.ret`. -/
def h06 : instruction := .JALR (zeros (n := 12), .Regidx 1#5, zreg)
/-- Rocq `h08`: `c.addi sp, -32`. -/
def h08 : instruction := .ITYPE (sign_extend (m := 12) (32#6), .Regidx 2#5, .Regidx 2#5, .ADDI)
/-- Rocq `h0a`: `c.sdsp ra, 24(sp)`. -/
def h0a : instruction := .STORE (zero_extend (m := 12) (3#6 +++ 0b000#3), .Regidx 1#5, sp, 8)
/-- Rocq `h0c`: `c.sdsp s0, 16(sp)`. -/
def h0c : instruction := .STORE (zero_extend (m := 12) (2#6 +++ 0b000#3), .Regidx 8#5, sp, 8)
/-- Rocq `h0e`: `c.sdsp s1, 8(sp)`. -/
def h0e : instruction := .STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 9#5, sp, 8)
/-- Rocq `h10`: `c.addi4spn s0, sp, 32`. -/
def h10 : instruction := .ITYPE (caddi4spnImm 8#8, sp, creg2reg_idx (.Cregidx 0#3), .ADDI)
/-- Rocq `h12`: `c.ld a5, 16(a0)`. -/
def h12 : instruction := .LOAD (16#12, .Regidx 10#5, .Regidx 15#5, false, 8)
/-- Rocq `h14`: `c.mv s1, a5`. -/
def h14 : instruction := .RTYPE (.Regidx 15#5, zreg, .Regidx 9#5, .ADD)
/-- Rocq `h16`: `jal ra, mycpu` (deviation 1: immediate `3412`). -/
def h16 : instruction := .JAL (3412#21, .Regidx 1#5)
/-- Rocq `h1a`: `sub a0, s1, a0`. -/
def h1a : instruction := .RTYPE (.Regidx 10#5, .Regidx 9#5, .Regidx 10#5, .SUB)
/-- Rocq `h1e`: `seqz a0, a0`. -/
def h1e : instruction := .ITYPE (1#12, .Regidx 10#5, .Regidx 10#5, .SLTIU)
/-- Rocq `h22`: `c.ldsp ra, 24(sp)`. -/
def h22 : instruction := .LOAD (zero_extend (m := 12) (3#6 +++ 0b000#3), sp, .Regidx 1#5, false, 8)
/-- Rocq `h24`: `c.ldsp s0, 16(sp)`. -/
def h24 : instruction := .LOAD (zero_extend (m := 12) (2#6 +++ 0b000#3), sp, .Regidx 8#5, false, 8)
/-- Rocq `h26`: `c.ldsp s1, 8(sp)`. -/
def h26 : instruction := .LOAD (zero_extend (m := 12) (1#6 +++ 0b000#3), sp, .Regidx 9#5, false, 8)
/-- Rocq `h28`: `c.addi16sp sp, 32`. -/
def h28 : instruction := .ITYPE (caddi16spImm 2#6, sp, sp, .ADDI)
/-- Rocq `h2a`: `c.ret`. -/
def h2a : instruction := .JALR (zeros (n := 12), .Regidx 1#5, zreg)

/-! # 1. The text -/

/-- Rocq `holding_text`. -/
def holdingText (σi : ExecSt) (T : PTree) : Prop :=
  textAtS σi T (pch 0x00) (AxSpinE7.hw 0x411c) ∧ textAtS σi T (pch 0x02) (AxSpinE7.hw 0xe399) ∧
  textAtS σi T (pch 0x04) (AxSpinE7.hw 0x4501) ∧ textAtS σi T (pch 0x06) (AxSpinE7.hw 0x8082) ∧
  textAtS σi T (pch 0x08) (AxSpinE7.hw 0x1101) ∧ textAtS σi T (pch 0x0a) (AxSpinE7.hw 0xec06) ∧
  textAtS σi T (pch 0x0c) (AxSpinE7.hw 0xe822) ∧ textAtS σi T (pch 0x0e) (AxSpinE7.hw 0xe426) ∧
  textAtS σi T (pch 0x10) (AxSpinE7.hw 0x1000) ∧ textAtS σi T (pch 0x12) (AxSpinE7.hw 0x691c) ∧
  textAtS σi T (pch 0x14) (AxSpinE7.hw 0x84be) ∧
  textAt4S σi T (pch 0x16) W16 ∧
  textAt4S σi T (pch 0x1a) W1a ∧
  textAt4S σi T (pch 0x1e) W1e ∧
  textAtS σi T (pch 0x22) (AxSpinE7.hw 0x60e2) ∧ textAtS σi T (pch 0x24) (AxSpinE7.hw 0x6442) ∧
  textAtS σi T (pch 0x26) (AxSpinE7.hw 0x64a2) ∧ textAtS σi T (pch 0x28) (AxSpinE7.hw 0x6105) ∧
  textAtS σi T (pch 0x2a) (AxSpinE7.hw 0x8082)

/-! # 2'. The three 4-byte decodes -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec16`. -/
theorem rfFDec16 : rfF (ext_decode W16) := by
  unfold W16 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec1a`. -/
theorem rfFDec1a : rfF (ext_decode W1a) := by
  unfold W1a ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec1e`. -/
theorem rfFDec1e : rfF (ext_decode W1e) := by
  unfold W1e ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 3) the decode walk of `W16` on the machine reference map. -/
theorem AxSpinHd.walk16M : runRead drefM (ext_decode W16) = some (h16, true) := by kernel_rfl
/-- (Lean-only, deviation 3) the decode walk of `W16` on the supervisor reference map. -/
theorem AxSpinHd.walk16S : runRead WkEntryNew.drefS0 (ext_decode W16) = some (h16, true) := by
  kernel_rfl
/-- (Lean-only, deviation 3) the decode walk of `W1a` on the machine reference map. -/
theorem AxSpinHd.walk1aM : runRead drefM (ext_decode W1a) = some (h1a, true) := by kernel_rfl
/-- (Lean-only, deviation 3) the decode walk of `W1a` on the supervisor reference map. -/
theorem AxSpinHd.walk1aS : runRead WkEntryNew.drefS0 (ext_decode W1a) = some (h1a, true) := by
  kernel_rfl
/-- (Lean-only, deviation 3) the decode walk of `W1e` on the machine reference map. -/
theorem AxSpinHd.walk1eM : runRead drefM (ext_decode W1e) = some (h1e, true) := by kernel_rfl
/-- (Lean-only, deviation 3) the decode walk of `W1e` on the supervisor reference map. -/
theorem AxSpinHd.walk1eS : runRead WkEntryNew.drefS0 (ext_decode W1e) = some (h1e, true) := by
  kernel_rfl

end walks

/-- Rocq `dec16` (deviation 3). -/
theorem dec16 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode W16) s = some (h16, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinHd.walk16M AxSpinHd.walk16S s

/-- Rocq `dec1a` (deviation 3). -/
theorem dec1a (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode W1a) s = some (h1a, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinHd.walk1aM AxSpinHd.walk1aS s

/-- Rocq `dec1e` (deviation 3). -/
theorem dec1e (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode W1e) s = some (h1e, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinHd.walk1eM AxSpinHd.walk1eS s

/-! # 3. The new SC exec (`CertC`) facts, symbolic register values -/

section certs
variable (ctrlOk : RegFile → Prop)

/-- Rocq `cert_sub`. -/
theorem certSub (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs2 rs1 rd : BitVec 5) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)) none
      (some (rd, gprVal rs rs1 - gprVal rs rs2)) := by
  intro _ s_pc _ _ _ Hag
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .SUB) s_pc = _
  rw [execExecuteRTYPESUBGpr]
  unfold gprSubVal
  have h1 : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  have h2 : s_pc.gpr rs2 = gprVal rs rs2 := gprValAgree _ _ rs2 Hag
  rw [h1, h2]
  rfl

/-- Rocq `cert_sltiu`. -/
theorem certSltiu (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (imm : BitVec 12) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU)) none
      (some (rd, zero_extend (m := 64)
        (bool_to_bit (zopz0zI_u (gprVal rs rs1) (sign_extend (m := 64) imm))))) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteITYPESLTIUGpr]
  unfold gprSltiuVal
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

end certs

end Weak
