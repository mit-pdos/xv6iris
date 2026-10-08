/-
Weak: **PHASE 5, stage 5 prerequisites for xv6's REAL `acquire`** (the 26 instructions of
`CodeAcquire` at `KernelSyms.acquire`, 64 bytes; the panic call at + 0x34 … + 0x3c is never
executed on an accepted row): the INSTRUCTION DEFINITIONS and the TEXT premise for the positional
engine (`AxSpinE`).

Rocq: `iris/AxSpinAq.v` @ xxvzwolszwmp.

## The Rocq header, in substance

```
  + 0x00 c.addi sp,-32      + 0x16 c.li a4,1          + 0x24 jal mycpu
  + 0x02 c.sdsp ra,24(sp)   + 0x18 c.bnez a0,panic    + 0x28 c.sd a0,16(s1)
  + 0x04 c.sdsp s0,16(sp)   + 0x1a c.mv a5,a4  <-+    + 0x2a c.ldsp ra,24(sp)
  + 0x06 c.sdsp s1,8(sp)    + 0x1c amoswap.w.aq   |    + 0x2c c.ldsp s0,16(sp)
  + 0x08 c.addi4spn s0,32          a5,a5,(s1)    |    + 0x2e c.ldsp s1,8(sp)
  + 0x0a c.mv s1,a0         + 0x20 sext.w a5      |    + 0x30 c.addi16sp 32
  + 0x0c jal push_off       + 0x22 c.bnez a5 -----+    + 0x32 c.ret
  + 0x10 c.mv a0,s1
  + 0x12 jal holding
```

§1 the 4-byte words (constants: an inline literal makes `rff_auto` crawl the decoder) and the
   expanded ASTs; the prologue / epilogue ASTs are push_off's / mycpu's (`q00 …`,
   `AxSpinE7.ins0a`, `AxSpinE7.ins1e`) — same words, same ASTs.
§2 `acquireText σi T`: the words are text at their pcs (`textAtS` / `textAt4S`) — IMAGE +
   page-table facts, to be discharged concretely by a certificate.  The amoswap word is included;
   its decoding is the amoswap leaf's business.
§3 the values the spin loop computes: `aqOne` (c.li a4,1), `sxw0` (sext.w), `aqFail vs` — THE
   BRANCH TEST of + 0x22 on the amoswap's read bytes `vs` (true = the loop goes round again).
The per-word `textOkB` facts are generic in the pc (AxSpinAqt1/2, AxSpinAqd).

## Deviations from Rocq

1. KERNEL DRIFT: this tree's kernel has `acquire` at 0x80000c58 and `mycpu` at 0x8000195c, so the
   `jal mycpu` word at + 0x24 is `Wa24 = 0x4e1000ef#32` (Rocq 0x4bb000ef) and `a24`'s JAL
   immediate is 3296 (Rocq 3258).  Every other word and every offset matches Rocq (checked
   against `Xv6/KernelImage.lean`: Lean-only `AxSpinAq.aqCode`/`aqCodeImg`/`aqCodeContig`, and
   the decodes of the three jal words by the kernel walks `AxSpinAq.walk*M`).  The panic call
   (+ 0x34 auipc, + 0x38 addi, + 0x3c jal panic) is also where Rocq has it.
2. TYPES / SPELLING (as `AxSpinPO` deviation 2): `mword n` ↦ `BitVec n`, `mword_of_int k` ↦
   `k#n`, `mstate` ↦ `ExecSt`, `ptree` ↦ `PTree`, `text_at_S`/`text_at4_S` ↦
   `textAtS`/`textAt4S`, `sign_extend' n` ↦ `sign_extend (m := n)`, `concat_vec` ↦ `+++`,
   `add_vec zero_reg x` ↦ `0#64 + x`, `add_vec` ↦ `+`, `subrange_vec_dec x 31 0` ↦
   `Sail.BitVec.extractLsb x 31 0` (the model's `execute_ADDIW`), `neq_vec x zero_reg` ↦
   `x != 0#64`, `amo_ldv` ↦ `amoLdv` (AxLeafS), `pac` ↦ `AxSpinHdB.pac`, `hw` ↦ `AxSpinE7.hw`.
   The `W*` words are `BitVec 32` constants (Rocq `Z`, used only as `mword_of_int W : mword 32`).
3. Section variables `σi T` are explicit arguments.  The two `pac` disequalities are by
   `decide +kernel` (Rocq `vm_compute` on `uint`).
4. Stage C / Q20' play no role here (no row positions, no control-flow argument).

**Rocq → Lean name map.**  `Wa0c`/`Wa12`/`Wa1c`/`Wa24` same; `a0a` `a0c` `a10` `a12` `a16`
`a18` `a1a` `a22` `a24` `a28` same; `acquire_text` `acquireText`; `aq_one` `aqOne`; `sxw0`
`sxw0`; `aq_fail` `aqFail`; `pac_1a_24` `pac1a24`; `pac_1a_34` `pac1a34`.  (No name is in the
duplicated-name table; all short names grepped absent from the tip.)
Lean-only (file-qualified): `AxSpinAq.aqCode`, `AxSpinAq.aqCodeImg`, `AxSpinAq.aqCodeContig`,
`AxSpinAq.walk0cM`, `AxSpinAq.walk12M`, `AxSpinAq.walk24M`.

**Dropped:** nothing (Rocq 20 definitions/lemmas; Lean 20 + 6 Lean-only checks).
-/
import Weak.AxSpinE7
import Weak.AxSpinPO
import Weak.AxSpinHdB
import Weak.AxLeafS
import Xv6.KernelTree

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. words, instructions -/

/-- `jal push_off`. -/
def Wa0c : BitVec 32 := 0xfbbff0ef#32
/-- `jal holding`. -/
def Wa12 : BitVec 32 := 0xf89ff0ef#32
/-- `amoswap.w.aq a5,a5,(s1)`. -/
def Wa1c : BitVec 32 := 0x0cf4a7af#32
/-- `jal mycpu` (deviation 1). -/
def Wa24 : BitVec 32 := 0x4e1000ef#32

/-- `c.mv s1,a0`. -/
def a0a : instruction := .RTYPE (.Regidx 10#5, zreg, .Regidx 9#5, .ADD)
/-- `jal push_off`. -/
def a0c : instruction := .JAL (2097082#21, .Regidx 1#5)
/-- `c.mv a0,s1`. -/
def a10 : instruction := .RTYPE (.Regidx 9#5, zreg, .Regidx 10#5, .ADD)
/-- `jal holding`. -/
def a12 : instruction := .JAL (2097032#21, .Regidx 1#5)
/-- `c.li a4,1`. -/
def a16 : instruction := .ITYPE (sign_extend (m := 12) (1#6), zreg, .Regidx 14#5, .ADDI)
/-- `c.bnez a0,panic`. -/
def a18 : instruction :=
  .BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 2#3), .BNE)
/-- `c.mv a5,a4`. -/
def a1a : instruction := .RTYPE (.Regidx 14#5, zreg, .Regidx 15#5, .ADD)
/-- `c.bnez a5,+0x1a` (the spin back-edge). -/
def a22 : instruction :=
  .BTYPE (sign_extend (m := 13) (252#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BNE)
/-- `jal mycpu` (deviation 1: immediate 3296). -/
def a24 : instruction := .JAL (3296#21, .Regidx 1#5)
/-- `c.sd a0,16(s1)`. -/
def a28 : instruction := .STORE (16#12, .Regidx 10#5, .Regidx 9#5, 8)

/-! Lean-only checks (deviation 1): the three jal words decode to the instructions above. -/

theorem AxSpinAq.walk0cM : runRead drefM (ext_decode Wa0c) = some (a0c, true) := by kernel_rfl
theorem AxSpinAq.walk12M : runRead drefM (ext_decode Wa12) = some (a12, true) := by kernel_rfl
theorem AxSpinAq.walk24M : runRead drefM (ext_decode Wa24) = some (a24, true) := by kernel_rfl

/-- (Lean-only, deviation 1) acquire's 22 non-panic instructions as (offset from `acquire`,
width, encoding), over the constants `acquireText` states. -/
def AxSpinAq.aqCode : List (Nat × Nat × Nat) :=
  [(0x00, 2, (AxSpinE7.hw 0x1101).toNat), (0x02, 2, (AxSpinE7.hw 0xec06).toNat),
   (0x04, 2, (AxSpinE7.hw 0xe822).toNat), (0x06, 2, (AxSpinE7.hw 0xe426).toNat),
   (0x08, 2, (AxSpinE7.hw 0x1000).toNat), (0x0a, 2, (AxSpinE7.hw 0x84aa).toNat),
   (0x0c, 4, Wa0c.toNat), (0x10, 2, (AxSpinE7.hw 0x8526).toNat), (0x12, 4, Wa12.toNat),
   (0x16, 2, (AxSpinE7.hw 0x4705).toNat), (0x18, 2, (AxSpinE7.hw 0xed11).toNat),
   (0x1a, 2, (AxSpinE7.hw 0x87ba).toNat), (0x1c, 4, Wa1c.toNat),
   (0x20, 2, (AxSpinE7.hw 0x2781).toNat), (0x22, 2, (AxSpinE7.hw 0xffe5).toNat),
   (0x24, 4, Wa24.toNat), (0x28, 2, (AxSpinE7.hw 0xe888).toNat),
   (0x2a, 2, (AxSpinE7.hw 0x60e2).toNat), (0x2c, 2, (AxSpinE7.hw 0x6442).toNat),
   (0x2e, 2, (AxSpinE7.hw 0x64a2).toNat), (0x30, 2, (AxSpinE7.hw 0x6105).toNat),
   (0x32, 2, (AxSpinE7.hw 0x8082).toNat)]

/-- (Lean-only, deviation 1) THE IMAGE CHECK: every entry of `AxSpinAq.aqCode` is the
instruction of this tree's kernel text (`Xv6/KernelImage.lean`) at `acquire + off`, with that
width and encoding. -/
theorem AxSpinAq.aqCodeImg :
    AxSpinAq.aqCode.all (fun c =>
      match Xv6.Kernel.textTree.find? (KernelSyms.«acquire» + c.1) with
      | some k => Nat.beq k.width c.2.1 && Nat.beq k.enc c.2.2
      | none => false) = true := by
  decide +kernel

/-- (Lean-only, deviation 1) the 22 instructions are contiguous from `acquire + 0x00` to
`+ 0x34` (where the panic call begins). -/
theorem AxSpinAq.aqCodeContig :
    AxSpinAq.aqCode.length = 22 ∧ AxSpinAq.aqCode.head?.map (·.1) = some 0x00 ∧
    ((AxSpinAq.aqCode.zip AxSpinAq.aqCode.tail).all fun p => Nat.beq (p.1.1 + p.1.2.1) p.2.1) = true ∧
    AxSpinAq.aqCode.getLast?.map (fun c => c.1 + c.2.1) = some 0x34 := by
  decide +kernel

/-! # 2. The text -/

section text
variable (σi : ExecSt) (T : PTree)

/-- Rocq `acquire_text`. -/
def acquireText : Prop :=
  textAtS σi T (AxSpinHdB.pac 0x00) (AxSpinE7.hw 0x1101) ∧
  textAtS σi T (AxSpinHdB.pac 0x02) (AxSpinE7.hw 0xec06) ∧
  textAtS σi T (AxSpinHdB.pac 0x04) (AxSpinE7.hw 0xe822) ∧
  textAtS σi T (AxSpinHdB.pac 0x06) (AxSpinE7.hw 0xe426) ∧
  textAtS σi T (AxSpinHdB.pac 0x08) (AxSpinE7.hw 0x1000) ∧
  textAtS σi T (AxSpinHdB.pac 0x0a) (AxSpinE7.hw 0x84aa) ∧
  textAt4S σi T (AxSpinHdB.pac 0x0c) Wa0c ∧
  textAtS σi T (AxSpinHdB.pac 0x10) (AxSpinE7.hw 0x8526) ∧
  textAt4S σi T (AxSpinHdB.pac 0x12) Wa12 ∧
  textAtS σi T (AxSpinHdB.pac 0x16) (AxSpinE7.hw 0x4705) ∧
  textAtS σi T (AxSpinHdB.pac 0x18) (AxSpinE7.hw 0xed11) ∧
  textAtS σi T (AxSpinHdB.pac 0x1a) (AxSpinE7.hw 0x87ba) ∧
  textAt4S σi T (AxSpinHdB.pac 0x1c) Wa1c ∧
  textAtS σi T (AxSpinHdB.pac 0x20) (AxSpinE7.hw 0x2781) ∧
  textAtS σi T (AxSpinHdB.pac 0x22) (AxSpinE7.hw 0xffe5) ∧
  textAt4S σi T (AxSpinHdB.pac 0x24) Wa24 ∧
  textAtS σi T (AxSpinHdB.pac 0x28) (AxSpinE7.hw 0xe888) ∧
  textAtS σi T (AxSpinHdB.pac 0x2a) (AxSpinE7.hw 0x60e2) ∧
  textAtS σi T (AxSpinHdB.pac 0x2c) (AxSpinE7.hw 0x6442) ∧
  textAtS σi T (AxSpinHdB.pac 0x2e) (AxSpinE7.hw 0x64a2) ∧
  textAtS σi T (AxSpinHdB.pac 0x30) (AxSpinE7.hw 0x6105) ∧
  textAtS σi T (AxSpinHdB.pac 0x32) (AxSpinE7.hw 0x8082)

end text

/-! # 3. The spin loop's values -/

/-- Rocq `aq_one`: a4 after `c.li a4,1` (x0 reads as zero). -/
def aqOne : BitVec 64 := 0#64 + sign_extend (m := 64) (sign_extend (m := 12) (1#6))

/-- Rocq `sxw0`: `sext.w a5,a5` = `addiw a5,a5,0`. -/
def sxw0 (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (sign_extend (m := 12) (0#6))) 31 0)

/-- Rocq `aq_fail`: THE BRANCH TEST of + 0x22 (`c.bnez a5`) on the amoswap's read bytes:
`true` = the lock was taken, go round again. -/
def aqFail (vs : List (BitVec 8)) : Bool := sxw0 (amoLdv 4 vs) != 0#64

theorem pac1a24 : AxSpinHdB.pac 0x1a ≠ AxSpinHdB.pac 0x24 := by decide +kernel
theorem pac1a34 : AxSpinHdB.pac 0x1a ≠ AxSpinHdB.pac 0x34 := by decide +kernel

end Weak
