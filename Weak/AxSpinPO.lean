/-
Weak: **PHASE 5, stage 5 prerequisites: the INSTRUCTION DEFINITIONS of xv6's REAL `push_off`**
(23 instructions, 58 bytes at `KernelSyms.push_off`) **and `pop_off`** (the 19 instructions of its
non-panic paths, at `KernelSyms.pop_off`) for the positional engine (`AxSpinE`).

Rocq: `iris/AxSpinPO.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 pcs, the 4-byte words (kept as constants: an inline literal makes `rff_auto` crawl the
   decoder), the expanded instruction ASTs (`q00` … `q38` for push_off, `p08` … `p22` for
   pop_off; pop_off's 00/02/04/06 and 28/2a/2c/2e are mycpu's `AxSpinE7.ins00 …`, same words;
   pop_off + 0x14 is `qlw`, + 0x1c is `qsw`);
§2 `pushOffText σi T` / `popOffText σi T`: the words are text at their pcs (`textAtS` /
   `textAt4S`) — IMAGE + page-table facts, to be discharged concretely by a certificate.
The per-word `textOkB` facts are generic in the pc (the AxSpinPOt files), the decode footprints
of the 4-byte words in AxSpinPOd.

## Deviations from Rocq

1. KERNEL DRIFT: this tree's kernel has `push_off` at 0x80000c1e, `pop_off` at 0x80000c98 and
   `mycpu` at 0x8000195c (Rocq 0x80000bce / 0x80000c48 / 0x800018e6), so the four `jal mycpu`
   words differ: `Wq10 = 0x52f000ef#32` (Rocq 0x509000ef), `Wq18 = 0x527000ef#32` (0x501000ef),
   `Wq2c = 0x513000ef#32` (0x4ed000ef), `Wp08 = 0x4bd000ef#32` (0x497000ef), and the JAL
   immediates are `q10` 3374 (Rocq 3336), `q18` 3366 (3328), `q2c` 3346 (3308), `p08` 3260
   (3222).  Every other word and every offset matches Rocq (checked against
   `Xv6/KernelImage.lean`; the decodes of all eight 4-byte words are checked by the Lean-only
   kernel walks `AxSpinPO.walk*`).
2. TYPES / SPELLING (as `AxSpinE7` deviation 2): `mword n` ↦ `BitVec n`, `mword_of_int k` ↦
   `k#n`, `mstate` ↦ `ExecSt`, `ptree` ↦ `PTree`, `text_at_S`/`text_at4_S` ↦
   `textAtS`/`textAt4S`, `sign_extend' n` ↦ `sign_extend (m := n)`, `concat_vec` ↦ `+++`,
   `zero_extend' 12` ↦ `zero_extend (m := 12)`, `caddi4spn_imm`/`caddi16sp_imm` ↦
   `caddi4spnImm`/`caddi16spImm`, `hw` ↦ `AxSpinE7.hw`.  The `W*` words are `BitVec 32`
   constants (Rocq `Z`, used only as `mword_of_int W : mword 32`).  `ppo off`/`ppp off` are
   `BitVec.ofInt 64 (push_off + off)` / `(pop_off + off)` with `off : Int`.
3. Section variables `σi T` are explicit arguments.

**Rocq → Lean name map.**  `ppo` `AxSpinPO.ppo` (duplicated name: WeakAxiomatic), `ppp` `ppp`,
`Wq0a`/`Wq10`/`Wq18`/`Wq2c`/`Wq30`/`Wp08`/`Wp0c`/`Wp16` same, `q00` … `q38`, `qlw`, `qsw` same,
`p08` `p08`, `p0c` `p0c`, `p10` `p10`, `p12` `AxSpinPO.p12` (duplicated name: AxRelease5),
`p16` … `p22` same, `push_off_text` `pushOffText`, `pop_off_text` `popOffText`.
Lean-only (file-qualified): `AxSpinPO.walk0aM` … (the eight 4-byte decode walks at `drefM`).

**Dropped:** nothing (Rocq 43 definitions; Lean 43 + 8 Lean-only check lemmas).
-/
import Weak.AxSpinE7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. pcs, words, instructions -/

/-- Rocq `ppo`: the address `push_off + off`. -/
def AxSpinPO.ppo (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«push_off» : Int) + off)
/-- Rocq `ppp`: the address `pop_off + off`. -/
def ppp (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«pop_off» : Int) + off)

/-- `csrrci a5,sstatus,2`. -/
def Wq0a : BitVec 32 := 0x100177f3#32
/-- `jal mycpu` (deviation 1). -/
def Wq10 : BitVec 32 := 0x52f000ef#32
/-- `jal mycpu` (deviation 1). -/
def Wq18 : BitVec 32 := 0x527000ef#32
/-- `jal mycpu` (deviation 1). -/
def Wq2c : BitVec 32 := 0x513000ef#32
/-- `srli a5,s1,1`. -/
def Wq30 : BitVec 32 := 0x0014d793#32
/-- `jal mycpu` (deviation 1). -/
def Wp08 : BitVec 32 := 0x4bd000ef#32
/-- `csrr a5,sstatus`. -/
def Wp0c : BitVec 32 := 0x100027f3#32
/-- `bge zero,a5,panic`. -/
def Wp16 : BitVec 32 := 0x02f05363#32

/-! push_off's expanded instructions -/

def q00 : instruction := .ITYPE (sign_extend (m := 12) (32#6), .Regidx 2#5, .Regidx 2#5, .ADDI)
def q02 : instruction := .STORE (zero_extend (m := 12) (3#6 +++ 0b000#3), .Regidx 1#5, sp, 8)
def q04 : instruction := .STORE (zero_extend (m := 12) (2#6 +++ 0b000#3), .Regidx 8#5, sp, 8)
def q06 : instruction := .STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 9#5, sp, 8)
def q08 : instruction := .ITYPE (caddi4spnImm 8#8, sp, creg2reg_idx (.Cregidx 0#3), .ADDI)
def q0a : instruction := .CSRImm (256#12, 2#5, .Regidx 15#5, .CSRRC)
def q0e : instruction := .RTYPE (.Regidx 15#5, zreg, .Regidx 9#5, .ADD)
/-- `jal mycpu` (deviation 1: immediate 3374). -/
def q10 : instruction := .JAL (3374#21, .Regidx 1#5)
def qlw : instruction := .LOAD (120#12, .Regidx 10#5, .Regidx 15#5, false, 4)
def q16 : instruction :=
  .BTYPE (sign_extend (m := 13) (11#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BEQ)
/-- `jal mycpu` (deviation 1: immediate 3366). -/
def q18 : instruction := .JAL (3366#21, .Regidx 1#5)
def q1e : instruction := .ADDIW (sign_extend (m := 12) (1#6), .Regidx 15#5, .Regidx 15#5)
def qsw : instruction := .STORE (120#12, .Regidx 15#5, .Regidx 10#5, 4)
def q22 : instruction := .LOAD (zero_extend (m := 12) (3#6 +++ 0b000#3), sp, .Regidx 1#5, false, 8)
def q24 : instruction := .LOAD (zero_extend (m := 12) (2#6 +++ 0b000#3), sp, .Regidx 8#5, false, 8)
def q26 : instruction := .LOAD (zero_extend (m := 12) (1#6 +++ 0b000#3), sp, .Regidx 9#5, false, 8)
def q28 : instruction := .ITYPE (caddi16spImm 2#6, sp, sp, .ADDI)
/-- `jal mycpu` (deviation 1: immediate 3346). -/
def q2c : instruction := .JAL (3346#21, .Regidx 1#5)
def q30 : instruction := .SHIFTIOP (1#6, .Regidx 9#5, .Regidx 15#5, .SRLI)
def q34 : instruction :=
  .ITYPE (sign_extend (m := 12) (1#6), creg2reg_idx (.Cregidx 7#3), creg2reg_idx (.Cregidx 7#3), .ANDI)
def q36 : instruction := .STORE (124#12, .Regidx 15#5, .Regidx 10#5, 4)
def q38 : instruction := .JAL (sign_extend (m := 21) (2032#11 +++ 0b0#1), zreg)

/-! pop_off's (00/02/04/06 = mycpu's ins00/02/04/06; 14 = qlw; 1c = qsw;
28/2a/2c/2e = mycpu's ins18/1a/1c/1e) -/

/-- `jal mycpu` (deviation 1: immediate 3260). -/
def p08 : instruction := .JAL (3260#21, .Regidx 1#5)
def p0c : instruction := .CSRReg (256#12, zreg, .Regidx 15#5, .CSRRS)
def p10 : instruction :=
  .ITYPE (sign_extend (m := 12) (2#6), creg2reg_idx (.Cregidx 7#3), creg2reg_idx (.Cregidx 7#3), .ANDI)
def AxSpinPO.p12 : instruction :=
  .BTYPE (sign_extend (m := 13) (15#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BNE)
def p16 : instruction := .BTYPE (38#13, .Regidx 15#5, zreg, .BGE)
def p1a : instruction := .ADDIW (sign_extend (m := 12) (63#6), .Regidx 15#5, .Regidx 15#5)
def p1e : instruction :=
  .BTYPE (sign_extend (m := 13) (5#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BNE)
def p20 : instruction := .LOAD (124#12, .Regidx 10#5, .Regidx 15#5, false, 4)
def p22 : instruction :=
  .BTYPE (sign_extend (m := 13) (3#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 7#3), .BEQ)

/-! Lean-only checks (deviation 1): the eight 4-byte words decode to the instructions above. -/

theorem AxSpinPO.walk0aM : runRead drefM (ext_decode Wq0a) = some (q0a, false) := by kernel_rfl
theorem AxSpinPO.walk10M : runRead drefM (ext_decode Wq10) = some (q10, false) := by kernel_rfl
theorem AxSpinPO.walk18M : runRead drefM (ext_decode Wq18) = some (q18, false) := by kernel_rfl
theorem AxSpinPO.walk2cM : runRead drefM (ext_decode Wq2c) = some (q2c, false) := by kernel_rfl
theorem AxSpinPO.walk30M : runRead drefM (ext_decode Wq30) = some (q30, false) := by kernel_rfl
theorem AxSpinPO.walkP08M : runRead drefM (ext_decode Wp08) = some (p08, false) := by kernel_rfl
theorem AxSpinPO.walkP0cM : runRead drefM (ext_decode Wp0c) = some (p0c, false) := by kernel_rfl
theorem AxSpinPO.walkP16M : runRead drefM (ext_decode Wp16) = some (p16, false) := by kernel_rfl

/-! # 2. The text -/

section text
variable (σi : ExecSt) (T : PTree)

/-- Rocq `push_off_text`. -/
def pushOffText : Prop :=
  textAtS σi T (AxSpinPO.ppo 0x00) (AxSpinE7.hw 0x1101) ∧
  textAtS σi T (AxSpinPO.ppo 0x02) (AxSpinE7.hw 0xec06) ∧
  textAtS σi T (AxSpinPO.ppo 0x04) (AxSpinE7.hw 0xe822) ∧
  textAtS σi T (AxSpinPO.ppo 0x06) (AxSpinE7.hw 0xe426) ∧
  textAtS σi T (AxSpinPO.ppo 0x08) (AxSpinE7.hw 0x1000) ∧
  textAt4S σi T (AxSpinPO.ppo 0x0a) Wq0a ∧
  textAtS σi T (AxSpinPO.ppo 0x0e) (AxSpinE7.hw 0x84be) ∧
  textAt4S σi T (AxSpinPO.ppo 0x10) Wq10 ∧
  textAtS σi T (AxSpinPO.ppo 0x14) (AxSpinE7.hw 0x5d3c) ∧
  textAtS σi T (AxSpinPO.ppo 0x16) (AxSpinE7.hw 0xcb99) ∧
  textAt4S σi T (AxSpinPO.ppo 0x18) Wq18 ∧
  textAtS σi T (AxSpinPO.ppo 0x1c) (AxSpinE7.hw 0x5d3c) ∧
  textAtS σi T (AxSpinPO.ppo 0x1e) (AxSpinE7.hw 0x2785) ∧
  textAtS σi T (AxSpinPO.ppo 0x20) (AxSpinE7.hw 0xdd3c) ∧
  textAtS σi T (AxSpinPO.ppo 0x22) (AxSpinE7.hw 0x60e2) ∧
  textAtS σi T (AxSpinPO.ppo 0x24) (AxSpinE7.hw 0x6442) ∧
  textAtS σi T (AxSpinPO.ppo 0x26) (AxSpinE7.hw 0x64a2) ∧
  textAtS σi T (AxSpinPO.ppo 0x28) (AxSpinE7.hw 0x6105) ∧
  textAtS σi T (AxSpinPO.ppo 0x2a) (AxSpinE7.hw 0x8082) ∧
  textAt4S σi T (AxSpinPO.ppo 0x2c) Wq2c ∧
  textAt4S σi T (AxSpinPO.ppo 0x30) Wq30 ∧
  textAtS σi T (AxSpinPO.ppo 0x34) (AxSpinE7.hw 0x8b85) ∧
  textAtS σi T (AxSpinPO.ppo 0x36) (AxSpinE7.hw 0xdd7c) ∧
  textAtS σi T (AxSpinPO.ppo 0x38) (AxSpinE7.hw 0xb7c5)

/-- Rocq `pop_off_text`. -/
def popOffText : Prop :=
  textAtS σi T (ppp 0x00) (AxSpinE7.hw 0x1141) ∧ textAtS σi T (ppp 0x02) (AxSpinE7.hw 0xe406) ∧
  textAtS σi T (ppp 0x04) (AxSpinE7.hw 0xe022) ∧ textAtS σi T (ppp 0x06) (AxSpinE7.hw 0x0800) ∧
  textAt4S σi T (ppp 0x08) Wp08 ∧
  textAt4S σi T (ppp 0x0c) Wp0c ∧
  textAtS σi T (ppp 0x10) (AxSpinE7.hw 0x8b89) ∧ textAtS σi T (ppp 0x12) (AxSpinE7.hw 0xef99) ∧
  textAtS σi T (ppp 0x14) (AxSpinE7.hw 0x5d3c) ∧
  textAt4S σi T (ppp 0x16) Wp16 ∧
  textAtS σi T (ppp 0x1a) (AxSpinE7.hw 0x37fd) ∧ textAtS σi T (ppp 0x1c) (AxSpinE7.hw 0xdd3c) ∧
  textAtS σi T (ppp 0x1e) (AxSpinE7.hw 0xe789) ∧ textAtS σi T (ppp 0x20) (AxSpinE7.hw 0x5d7c) ∧
  textAtS σi T (ppp 0x22) (AxSpinE7.hw 0xc399) ∧
  textAtS σi T (ppp 0x28) (AxSpinE7.hw 0x60a2) ∧ textAtS σi T (ppp 0x2a) (AxSpinE7.hw 0x6402) ∧
  textAtS σi T (ppp 0x2c) (AxSpinE7.hw 0x0141) ∧ textAtS σi T (ppp 0x2e) (AxSpinE7.hw 0x8082)

end text

end Weak
