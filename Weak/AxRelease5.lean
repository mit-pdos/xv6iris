/-
Weak: **VACUITY CHECK of `release_wpd4`'s text facts on xv6's REAL release bytes** (the pure
half).  An `rli_*` premise of Rocq `release_wpd4` (AxRelease4) is
`kernel_text -∗ instr4 σi T satp0 ArmedR Ex_rel pc is_rvc ins`, and `AxRelease.instr4` =
(text arm) ∧ `pure4`.  Here:
  `exRel`   — the concrete exact-register map of release;
  `pure4`   — `instr4`'s non-text part at `armedR` / `exRel`;
  `AxRelease5.pXX` — `pure4` PROVED at every one of the 20 release words (pc / is_rvc / AST):
              the armed / fence / sw-zero facts, base ≠ tp, src ≠ tp, `exBase` (every access
              base exact: sp, or s1 in the lock window; c.sdsp data ra/s0/s1 exact at entry),
              `exOk` (the exact map is a valid dataflow annotation at every sequential step).
The COMPRESSED decode halves of the text arm at the 10 compressed release words are AxRelease7's
`dc00`…`dc08` and AxRelease8's `dc0a`…`dc28`; the 4-byte decode facts are AxLeafS3's
(+ the ctrl words).  `rf0 (execute ins)` for the 4 compressed ALU words: AxSymEngine2's
`rf0ExecuteRTYPEADD` (c.mv) and AxRelease6's `rf0ExecuteITYPEADDI` (c.addi sp / c.addi4spn /
c.addi16sp).

Rocq: `iris/AxRelease5.v` @ xxvzwolszwmp.

THE EXACT-REGISTER MAP of xv6's release (offsets from `release`):
  `[0x00, 0x0c]`: ra, s0, s1, a0 exact (the entry state, the frame push, s0 := sp+32,
                  s1 := a0);
  `[0x10, 0x1e]`: s1 exact (the window of the lock-word stores — the return point of
                  `holding` establishes it);
  elsewhere     : nothing (after the epilogue reloads).

KERNEL CROSS-CHECK (Xv6/KernelImage.lean, release = 0x80000ce0, as AxRelease's header): the 20
words agree with Rocq's ASTs EXCEPT the last two (deviation 2): +0x00 0x1101 `c.addi sp,-32`,
+0x02/04/06 0xec06/0xe822/0xe426 `c.sdsp ra/s0/s1`, +0x08 0x1000 `c.addi4spn s0,sp,32`, +0x0a
0x84aa `c.mv s1,a0`, +0x0c 0xf07ff0ef `jal holding` (0x80000bf2, offset −250 = 2096902 mod 2^21),
+0x10 0xcd11 `c.beqz a0,+28`, +0x12 0x0004b823 `sd zero,16(s1)`, +0x16 0x0310000f `fence rw,w`,
+0x1a 0x0004a023 `sw zero,0(s1)`, +0x1e 0xf9bff0ef `jal pop_off` (0x80000c98, −102 = 2097050),
+0x22/24/26 0x60e2/0x6442/0x64a2 `c.ldsp ra/s0/s1`, +0x28 0x6105 `c.addi16sp sp,32`, +0x2a 0x8082
`c.ret`, +0x2c 0x00006517 `auipc a0,0x6`, +0x30 0x36c50513 `addi a0,a0,876`, +0x34 0xb4dff0ef
`jal unreachable` (0x80000860, −1204 = 2095948).

## Deviations from Rocq

1. SPELLING (as AxRelease deviation 3 / AxRelease7 deviation 1): `mword n` ↦ `BitVec n`,
   `mword_of_int k : mword n` ↦ `k#n`, `mword_of_int (KernelSyms.release + k)` ↦
   `Xv6.releaseAddr + k#64`, `uint pc - KernelSyms.release` ↦ `(pc.toNat : Int) -
   Xv6.releaseAddr.toNat`, `uint r = k` ↦ `r.toNat = k`, `add_vec_int pc 2` / `4` ↦
   `pc + 2#64` / `pc + 4#64`, `sign_extend' 12` ↦ `sign_extend (m := 12)`, `zero_extend' 12
   (concat_vec u 'b"000")` ↦ `zero_extend (m := 12) (u +++ 0b000#3)`, `zeros' 12` ↦
   `zeros (n := 12)`, `caddi4spn_imm`/`caddi16sp_imm` ↦ `caddi4spnImm`/`caddi16spImm`,
   `ArmedR` ↦ AxCondM4's `armedR`, `src_ok` ↦ `AxRelease.srcOk`.
2. KERNEL DRIFT (the Lean image is xv6-riscv b72cbac1): release+0x30 is `addi a0,a0,876`
   (Rocq 948) and release+0x34 is `jal unreachable`, offset −1204 = `2095948#21` (Rocq: `2095970#21`, offset
   −1182).  `AxRelease5.p30` / `AxRelease5.p34` state the
   Lean image's words.  (Both are outside the exact windows; their `pure4` is trivial either way.)
3. The Rocq tactics `rofs` / `guint` / `guint0` / `nmw` / `nreg` / `exact_c` / `ex_ok_c` /
   `pure_c` (vm_compute rewriting of `uint` / `rel_off` literals) are replaced by one Lean macro
   `ax_release5_pure`: the decidable conjuncts (armed, src, `exBase`, `exOk` — `exOk`'s `∀ r` is
   over `BitVec 5`, decidable in core) go by `decide` after unfolding; `isSwz` / `baseOk3` /
   `AxRelease.srcOk` (quantified over `BitVec 12` / `Nat`, or `≠` on `regidx`, which has no
   `DecidableEq`) through Lean-only boolean tests (`AxRelease5.isSwzB` / `baseOk3B` / `srcOkB`)
   and their soundness lemmas.

**Rocq → Lean name map.**  `rel_off` `relOff`, `Ex_rel` `exRel`, `pure4` `pure4` (none in the
duplicated-name table); `p12` `AxRelease5.p12` (duplicated with AxSpinPO); `p_XX`
`AxRelease5.pXX` FILE-QUALIFIED (the bare camelCase names `p08`/`p0c`/`p10`/`p16`/`p1a`/`p1e`/
`p22` are AxSpinPO's instruction defs), except `p_12` ↦ `AxRelease5.p12b` (its camelCase
`p12` is Rocq `p12`'s; the two Rocq lemmas have the same statement).  Tactics: see deviation 3.

**Dropped:** nothing.  Rocq 3 definitions + 21 lemmas (+ 8 Ltacs); Lean 3 definitions + 21
theorems, plus Lean-only (file-qualified): `AxRelease5.isSwzB` / `baseOk3B` / `srcOkB`,
`AxRelease5.notIsSwzOfB` / `baseOk3OfB` / `srcOkOfB`, and the macro `ax_release5_pure`.
-/
import Weak.AxCondM4
import Weak.AxRelease

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rel_off`: the offset of `pc` from `release`. -/
def relOff (pc : BitVec 64) : Int := (pc.toNat : Int) - (Xv6.releaseAddr.toNat : Int)

/-- Rocq `Ex_rel`: THE EXACT-REGISTER MAP of xv6's release. -/
def exRel (pc : BitVec 64) (r : BitVec 5) : Prop :=
  (0 ≤ relOff pc ∧ relOff pc ≤ 12 ∧ (r.toNat = 1 ∨ r.toNat = 8 ∨ r.toNat = 9 ∨ r.toNat = 10)) ∨
  (16 ≤ relOff pc ∧ relOff pc ≤ 30 ∧ r.toNat = 9)

/-- Rocq `pure4`: the non-text part of `AxRelease.instr4` at `armedR` / `exRel`. -/
def pure4 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  (if is_rvc then ¬ armedR (pc + 2#64) else (armedR (pc + 4#64) → ins = fenceRwWIns)) ∧
  (isSwz ins → armedR pc) ∧ (baseOk3 ins ∧ AxRelease.srcOk ins) ∧
  exBase exRel pc is_rvc ins ∧ exOk exRel pc is_rvc ins

/-- (Lean-only) a boolean `isSwz` test. -/
def AxRelease5.isSwzB (ins : instruction) : Bool :=
  match ins with
  | .STORE (_, .Regidx s2, _, w) => s2 == 0#5 && w == 4
  | _ => false

/-- (Lean-only) a boolean `baseOk3` test. -/
def AxRelease5.baseOk3B (ins : instruction) : Bool :=
  match ins with
  | .STORE (_, _, .Regidx b, _) => b != 4#5
  | _ => true

/-- (Lean-only) a boolean `AxRelease.srcOk` test. -/
def AxRelease5.srcOkB (ins : instruction) : Bool :=
  match ins with
  | .STORE (_, .Regidx s2, _, _) => s2 != 4#5
  | .RTYPE (.Regidx s2, _, _, _) => s2 != 4#5
  | _ => true

theorem AxRelease5.notIsSwzOfB (ins : instruction) (h : AxRelease5.isSwzB ins = false) :
    ¬ isSwz ins := by
  rintro ⟨imm, rs1, rfl⟩
  simp [AxRelease5.isSwzB] at h

theorem AxRelease5.baseOk3OfB (ins : instruction) (h : AxRelease5.baseOk3B ins = true) :
    baseOk3 ins := by
  intro imm rs2 rs1 wd e
  subst e
  intro e'
  injection e' with e'
  subst e'
  simp [AxRelease5.baseOk3B] at h

theorem AxRelease5.srcOkOfB (ins : instruction) (h : AxRelease5.srcOkB ins = true) :
    AxRelease.srcOk ins := by
  unfold AxRelease.srcOk
  split
  · intro e'
    injection e' with e'
    subst e'
    simp [AxRelease5.srcOkB] at h
  · intro e'
    injection e' with e'
    subst e'
    simp [AxRelease5.srcOkB] at h
  · trivial

/-- (Lean-only; Rocq `pure_c`) prove `pure4 pc is_rvc ins` at a literal pc / AST. -/
macro "ax_release5_pure" : tactic => `(tactic| (
  unfold pure4
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [↓reduceIte, Bool.false_eq_true]
    all_goals first
    | (unfold armedR Xv6.releaseAddr; decide)
    | (intro h; exfalso; revert h; unfold armedR Xv6.releaseAddr; decide)
    | (intro _; rfl)
  · first
    | exact fun h => absurd h (AxRelease5.notIsSwzOfB _ (by decide))
    | (intro _; unfold armedR Xv6.releaseAddr; decide)
  · exact AxRelease5.baseOk3OfB _ (by decide)
  · exact AxRelease5.srcOkOfB _ (by decide)
  · dsimp only [exBase, exactAt, exRel, relOff, sp, zreg, creg2reg_idx, Xv6.releaseAddr]
    all_goals decide
  · dsimp only [exOk, exSrc, exactAt, exRel, relOff, sp, zreg, creg2reg_idx, instrLen,
      Xv6.releaseAddr]
    all_goals decide))

theorem AxRelease5.p12 : pure4 (Xv6.releaseAddr + 0x12#64) false
    (.STORE (16#12, zreg, .Regidx 9#5, 8)) := by
  ax_release5_pure

/-! ## The pure half of every `rli_*` fact, at the real release words -/

theorem AxRelease5.p00 : pure4 Xv6.releaseAddr true
    (.ITYPE (sign_extend (m := 12) (32#6), .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  ax_release5_pure

theorem AxRelease5.p02 : pure4 (Xv6.releaseAddr + 0x2#64) true
    (.STORE (zero_extend (m := 12) (3#6 +++ 0b000#3), .Regidx 1#5, sp, 8)) := by
  ax_release5_pure

theorem AxRelease5.p04 : pure4 (Xv6.releaseAddr + 0x4#64) true
    (.STORE (zero_extend (m := 12) (2#6 +++ 0b000#3), .Regidx 8#5, sp, 8)) := by
  ax_release5_pure

theorem AxRelease5.p06 : pure4 (Xv6.releaseAddr + 0x6#64) true
    (.STORE (zero_extend (m := 12) (1#6 +++ 0b000#3), .Regidx 9#5, sp, 8)) := by
  ax_release5_pure

theorem AxRelease5.p08 : pure4 (Xv6.releaseAddr + 0x8#64) true
    (.ITYPE (caddi4spnImm 8#8, sp, creg2reg_idx (.Cregidx 0#3), .ADDI)) := by
  ax_release5_pure

theorem AxRelease5.p0a : pure4 (Xv6.releaseAddr + 0xa#64) true
    (.RTYPE (.Regidx 10#5, zreg, .Regidx 9#5, .ADD)) := by
  ax_release5_pure

theorem AxRelease5.p0c : pure4 (Xv6.releaseAddr + 0xc#64) false
    (.JAL (2096902#21, .Regidx 1#5)) := by
  ax_release5_pure

theorem AxRelease5.p10 : pure4 (Xv6.releaseAddr + 0x10#64) true
    (.BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 2#3),
      .BEQ)) := by
  ax_release5_pure

theorem AxRelease5.p12b : pure4 (Xv6.releaseAddr + 0x12#64) false
    (.STORE (16#12, zreg, .Regidx 9#5, 8)) := by
  ax_release5_pure

theorem AxRelease5.p16 : pure4 (Xv6.releaseAddr + 0x16#64) false
    (.FENCE (0#4, 3#4, 1#4, zreg, zreg)) := by
  ax_release5_pure

theorem AxRelease5.p1a : pure4 (Xv6.releaseAddr + 0x1a#64) false
    (.STORE (0#12, zreg, .Regidx 9#5, 4)) := by
  ax_release5_pure

theorem AxRelease5.p1e : pure4 (Xv6.releaseAddr + 0x1e#64) false
    (.JAL (2097050#21, .Regidx 1#5)) := by
  ax_release5_pure

theorem AxRelease5.p22 : pure4 (Xv6.releaseAddr + 0x22#64) true
    (.LOAD (zero_extend (m := 12) (3#6 +++ 0b000#3), sp, .Regidx 1#5, false, 8)) := by
  ax_release5_pure

theorem AxRelease5.p24 : pure4 (Xv6.releaseAddr + 0x24#64) true
    (.LOAD (zero_extend (m := 12) (2#6 +++ 0b000#3), sp, .Regidx 8#5, false, 8)) := by
  ax_release5_pure

theorem AxRelease5.p26 : pure4 (Xv6.releaseAddr + 0x26#64) true
    (.LOAD (zero_extend (m := 12) (1#6 +++ 0b000#3), sp, .Regidx 9#5, false, 8)) := by
  ax_release5_pure

theorem AxRelease5.p28 : pure4 (Xv6.releaseAddr + 0x28#64) true
    (.ITYPE (caddi16spImm 2#6, sp, sp, .ADDI)) := by
  ax_release5_pure

theorem AxRelease5.p2a : pure4 (Xv6.releaseAddr + 0x2a#64) true
    (.JALR (zeros (n := 12), .Regidx 1#5, zreg)) := by
  ax_release5_pure

theorem AxRelease5.p2c : pure4 (Xv6.releaseAddr + 0x2c#64) false
    (.UTYPE (6#20, .Regidx 10#5, .AUIPC)) := by
  ax_release5_pure

theorem AxRelease5.p30 : pure4 (Xv6.releaseAddr + 0x30#64) false
    (.ITYPE (876#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
  ax_release5_pure

theorem AxRelease5.p34 : pure4 (Xv6.releaseAddr + 0x34#64) false
    (.JAL (2095948#21, .Regidx 1#5)) := by
  ax_release5_pure

/- The compressed DECODE halves `dc_XX` are in AxRelease7 / AxRelease8. -/

end Weak
