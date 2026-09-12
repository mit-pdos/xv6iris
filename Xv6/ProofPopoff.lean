/-
Proof of `pop_off`'s specification (`SpecPopoff.POPOFF`), given the
interface of `mycpu`: the prologue, the call, `intr_get()` (a `csrr` of
`sstatus`, whose `SIE` bit is `0`, so the `unreachable` arm is dead), the
depth check (dead too: the depth is at least 1), the decrement of
`c->noff` inside the context's per-cpu cells, and -- at depth 0 -- the
`intena` check, which finds `0` (the exit stays interrupts-off); then the
epilogue.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecPopoff
import Xv6.SpecMycpu
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! ## Facts -/

/-- With `SIE = 0`, `sstatus & SIE = 0`. -/
theorem sie0_and2 (v : BitVec 64) (h : BitVec.extractLsb' 1 1 v = 0#1) : v &&& 2#64 = 0#64 := by
  bv_decide

/-- With `SIE = 0`, `(sstatus >> 1) & 1 = 0`. -/
theorem sie0_shr_and1 (v : BitVec 64) (h : BitVec.extractLsb' 1 1 v = 0#1) : (v >>> 1) &&& 1#64 = 0#64 := by
  bv_decide

theorem bcond_bne_00 : bcond bop.BNE 0#64 0#64 = false := by decide
theorem bcond_beq_00 : bcond bop.BEQ 0#64 0#64 = true := by decide

theorem ofNat64_eq_zero_iff (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0#64 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro h; subst h; rfl

theorem bcond_bne_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    bcond bop.BNE (BitVec.ofNat 64 n) 0#64 = decide (n ≠ 0) := by
  simp only [bcond]
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 n ≠ 0#64 := fun e => h ((ofNat64_eq_zero_iff n hn).mp e)
    simp [this, h]

theorem bcond_beq_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    bcond bop.BEQ (BitVec.ofNat 64 n) 0#64 = decide (n = 0) := by
  simp only [bcond]
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 n ≠ 0#64 := fun e => h ((ofNat64_eq_zero_iff n hn).mp e)
    simp [this, h]

/-- `blez` on a positive count is not taken. -/
theorem bcond_bge_zero_pos (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) :
    bcond bop.BGE 0#64 (BitVec.ofNat 64 n) = false := by
  have hlt : (0#64).slt (BitVec.ofNat 64 n) = true := by
    have hmsb : (BitVec.ofNat 64 n).msb = false := by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_of_msb hmsb, BitVec.toInt_zero, BitVec.toNat_ofNat]
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [bcond, hlt, Bool.not_true]

theorem extractLsb'_ofNat64 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]

theorem ofNat_add_neg1' (i : Nat) (hi : 1 ≤ i) (hi' : i < 2 ^ 32) :
    BitVec.ofNat 64 i + 0xFFFFFFFFFFFFFFFF#64 = BitVec.ofNat 64 (i - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i - 1 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : 0xFFFFFFFFFFFFFFFF < 2 ^ 64)]
  omega

/-- `addiw a5,a5,-1` on a count in `[1, 2^31)`. -/
theorem addiw_pred (n : Nat) (h1 : 1 ≤ n) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n + 0xFFFFFFFFFFFFFFFF#64)) =
      BitVec.ofNat 64 (n - 1) := by
  rw [ofNat_add_neg1' n h1 (by omega), extractLsb'_ofNat64 _ (by omega)]
  exact signExtend_ofNat32 _ (by omega)

/-- `addiw a5,a5,1` on a count with `n + 1 < 2^31`. -/
theorem addiw_succ (n : Nat) (hn : n + 1 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n + 1#64)) = BitVec.ofNat 64 (n + 1) := by
  have h32 : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n + 1#64) = BitVec.ofNat 32 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    omega
  rw [h32]
  exact signExtend_ofNat32 _ hn

/-- The exit context of a `c->noff` store inside a two-slot body, when the
new depth is the popped one. -/
theorem withCpu_popOff2 (k : KCtx) (R : RegMap) :
    ((k.pushed 2).withRegs R).withCpu R (k.noff - 1) k.intena = (k.popOff.pushed 2).withRegs R := rfl

set_option maxHeartbeats 4000000 in
theorem pop_off_proof (M : MYCPU) : POPOFF := ⟨fun {hlc GF} _ _ cpu k hsie hnoff hK hlks hexit => by
  unfold wp_pop_off_body
  iintro ⟨Hk, Hpc, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  have hn31 : k.noff < 2 ^ 31 := hwf.2.2.2.2
  simp only [popOffAddr, KernelSyms.«pop_off»]
  k_norm
  -- prologue
  iapply (wp_prologue2 cpu k hsie 0x80000bfa#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- jal mycpu
  k_step (wp_s_jal cpu _ ?hs 0x80000c02#64 false 3256#21 1#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  have hm := M.wp_mycpu (hlc := hlc) (GF := GF) cpu ((k.pushed 2).withRegs
      (((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64)).set 8#5 (k.regs 2#5)).set 1#5 0x80000c06#64))
    (by k_norm) (by k_norm; omega)
  unfold wp_mycpu_body at hm
  simp only [mycpuAddr, KernelSyms.«mycpu»] at hm
  k_norm at hm
  iapply hm
  iframe
  iintro %R2 Hk Hpc %⟨hcs2, h10⟩
  have hret : jumpPc 0x80000c06#64 = 0x80000c06#64 := by simp only [jumpPc, BitVec.reduceAnd]
  k_norm [hret]
  -- csrr a5,sstatus
  k_step (wp_s_csrr_sstatus cpu _ ?hs 0x80000c06#64 false 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro %v %hv Hk Hpc
  simp only [sstatusAt] at hv
  k_norm at hv
  -- andi a5,a5,2
  k_step (wp_s_andi cpu _ ?hs 0x80000c0a#64 true 2#12 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [sie0_and2 v hv]
  iintro Hk Hpc
  -- bnez a5, c2a: not taken
  k_step (wp_s_branch cpu _ ?hs 0x80000c0c#64 true 30#13 15#5 0#5 (by decide) bop.BNE) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [bcond_bne_00]
  iintro Hk Hpc
  -- lw a5,120(a0)
  k_step (wp_s_lw_noff cpu _ ?hs 0x80000c0e#64 true 120#12 15#5 10#5 (by decide) ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [h10]
  case haddr => k_norm [h10]; rfl
  iintro Hk Hpc
  -- blez a5, c36: not taken
  k_step (wp_s_branch0 cpu _ ?hs 0x80000c10#64 false 38#13 15#5 (by decide) bop.BGE) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [bcond_bge_zero_pos k.noff hnoff hn31]
  iintro Hk Hpc
  -- addiw a5,a5,-1
  k_step (wp_s_addiw cpu _ ?hs 0x80000c14#64 true 4095#12 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [addiw_pred k.noff hnoff hn31]
  iintro Hk Hpc
  -- sw a5,120(a0): the depth becomes noff - 1
  k_step (wp_s_sw_noff cpu _ ?hs 0x80000c16#64 true 120#12 10#5 15#5 ?haddr (k.noff - 1) ?hval ?hwf') from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [h10, withCpu_popOff2]
  case haddr => k_norm [h10]; rfl
  case hval => k_norm; exact extractLsb'_ofNat64 _ (by omega)
  case hwf' =>
    obtain ⟨w1, w2, w3, w4, w5⟩ := hwf
    unfold KCtx.wf
    simp only [KCtx.withCpu_sie, KCtx.withCpu_noff, KCtx.withCpu_intena, KCtx.withCpu_locks, KCtx.withCpu_tier,
      KCtx.withRegs_sie, KCtx.withRegs_intena, KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.pushed_sie,
      KCtx.pushed_intena, KCtx.pushed_locks, KCtx.pushed_tier]
    refine ⟨fun h => ?_, fun _ => hsie, fun h => absurd h (by rw [hsie]; decide), hlks, by omega⟩
    rw [hsie]; symm; exact hexit (by omega)
  iintro Hk Hpc
  -- bnez a5, c22
  by_cases hn1 : k.noff = 1
  · -- the count reached 0: read `c->intena` (0), skip the re-enable
    have h0 : k.noff - 1 = 0 := by omega
    have hint : k.intena = false := hexit hn1
    k_step (wp_s_branch cpu _ ?hs 0x80000c18#64 true 10#13 15#5 0#5 (by decide) bop.BNE) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [h0, bcond_bne_00]
    iintro Hk Hpc
    k_step (wp_s_lw_intena cpu _ ?hs 0x80000c1a#64 true 124#12 15#5 10#5 (by decide) ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [h10, hint]
    case haddr => k_norm [h10]; rfl
    iintro Hk Hpc
    k_step (wp_s_branch cpu _ ?hs 0x80000c1c#64 true 6#13 15#5 0#5 (by decide) bop.BEQ) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [bcond_beq_00]
    iintro Hk Hpc
    iapply (wp_epilogue2 cpu k.popOff (by k_norm) 0x80000c22#64 (by k_norm; omega) _ ?hR2
      (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc
    ipureintro
    obtain ⟨hs2, _, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hcs2
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
    unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    exact ⟨h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
    case hR2 => k_norm; rw [hcs2.1]; simp [RegMap.set_apply]
  · -- the count is still positive: straight to the epilogue
    have hd : k.noff - 1 ≠ 0 := by omega
    k_step (wp_s_branch cpu _ ?hs 0x80000c18#64 true 10#13 15#5 0#5 (by decide) bop.BNE) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [bcond_bne_ofNat (k.noff - 1) (by omega), decide_eq_true hd]
    iintro Hk Hpc
    iapply (wp_epilogue2 cpu k.popOff (by k_norm) 0x80000c22#64 (by k_norm; omega) _ ?hR2
      (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc
    ipureintro
    obtain ⟨hs2, _, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hcs2
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
    unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    exact ⟨h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
    case hR2 => k_norm; rw [hcs2.1]; simp [RegMap.set_apply]
⟩

end Xv6
