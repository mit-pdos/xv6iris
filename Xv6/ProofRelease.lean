/-
Proof of `release`'s specification (`SpecRelease.RELEASE`), given the
interfaces of `holding` and `pop_off`: the four-slot prologue, the (dead)
ownership check through `holding`'s held contract, the owner-word clear,
the fence, the word store that frees the lock (depositing the payload),
`pop_off`, the epilogue.
-/
import MachCSL.WpSmodeFrame
import MachCSL.WpLock
import Xv6.SpecRelease
import Xv6.SpecPopoff
import Xv6.SpecHolding
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option maxHeartbeats 4000000 in
theorem release_proof (HO : HOLDING) (PO : POPOFF) : RELEASE := ⟨
  fun {hlc GF} _ _ cpu k γ s R _ hsie htier hnoff hK hexit => by
  unfold wp_release_body
  iintro ⟨Hk, #Htext, Hpc, #Hlk, Hlocked, HR, HΦ⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  simp only [releaseAddr, KernelSyms.«release»]
  k_norm
  -- prologue
  iapply (wp_prologue4s1 cpu k hsie htier 0x80000c42#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- mv s1,a0
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000c4c#64 true 9#5 0#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- jal holding
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000c4e#64 false 2096902#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  case htgt => k_tgt
  iintro Hk Hpc
  have hho : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hK' : 6 ≤ k'.avail),
      kctx cpu k' ∗ kernelText ∗ pcIs cpu 0x80000b54#64 ∗ isLock γ (k'.regs 10#5) s R ∗
      locked γ cpu ∗
      (∀ R' : RegMap, kctx cpu (k'.withRegs R') -∗ pcIs cpu (retPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R' ∧ R' 10#5 = 1#64⌝ -∗ locked γ cpu -∗ wpLoop cpu) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hK'
    have h := HO.wp_holding_locked (hlc := hlc) (GF := GF) cpu k' γ s R hsie' htier' hK'
    unfold wp_holding_locked_body at h
    simp only [holdingAddr, KernelSyms.«holding»] at h
    exact h
  iapply (hho _ ?hs ?ht ?hK) $$ [- $Hk $Hpc $Hlocked]
  rotate_right 1
  k_norm
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  iintro %R2 Hk Hpc %⟨hcs2, h10⟩ Hlocked
  have hret1 : retPc 0x80000c52#64 = 0x80000c52#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret1]
  k_norm at hcs2
  have h29 : R2 9#5 = k.regs 10#5 := by
    have := hcs2.2.2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at this
    exact this
  -- beqz a0, panic: not taken (holding answered 1)
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000c52#64 true 28#13 10#5 0#5 (by decide) bop.BEQ ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [h10, bcond_beq_one]
  case htgt => k_tgt
  iintro Hk Hpc
  icases locked_cases γ cpu $$ Hlocked with ⟨Hlc, Hheld⟩
  -- sd zero,16(s1): lk->cpu = 0
  k_step (wp_s_sd_zero_lkcpu_release cpu _ ?hs ?ht 0x80000c54#64 false 16#12 9#5 γ (k.regs 10#5) s R ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hlc]
  case haddr => k_norm [h29]
  iintro Hk Hpc Hlp
  -- fence rw,w
  k_step (wp_s_fence_rw_w cpu _ ?hs ?ht 0x80000c58#64 false 0#5 0#5) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- sw zero,0(s1): the lock is free
  k_step (wp_s_sw_zero_release cpu _ ?hs ?ht 0x80000c5c#64 false 0#12 9#5 γ (k.regs 10#5) s R ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hlp $Hheld $HR]
  case haddr => k_norm [h29]
  iintro Hk Hpc %hmem
  -- jal pop_off
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000c60#64 false 2097050#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  case htgt => k_tgt
  iintro Hk Hpc
  have hpo : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hnoff' : 1 ≤ k'.noff)
      (hK' : 4 ≤ k'.avail) (hlks' : k'.locks.length ≤ k'.noff - 1) (hexit' : k'.noff = 1 → k'.intena = false),
      kctx cpu k' ∗ kernelText ∗ pcIs cpu 0x80000bfa#64 ∗
      (∀ R' : RegMap, kctx cpu (k'.popOff.withRegs R') -∗ pcIs cpu (retPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hnoff' hK' hlks' hexit'
    have h := PO.wp_pop_off (hlc := hlc) (GF := GF) cpu k' hsie' htier' hnoff' hK' hlks' hexit'
    unfold wp_pop_off_body at h
    simp only [popOffAddr, KernelSyms.«pop_off»] at h
    exact h
  have hflt : (k.locks.filter (fun x => x ≠ s)).length < k.locks.length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨s, hmem, by simp⟩
  iapply (hpo _ ?hs ?ht ?hn ?hK ?hl ?he) $$ [- $Hk $Hpc]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hn => k_norm; omega
  case hK => k_norm; omega
  case hl => k_norm; have := hwf.2.2.2.1; omega
  case he => k_norm; exact hexit
  iintro %R3 Hk Hpc %hcs3
  have hret2 : retPc 0x80000c64#64 = 0x80000c64#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret2]
  k_norm at hcs3
  -- epilogue
  have h32 : R3 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    have := hcs3.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at this
    rw [this]
    have h22 := hcs2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h22
    exact h22
  iapply (wp_epilogue4s1 cpu ((k.withLocks (k.locks.filter (fun x => x ≠ s))).popOff) (by k_norm) (by k_norm)
    0x80000c64#64 (by k_norm; omega) R3 (by k_norm; exact h32) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5))
    $$ [- $Hk $Hpc]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc
  k_norm
  iapply HΦ $$ %_ Hk Hpc
  ipureintro
  obtain ⟨c3_2, c3_8, c3_9, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27⟩ := hcs3
  obtain ⟨c2_2, c2_8, c2_9, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩ := hcs2
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c3_18 c3_19 c3_20 c3_21 c3_22 c3_23 c3_24 c3_25 c3_26 c3_27
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c2_18 c2_19 c2_20 c2_21 c2_22 c2_23 c2_24 c2_25 c2_26 c2_27
  unfold calleeSaved
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
  exact ⟨c3_18.trans c2_18, c3_19.trans c2_19, c3_20.trans c2_20, c3_21.trans c2_21, c3_22.trans c2_22,
    c3_23.trans c2_23, c3_24.trans c2_24, c3_25.trans c2_25, c3_26.trans c2_26, c3_27.trans c2_27⟩⟩

end Xv6
