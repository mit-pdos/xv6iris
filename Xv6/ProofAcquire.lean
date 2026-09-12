/-
Proof of `acquire`'s specification (`SpecAcquire.ACQUIRE`), given the
interfaces of `push_off`, `holding` and `mycpu`: the four-slot prologue,
`push_off`, the (dead) re-entrancy check through `holding`'s not-held
contract, the `amoswap.w.aq` spin (Löb induction: a failed swap leaves
the lock word 1 and the held set unchanged; the winning swap hands out
the pre-token, the payload at this context and the view receipt), the
owner-word store of `mycpu()`, the epilogue.
-/
import MachCSL.WpSmodeFrame
import MachCSL.WpLock
import Xv6.SpecAcquire
import Xv6.SpecPushoff
import Xv6.SpecHolding
import Xv6.SpecMycpu
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option maxHeartbeats 4000000 in
/-- The spin: from `0x80000bd4` with `a4 = 1` and `s1 = lk`, the loop
`mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; bnez a5` runs until the
swap returns 0; the registers other than `a5` are those of `R0`. -/
theorem acquire_spin {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (kb : KCtx) (hsie : kb.sie = false) (htier : kb.tier = KTier.bare)
    (γ : GName) (lk : BitVec 64) (s : String) (R : CtxId → IProp GF) [CtxMorph R]
    (hs : s ∉ kb.locks) (hlen : kb.locks.length < kb.noff) (R0 : RegMap) (h9 : R0 9#5 = lk) (h14 : R0 14#5 = 1#64) :
    kernelText ∗ isLock γ lk s R ∗
    (∀ R' : RegMap, kctx cpu ((kb.withRegs R').withLocks (s :: kb.locks)) -∗
      pcIs cpu 0x80000bde#64 -∗ ⌜∀ i, i ≠ 15#5 → R' i = R0 i⌝ -∗
      lockedPre γ cpu -∗ R curCtx -∗ lockCtxHeld -∗ (∃ K : Nat, viewLb cpu K) -∗ wpLoop cpu)
    ⊢ ∀ Rc : RegMap, ⌜∀ i, i ≠ 15#5 → Rc i = R0 i⌝ -∗
      kctx cpu (kb.withRegs Rc) -∗ pcIs cpu 0x80000bd4#64 -∗ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, #Hlk, HΦ⟩
  iloeb as IH
  iintro %Rc %hinv Hk Hpc
  have hc9 : Rc 9#5 = lk := by rw [hinv 9#5 (by decide)]; exact h9
  have hc14 : Rc 14#5 = 1#64 := by rw [hinv 14#5 (by decide)]; exact h14
  -- mv a5,a4
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000bd4#64 true 15#5 0#5 14#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc] with [hc14]
  iintro Hk Hpc
  -- amoswap.w.aq a5,a5,(s1)
  k_step (wp_s_amoswap_lock cpu _ ?hs ?ht 0x80000bd6#64 false 15#5 9#5 15#5 (by decide) γ lk s R
    ?haddr ?hval ?hnot ?hlen) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
  case haddr => k_norm; exact hc9
  case hval => k_norm; rfl
  case hnot => k_norm; exact hs
  case hlen => k_norm; exact hlen
  iintro %old Hk Hpc Hpost
  -- sext.w a5,a5
  k_step (wp_s_addiw cpu _ ?hs ?ht 0x80000bda#64 true 0#12 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
    with [sext_low_sext old]
  iintro Hk Hpc
  by_cases h0 : old = 0#32
  · -- won: fall through to 0x80000bde
    subst h0
    k_step (wp_s_branch cpu _ ?hs ?ht 0x80000bdc#64 true 8184#13 15#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
      $$ [- $Hk $Hpc] with [bcond_bne_zero, acqLocks_zero]
    case htgt => k_tgt
    iintro Hk Hpc
    icases (show acqPost γ R cpu 0#32 ⊢ lockedPre γ cpu ∗ R curCtx ∗ lockCtxHeld ∗ ∃ K : Nat, viewLb cpu K from by
      rw [acqPost_zero]) $$ Hpost with ⟨Hpre, HR, Hheld, Hview⟩
    k_norm [acqLocks_zero]
    iapply HΦ $$ %_ Hk Hpc %_ Hpre HR Hheld Hview
    intro i hi
    simp only [RegMap.set_apply, hi, ite_false]
    exact hinv i hi
  · -- lost: the word was 1; back to 0x80000bd4
    k_step (wp_s_branch cpu _ ?hs ?ht 0x80000bdc#64 true 8184#13 15#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
      $$ [- $Hk $Hpc] with [bcond_bne_sext_ne old h0, acqLocks_ne s _ h0]
    case htgt => k_tgt
    iintro Hk Hpc
    icases (show acqPost γ R cpu old ⊢ emp from by rw [acqPost_ne γ R cpu h0]) $$ Hpost with _
    k_norm [acqLocks_ne s _ h0]
    iapply IH $$ HΦ %_ %_ Hk Hpc
    intro i hi
    simp only [RegMap.set_apply, hi, ite_false]
    exact hinv i hi

set_option maxHeartbeats 4000000 in
theorem acquire_proof (PU : PUSHOFF) (HO : HOLDING) (MC : MYCPU) : ACQUIRE := ⟨
  fun {hlc GF} _ _ cpu k γ s R _ hsie htier hnoff hK hs => by
  unfold wp_acquire_body
  iintro ⟨Hk, #Htext, Hpc, #Hlk, HΦ⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  simp only [acquireAddr, KernelSyms.«acquire»]
  k_norm
  ihave HΦ := wpNext_off _ _ _ $$ HΦ
  -- prologue
  iapply (wp_prologue4s1 cpu k hsie htier 0x80000bba#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- mv s1,a0
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000bc4#64 true 9#5 0#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- jal push_off
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000bc6#64 false 2097082#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  case htgt => k_tgt
  iintro Hk Hpc
  have hpu : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hnoff' : k'.noff + 1 < 2 ^ 31)
      (hK' : 6 ≤ k'.avail),
      kctx cpu k' ∗ kernelText ∗ pcIs cpu 0x80000b80#64 ∗
      (∀ R' : RegMap, kctx cpu (k'.pushOff.withRegs R') -∗ pcIs cpu (retPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hnoff' hK'
    have h := PU.wp_push_off (hlc := hlc) (GF := GF) cpu k' hsie' htier' hnoff' hK'
    unfold wp_push_off_body at h
    simp only [pushOffAddr, KernelSyms.«push_off»] at h
    exact h
  iapply (hpu _ ?hs ?ht ?hn ?hK) $$ [- $Hk $Hpc]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hn => k_norm; omega
  case hK => k_norm; omega
  iintro %R2 Hk Hpc %hcs2
  have hret1 : retPc 0x80000bca#64 = 0x80000bca#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret1]
  k_norm at hcs2
  have h9 : R2 9#5 = k.regs 10#5 := by
    have := hcs2.2.2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at this
    exact this
  -- mv a0,s1
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000bca#64 true 10#5 0#5 9#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [h9]
  iintro Hk Hpc
  -- jal holding
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000bcc#64 false 2097032#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  case htgt => k_tgt
  iintro Hk Hpc
  have hho : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hK' : 6 ≤ k'.avail)
      (hs' : s ∉ k'.locks),
      kctx cpu k' ∗ kernelText ∗ pcIs cpu 0x80000b54#64 ∗ isLock γ (k'.regs 10#5) s R ∗
      (∀ R' : RegMap, kctx cpu (k'.withRegs R') -∗ pcIs cpu (retPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R' ∧ R' 10#5 = 0#64⌝ -∗ wpLoop cpu) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hK' hs'
    have h := HO.wp_holding_notheld (hlc := hlc) (GF := GF) cpu k' γ s R hsie' htier' hK' hs'
    unfold wp_holding_notheld_body at h
    simp only [holdingAddr, KernelSyms.«holding»] at h
    exact h
  iapply (hho _ ?hs ?ht ?hK ?hnot) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  case hnot => k_norm; exact hs
  iintro %R3 Hk Hpc %⟨hcs3, h10⟩
  have hret2 : retPc 0x80000bd0#64 = 0x80000bd0#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret2]
  k_norm at hcs3
  -- li a4,1
  k_step (wp_s_addi cpu _ ?hs ?ht 0x80000bd0#64 true 1#12 14#5 0#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- bnez a0, panic: not taken (holding answered 0)
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000bd2#64 true 28#13 10#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [h10, bcond_bne_zero]
  case htgt => k_tgt
  iintro Hk Hpc
  -- the spin
  have h39 : R3 9#5 = k.regs 10#5 := by
    have := hcs3.2.2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at this
    rw [this]; exact h9
  iapply (acquire_spin cpu (k.pushOff.pushed 4) (by k_norm) (by k_norm) γ (k.regs 10#5) s R
    (by k_norm; exact hs) (by k_norm; exact Nat.lt_succ_of_le hwf.2.2.2.1) (R3.set 14#5 1#64)
    (by simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; exact h39)
    (by simp only [RegMap.set_apply, BitVec.reduceEq, ite_true])) $$ [HΦ Hframe] %_ %(fun _ _ => rfl) Hk Hpc
  -- after the spin: mycpu, the owner store, the epilogue
  iframe #
  iintro %R' Hk Hpc %hR' Hpre HR Hheld Hview
  k_norm
  -- jal mycpu
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000bde#64 false 3292#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  case htgt => k_tgt
  iintro Hk Hpc
  have hmc : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hK' : 2 ≤ k'.avail),
      kctx cpu k' ∗ kernelText ∗ pcIs cpu 0x800018ba#64 ∗
      (∀ R' : RegMap, kctx cpu (k'.withRegs R') -∗ pcIs cpu (retPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R' ∧ R' 10#5 = cpuAddr cpu⌝ -∗ wpLoop cpu) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hK'
    have h := MC.wp_mycpu (hlc := hlc) (GF := GF) cpu k' hsie' htier' hK'
    unfold wp_mycpu_body at h
    simp only [mycpuAddr, KernelSyms.«mycpu»] at h
    exact h
  iapply (hmc _ ?hs ?ht ?hK) $$ [- $Hk $Hpc]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  iintro %R4 Hk Hpc %⟨hcs4, h10'⟩
  have hret3 : retPc 0x80000be2#64 = 0x80000be2#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret3]
  k_norm at hcs4
  have h49 : R4 9#5 = k.regs 10#5 := by
    have := hcs4.2.2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at this
    rw [this, hR' 9#5 (by decide)]
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    exact h39
  -- sd a0,16(s1): lk->cpu = mycpu()
  k_step (wp_s_sd_lkcpu_acquire cpu _ ?hs ?ht 0x80000be2#64 true 16#12 9#5 10#5 γ (k.regs 10#5) s R ?haddr ?hval) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hpre]
  case haddr => k_norm [h49]
  case hval => k_norm; exact h10'
  iintro Hk Hpc Hlc
  -- epilogue
  have h42 : R4 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    have := hcs4.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at this
    rw [this, hR' 2#5 (by decide)]
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    have h32 := hcs3.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at h32
    rw [h32]
    have h22 := hcs2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h22
    exact h22
  iapply (wp_epilogue4s1 cpu ((k.withLocks (s :: k.locks)).pushOff) (by k_norm) (by k_norm) 0x80000be4#64
    (by k_norm; omega) R4 (by k_norm; exact h42) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5)) $$ [- $Hk $Hpc]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc
  k_norm
  iapply HΦ $$ %_ Hk Hpc [] [Hlc Hheld] HR Hview
  · ipureintro
    obtain ⟨c4_2, c4_8, c4_9, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27⟩ := hcs4
    obtain ⟨c3_2, c3_8, c3_9, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27⟩ := hcs3
    obtain ⟨c2_2, c2_8, c2_9, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩ := hcs2
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c4_18 c4_19 c4_20 c4_21 c4_22 c4_23 c4_24 c4_25 c4_26 c4_27
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c3_18 c3_19 c3_20 c3_21 c3_22 c3_23 c3_24 c3_25 c3_26 c3_27
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c2_18 c2_19 c2_20 c2_21 c2_22 c2_23 c2_24 c2_25 c2_26 c2_27
    have hR'' : ∀ i, i ≠ 15#5 → i ≠ 14#5 → R' i = R3 i := by
      intro i hi hi'
      rw [hR' i hi]
      simp only [RegMap.set_apply, hi', ite_false]
    unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, _root_.true_and,
      _root_.and_true]
    exact ⟨(c4_18.trans (hR'' _ (by decide) (by decide))).trans (c3_18.trans c2_18),
      (c4_19.trans (hR'' _ (by decide) (by decide))).trans (c3_19.trans c2_19),
      (c4_20.trans (hR'' _ (by decide) (by decide))).trans (c3_20.trans c2_20),
      (c4_21.trans (hR'' _ (by decide) (by decide))).trans (c3_21.trans c2_21),
      (c4_22.trans (hR'' _ (by decide) (by decide))).trans (c3_22.trans c2_22),
      (c4_23.trans (hR'' _ (by decide) (by decide))).trans (c3_23.trans c2_23),
      (c4_24.trans (hR'' _ (by decide) (by decide))).trans (c3_24.trans c2_24),
      (c4_25.trans (hR'' _ (by decide) (by decide))).trans (c3_25.trans c2_25),
      (c4_26.trans (hR'' _ (by decide) (by decide))).trans (c3_26.trans c2_26),
      (c4_27.trans (hR'' _ (by decide) (by decide))).trans (c3_27.trans c2_27)⟩
  · iapply locked_intro; iframe Hlc Hheld⟩

end Xv6
