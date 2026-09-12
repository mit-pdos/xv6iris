/-
Proof of `holding`'s two contracts (`SpecHolding.HOLDING`), given the
interface of `mycpu`: the racy load of the lock word, the early return
when it is 0, else the four-slot prologue, the racy load of the owner
word, the call to `mycpu`, the comparison (`sub`, `seqz`), the epilogue.

Not held: the word may read anything; if it is nonzero the owner word is
not this hart's `&cpus[i]`, so the comparison answers 0.  Held: the word
reads 1 and the owner word is this hart's pointer, so the comparison
answers 1.
-/
import MachCSL.WpSmodeFrame
import MachCSL.WpLock
import Xv6.SpecHolding
import Xv6.SpecMycpu
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! ## Arithmetic -/

theorem bcond_bne_00' : bcond bop.BNE 0#64 0#64 = false := by decide

theorem bcond_bne_sext_ne (w : BitVec 32) (h : w ≠ 0#32) : bcond bop.BNE (BitVec.signExtend 64 w) 0#64 = true := by
  simp only [bcond, bne_iff_ne, ne_eq]
  intro h'
  apply h
  bv_decide

theorem bcond_bne_one : bcond bop.BNE (BitVec.signExtend 64 lkOne) 0#64 = true := by decide

/-- `seqz` of a nonzero difference (in the executor's normal form). -/
theorem sltiu_diff_ne (a b : BitVec 64) (h : a ≠ b) :
    (if (a + -b).ult 1#64 then 1#64 else 0#64) = 0#64 := by
  rw [if_neg]
  intro hlt
  apply h
  bv_decide

/-- `seqz` of a zero difference. -/
theorem sltiu_diff_eq (a : BitVec 64) :
    (if (a + -a).ult 1#64 then 1#64 else 0#64) = 1#64 := by
  rw [if_pos]
  bv_decide

/-- The context inside `holding`'s frame. -/
abbrev holdingFrameCtx (k : KCtx) : KCtx :=
  (k.pushed 4).withRegs ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5 (k.regs 2#5))

/-! ## The shared tail: the owner word, mycpu, the comparison, the epilogue -/

set_option maxHeartbeats 4000000 in
/-- The prologue-to-return tail of `holding` from `0x80000b5c`, for a
context `k` whose `a0` is `lk`, given what the owner-word load answers
(`P` before, `Q w` after, with the answer `w`) and the comparison's value. -/
theorem holding_tail (MC : MYCPU) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 6 ≤ k.avail)
    (P : IProp GF) (Q : BitVec 64 → IProp GF) (ans : BitVec 64)
    (hld : instr (GF := GF) 0x80000b66#64 true (instruction.LOAD (16#12, regidx.Regidx 10#5, regidx.Regidx 15#5, false, 8)) ∗
      kctx cpu (holdingFrameCtx k) ∗ pcIs cpu 0x80000b66#64 ∗ P ∗
      ▷ wpNext (holdingFrameCtx k).sie (holdingFrameCtx k).proc cpu (fun cpu' =>
          iprop(∀ w : BitVec 64, kctx cpu' ((holdingFrameCtx k).setReg 15#5 w) -∗
            pcIs cpu' (0x80000b66#64 + instrLen true) -∗ Q w -∗ wpLoop cpu'))
      ⊢ wpLoop cpu)
    (hans : ∀ w, Q w ⊢ ⌜(if (w + -cpuAddr cpu).ult 1#64 then 1#64 else 0#64) = ans⌝ ∗ Q w) :
    kernelText ∗ kctx cpu k ∗ pcIs cpu 0x80000b5c#64 ∗ P ∗
    (∀ (R' : RegMap) (w : BitVec 64), kctx cpu (k.withRegs R') -∗ pcIs cpu (retPc (k.regs 1#5)) -∗
      ⌜calleeSaved k.regs R' ∧ R' 10#5 = ans⌝ -∗ Q w -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, Hk, Hpc, HP, HΦ⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  -- prologue
  iapply (wp_prologue4s1 cpu k hsie htier 0x80000b5c#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) HT
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- ld a5,16(a0): the owner word
  iapply hld $$ [- $Hk $Hpc $HP]
  k_code (text_instr _ _ _ _ rfl rfl) HT
  inext
  k_norm
  iapply wpNext_off_intro
  iintro %w Hk Hpc HQ
  k_norm
  -- mv s1,a5
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000b68#64 true 9#5 0#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- jal mycpu
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000b6a#64 false 3408#21 1#5 (by decide) ?htgt) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
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
  iintro %R2 Hk Hpc %⟨hcs2, h10⟩
  have hret : retPc 0x80000b6e#64 = 0x80000b6e#64 := by simp only [retPc, BitVec.reduceAnd]
  k_norm [hret]
  -- sub a0,s1,a0
  k_step (wp_s_sub cpu _ ?hs ?ht 0x80000b6e#64 false 10#5 9#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
    with [hcs2.2.2.1, h10]
  iintro Hk Hpc
  -- sltiu a0,a0,1
  icases hans w $$ HQ with ⟨%hval, HQ⟩
  k_step (wp_s_sltiu cpu _ ?hs ?ht 0x80000b72#64 false 1#12 10#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
    with [hval]
  iintro Hk Hpc
  -- epilogue
  have h2 := hcs2.1
  k_norm at h2
  have hR2 : ((R2.set 10#5 (w + -cpuAddr cpu)).set 10#5 ans) 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    exact h2
  iapply (wp_epilogue4s1 cpu k hsie htier 0x80000b76#64 (by omega) _ hR2 (k.regs 1#5) (k.regs 8#5) (k.regs 9#5))
    $$ [- $Hk $Hpc]
  k_code (text_instr _ _ _ _ rfl rfl) HT
  k_norm
  iframe
  inext
  iintro Hk Hpc
  iapply HΦ $$ %_ %w Hk Hpc [] HQ
  ipureintro
  k_norm at hcs2
  obtain ⟨c2_2, c2_8, c2_9, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩ := hcs2
  constructor
  · unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    exact ⟨c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]

/-! ## The two contracts -/

set_option maxHeartbeats 4000000 in
theorem holding_notheld_proof (MC : MYCPU) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 6 ≤ k.avail) (hs : s ∉ k.locks) :
    wp_holding_notheld_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hK hs := by
  unfold wp_holding_notheld_body
  iintro ⟨Hk, #Htext, Hpc, #Hlk, HΦ⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  ihave Hk := (show kctx cpu k ⊢ kctx cpu (k.withRegs k.regs) from by rw [KCtx.withRegs_self]) $$ Hk
  simp only [holdingAddr, KernelSyms.«holding»]
  -- lw a5,0(a0): racy
  k_step (wp_s_lw_lockword cpu _ ?hs ?ht 0x80000b54#64 true 0#12 15#5 10#5 (by decide) γ (k.regs 10#5) s R ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc]
  case haddr => k_norm
  iintro %w Hk Hpc
  by_cases hw : w = 0#32
  · -- the word is 0: not held; return 0
    subst hw
    k_step (wp_s_branch cpu _ ?hs ?ht 0x80000b56#64 true 6#13 15#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [bcond_bne_00']
    case htgt => k_tgt
    iintro Hk Hpc
    -- li a0,0
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000b58#64 true 0#12 10#5 0#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    -- ret
    k_step (wp_s_ret cpu _ ?hs ?ht 0x80000b5a#64 true 1#5) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc
    ipureintro
    constructor
    · unfold calleeSaved
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, BitVec.reduceSignExtend, BitVec.add_zero]
  · -- the word is nonzero: read the owner word, which is not ours
    k_step (wp_s_branch cpu _ ?hs ?ht 0x80000b56#64 true 6#13 15#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
      $$ [- $Hk $Hpc] with [bcond_bne_sext_ne w hw]
    case htgt => k_tgt
    iintro Hk Hpc
    iapply (holding_tail MC cpu (k.withRegs (k.regs.set 15#5 (BitVec.signExtend 64 w))) hsie htier hK
      (isLock γ (k.regs 10#5) s R) (fun w' => iprop(⌜w' ≠ cpuAddr cpu⌝)) 0#64 ?hld ?hans)
    rotate_right 1
    · iframe Hk Hpc
      iframe #
      iintro %R' %w' Hk Hpc %hcs %_
      k_norm
      iapply HΦ $$ %_ Hk Hpc
      ipureintro
      obtain ⟨hcs, h10⟩ := hcs
      refine ⟨?_, h10⟩
      unfold calleeSaved at hcs ⊢
      simp only [KCtx.withRegs_regs, RegMap.set_apply, BitVec.reduceEq, ite_false] at hcs
      exact hcs
    case hld =>
      iintro ⟨#Hi, Hk, Hpc, #Hlk, HΦ'⟩
      iapply (wp_s_ld_lkcpu_notheld cpu (holdingFrameCtx (k.withRegs (k.regs.set 15#5 (BitVec.signExtend 64 w))))
        (by k_norm [holdingFrameCtx]) (by k_norm [holdingFrameCtx]) 0x80000b66#64 true 16#12 15#5 10#5 (by decide) γ
        (k.regs 10#5) s R (by k_norm [holdingFrameCtx]) (by k_norm [holdingFrameCtx]; exact hs))
      iframe Hk Hpc
      iframe #
      inext
      iapply wpNext_mono $$ HΦ'
      iintro %cpu' HK %w' Hk Hpc %hne
      iapply HK $$ %w' Hk Hpc
      ipureintro; exact hne
    case hans =>
      intro w'
      iintro %hne
      isplit
      · ipureintro; exact sltiu_diff_ne w' (cpuAddr cpu) hne
      · ipureintro; exact hne

set_option maxHeartbeats 4000000 in
theorem holding_locked_proof (MC : MYCPU) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 6 ≤ k.avail) :
    wp_holding_locked_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hK := by
  unfold wp_holding_locked_body
  iintro ⟨Hk, #Htext, Hpc, #Hlk, Hlocked, HΦ⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  ihave Hk := (show kctx cpu k ⊢ kctx cpu (k.withRegs k.regs) from by rw [KCtx.withRegs_self]) $$ Hk
  icases locked_cases γ cpu $$ Hlocked with ⟨Hlc, Hheld⟩
  simp only [holdingAddr, KernelSyms.«holding»]
  -- lw a5,0(a0): 1 for the holder
  k_step (wp_s_lw_lockword_locked cpu _ ?hs ?ht 0x80000b54#64 true 0#12 15#5 10#5 (by decide) γ (k.regs 10#5) s R ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hlc]
  case haddr => k_norm
  iintro %w Hk Hpc %hw Hlc
  subst hw
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000b56#64 true 6#13 15#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [bcond_bne_one]
  case htgt => k_tgt
  iintro Hk Hpc
  iapply (holding_tail MC cpu (k.withRegs (k.regs.set 15#5 (BitVec.signExtend 64 lkOne))) hsie htier hK
    iprop(isLock γ (k.regs 10#5) s R ∗ lockedCore γ cpu) (fun w' => iprop(⌜w' = cpuAddr cpu⌝ ∗ lockedCore γ cpu))
    1#64 ?hld ?hans)
  rotate_right 1
  · iframe Hk Hpc Hlc
    iframe #
    iintro %R' %w' Hk Hpc %hcs ⟨%_, Hlc⟩
    k_norm
    iapply HΦ $$ %_ Hk Hpc
    · ipureintro
      obtain ⟨hcs, h10⟩ := hcs
      refine ⟨?_, h10⟩
      unfold calleeSaved at hcs ⊢
      simp only [KCtx.withRegs_regs, RegMap.set_apply, BitVec.reduceEq, ite_false] at hcs
      exact hcs
    · iapply locked_intro; iframe Hlc Hheld
  case hld =>
    iintro ⟨#Hi, Hk, Hpc, ⟨#Hlk, Hlc⟩, HΦ'⟩
    iapply (wp_s_ld_lkcpu_locked cpu (holdingFrameCtx (k.withRegs (k.regs.set 15#5 (BitVec.signExtend 64 lkOne))))
      (by k_norm [holdingFrameCtx]) (by k_norm [holdingFrameCtx]) 0x80000b66#64 true 16#12 15#5 10#5 (by decide) γ
      (k.regs 10#5) s R (by k_norm [holdingFrameCtx]))
    iframe Hk Hpc Hlc
    iframe #
    inext
    iapply wpNext_mono $$ HΦ'
    iintro %cpu' HK Hk Hpc Hlc
    iapply HK $$ %(cpuAddr cpu) Hk Hpc
    iframe Hlc
    ipureintro; rfl
  case hans =>
    intro w'
    iintro ⟨%heq, Hlc⟩
    subst heq
    iframe Hlc
    isplit
    · ipureintro; exact sltiu_diff_eq (cpuAddr cpu)
    · ipureintro; rfl

theorem holding_proof (MC : MYCPU) : HOLDING :=
  ⟨fun {_ _} _ _ cpu k γ s R hsie htier hK hs => holding_notheld_proof MC cpu k γ s R hsie htier hK hs,
   fun {_ _} _ _ cpu k γ s R hsie htier hK => holding_locked_proof MC cpu k γ s R hsie htier hK⟩

end Xv6
