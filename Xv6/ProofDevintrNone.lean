/-
Proof of `devintr`'s third arm (`SpecDevintrNone.DEVINTR_NONE`): no
callees.

```
 +0x00  prologue (4 slots: ra at 24(sp), s0 at 16(sp))
 +0x08  csrr a4,scause
 +0x0c  a5 = -1 << 63 + 9 ; +0x12 beq a4,a5 (not taken: not the external cause)
 +0x16  a5 = -1 << 63 + 5 ; +0x1c a0 = 0 ; +0x1e beq a4,a5 (not taken: not the timer)
 +0x22  epilogue, returning 0
```
-/
import MachCSL.WpSmodeFrame
import MachCSL.WpSmodeFrame6
import MachCSL.WpSmodeTrapCsr
import Xv6.SpecDevintrNone
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

theorem dvn_ext : sCause InterruptType.I_S_External = 0x8000000000000009#64 := by decide
theorem dvn_tim : sCause InterruptType.I_S_Timer = 0x8000000000000005#64 := by decide

theorem dvn_beq_ext (sc : BitVec 64) (h : ¬ sCauseOk sc) :
    bcond bop.BEQ sc 0x8000000000000009#64 = false := by
  unfold sCauseOk at h
  rw [dvn_ext, dvn_tim] at h
  simp only [bcond]
  exact decide_eq_false (fun he => h (Or.inr he))

theorem dvn_beq_tim (sc : BitVec 64) (h : ¬ sCauseOk sc) :
    bcond bop.BEQ sc 0x8000000000000005#64 = false := by
  unfold sCauseOk at h
  rw [dvn_ext, dvn_tim] at h
  simp only [bcond]
  exact decide_eq_false (fun he => h (Or.inl he))

set_option maxHeartbeats 8000000 in
/-- **`devintr`'s third arm meets its specification.** -/
theorem devintr_none_proof : DEVINTR_NONE :=
  ⟨fun {hlc GF} _ _ cpu k sc hsie hK hsc => by
  unfold wp_devintr_none_body
  simp only [devintrAddr]
  iintro ⟨Hk, Hpc, Hsc, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  iapply (wp_prologue4s0_gen cpu k KA.«devintr» hK)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  k_norm
  iapply wpNext_off_intro
  iintro Hk Hpc Hframe
  -- +0x08  csrr a4,scause
  k_step (wp_s_csrr_scause cpu _ ?hs (KA.«devintr» + 0x8#64) false 14#5 (by decide) sc)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc Hsc
  k_step (wp_s_addi cpu _ (KA.«devintr» + 0xc#64) true 4095#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_slli cpu _ (KA.«devintr» + 0xe#64) true 63#6 15#5 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_addi cpu _ (KA.«devintr» + 0x10#64) true 9#12 15#5 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_branch cpu _ (KA.«devintr» + 0x12#64) false 24#13 14#5 15#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [dvn_beq_ext sc hsc]
  iintro Hk Hpc
  k_step (wp_s_addi cpu _ (KA.«devintr» + 0x16#64) true 4095#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_slli cpu _ (KA.«devintr» + 0x18#64) true 63#6 15#5 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_addi cpu _ (KA.«devintr» + 0x1a#64) true 5#12 15#5 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_addi cpu _ (KA.«devintr» + 0x1c#64) true 0#12 10#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_branch cpu _ (KA.«devintr» + 0x1e#64) false 96#13 14#5 15#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [dvn_beq_tim sc hsc]
  iintro Hk Hpc
  -- +0x22  the epilogue
  iapply (wp_epilogue4s0_gen cpu k (KA.«devintr» + 0x22#64) hK _ ?h2 (k.regs 1#5) (k.regs 8#5))
    $$ [- $Hk $Hpc $Hframe]
  rotate_right 1
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  k_norm
  iapply wpNext_off_intro
  iintro Hk Hpc
  iapply HΦ $$ %_ Hk Hpc Hsc
  · ipureintro
    unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
    simp
  case h2 => simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]⟩

end Xv6
