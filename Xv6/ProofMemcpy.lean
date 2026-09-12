/-
Proof of `memcpy`'s specification (`SpecMemcpy.MEMCPY`), given the
interface of `memmove`: the prologue, the call (discharged by
`MEMMOVE.wp_memmove` at the callee's context), the epilogue.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecMemcpy
import Xv6.SpecMemmove
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option maxHeartbeats 4000000 in
theorem memcpy_proof (M : MEMMOVE) : MEMCPY := ⟨fun {hlc GF} _ _ cpu k bs olds n dqs hsie htier hK hn hn32 hls hld => by
  unfold wp_memcpy_body
  iintro ⟨Hk, Hpc, Hsrc, Hdst, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  simp only [memcpyAddr, KernelSyms.«memcpy»]
  k_norm
  ihave HΦ := wpNext_off _ _ _ $$ HΦ
  -- prologue
  iapply (wp_prologue2 cpu k hsie htier 0x80000d3a#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- jal ra, memmove
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000d42#64 false 2097048#21 1#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- the call
  have hm := M.wp_memmove (hlc := hlc) (GF := GF) cpu ((k.pushed 2).withRegs
      ((((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64)).set 8#5 (k.regs 2#5)).set 1#5 0x80000d46#64)))
    bs olds n dqs (by k_norm) (by k_norm) (by k_norm; omega) (by k_norm; exact hn) hn32 hls hld
  unfold wp_memmove_body at hm
  simp only [memmoveAddr, KernelSyms.«memmove»] at hm
  k_norm at hm
  iapply hm
  iframe
  iapply wpNext_off_intro
  iintro %R' Hk Hpc Hsrc Hdst %⟨hcs, h10⟩
  have hret : jumpPc 0x80000d46#64 = 0x80000d46#64 := by simp only [jumpPc, BitVec.reduceAnd]
  k_norm [hret]
  have hR2 : R' 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64 := by
    rw [hcs.1]; simp [RegMap.set_apply]
  -- epilogue
  iapply (wp_epilogue2 cpu k hsie htier 0x80000d46#64 (by omega) R' hR2 (k.regs 1#5) (k.regs 8#5))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc
  iapply HΦ $$ %_ Hk Hpc Hsrc Hdst
  ipureintro
  obtain ⟨_, _, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hcs
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h10
  constructor
  · unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    exact ⟨h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
    exact h10⟩

end Xv6
