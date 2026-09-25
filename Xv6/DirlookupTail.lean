/-
`dirlookup`'s shared tail `+0x96 .. +0xaa` (Rocq `ProofDirlookup.v`'s
`Htail`, the persistent `dl_tail_body`): the record's two cells put back,
the nine restores, the pop, `ret`, and the contract discharged at whichever
arm reached it (empty directory, found, exhausted).

**Deviation from Rocq.**  Rocq proves the tail once as a persistent
`wp_next`-wrapped assertion whose continuation each arm supplies; here it is
one stage lemma entered with the arm's `dirlookupArm` resource at the return
register (the readi `rd_join` pattern), so the arm payloads still stay out
of the tail's proof.
-/
import Xv6.DirlookupDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [IregG GF] [IcacheG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]

set_option maxHeartbeats 8000000 in
/-- **`+0x96 .. +0xaa`: THE TAIL** -- the record's cells, the epilogue, and
the contract's continuation at the arm the caller reached it on. -/
theorem dirlookup_tail (cpu : CPU) (k : KCtx) (spie spp : Bool) (R : RegMap)
    (ip : BitVec 64) (dinum : BitVec 32) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (dn dr : Dinode) (fn : Nat → BitVec 8) (hasp : Bool) (pofv pidv : BitVec 32)
    (dqp dqd dqn : DFrac) (found : Bool) (kk kslot : Nat) (q : Qp)
    (v10 : BitVec 64) (bs : List (BitVec 8)) (a0 : BitVec 64)
    (hK : 12 ≤ k.avail)
    (hal : (dirlookupDeAddr (k.regs 2#5)).toNat % 8 = 0)
    (hR2 : R 2#5 = dirlookupDeAddr (k.regs 2#5)) (ha0 : R 10#5 = a0)
    (h24 : R 24#5 = k.regs 24#5) (h25 : R 25#5 = k.regs 25#5)
    (h26 : R 26#5 = k.regs 26#5) (h27 : R 27#5 = k.regs 27#5) :
    kctx cpu (((k.withSpie spie spp).pushed 12).withRegs R) ∗ pcIs cpu (KA.«dirlookup» + 0x96#64) ∗
    dirlookupFrame (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5)
      (k.regs 20#5) (k.regs 21#5) (k.regs 22#5) (k.regs 23#5) v10 ∗
    dirlookupDe (k.regs 2#5) bs ∗
    trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
    dirlookupKeep k ip dinum bm data dn dr fn pidv dqp dqd dqn ∗
    dirlookupArm data dn fn hasp (k.regs 12#5) pofv found kk kslot q a0 ∗
    (∀ c' : CPU, dirlookupPost k ip dinum bm data dn dr fn hasp pofv pidv dqp dqd dqn c')
    ⊢ wpLoop (GF := GF) cpu := by
  have hK' : 12 ≤ (k.withSpie spie spp).avail := hK
  iintro ⟨Hk, Hpc, Hframe, Hde, Hte, Hce, Hkeep, Harm, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases dirlookup_frame_close _ _ _ _ _ _ _ _ _ _ _ bs hal $$ [Hframe Hde]
    with ⟨%v10', %v11', Hf⟩
  · iframe
  iapply (wp_epilogue_dirlookup cpu (k.withSpie spie spp) (KA.«dirlookup» + 0x96#64) hK' R hR2
      (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5) (k.regs 20#5)
      (k.regs 21#5) (k.regs 22#5) (k.regs 23#5) v10 v10' v11')
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  k_next_e
  iintro Hk Hpc
  k_norm_g
  ispecialize Hnext $$ %cpu
  ihave HΦ := dirlookupPost_elim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hnext
  iapply HΦ $$ %spie %spp %_ %found %kk %kslot %q [] Hk Hpc Hte Hce Hkeep
  · ipureintro
    unfold calleeSaved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] <;>
      first | rfl | assumption
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, ha0]
    iexact Harm

end

end Xv6
