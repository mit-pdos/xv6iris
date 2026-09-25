/-
Proof of `namei`'s ROOT CORNER `namei("/")` (`SpecNamei.NAMEI_ROOT`, Rocq
`ProofNameiRoot.v`'s `NameiRootProof`), given namex's root corner
(`SpecNamex.NAMEX_ROOT`).  It is also Rocq's boot form
(`SpecNameiRootBoot` / `LinkNameiRootBoot.v`), which SpecNamei's header
shows collapses onto this contract.

    +0x00 .. +0x06   the 4-slot frame (ra, s0)             (NameiFrame)
    +0x08            addi a2,s0,-32    (the name buffer's address, unused)
    +0x0c            c.li a1,0         nameiparent = 0: namex's `ha1`
    +0x0e            jal namex         (SpecNamex.wp_namex_root)
    +0x12 .. +0x18   the epilogue                           (NameiFrame)

Rocq's header, kept: THE NAME BUFFER IS NOT CARVED -- on "/" no memmove
runs, so the four frame slots stay four stack slots from the push to the pop.

**Deviations from Rocq**: the corner runs at ANY interrupt state and depth
(it never parks): every step shifts the contract's `wpNext k.sie` along
(`k_step_r`, `Xv6/NamexRoot.lean`), and namex's corner is crossed at its own
`wpNext k.sie` with iget's `spie`/`spp` pin, which is namei's verbatim
(Rocq: `wp_next b p` throughout).  The per-instruction steps are the frame
rules of `Xv6/NameiFrame.lean`.
-/
import Xv6.NameiFrame
import Xv6.NamexRoot

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem namei_root_br_namex : KA.«namei» + 0xfffffffffffffe08#64 = KA.«namex» := by decide
theorem namei_root_ret_12 : jumpPc (KA.«namei» + 0x12#64) = (KA.«namei» + 0x12#64) := by decide

theorem namei_root_slots_4 (a : Nat) (h : nameiRootSlots ≤ a) : 4 ≤ a := by
  unfold nameiRootSlots at h; omega

theorem namei_root_slots_namex (a : Nat) (h : nameiRootSlots ≤ a) : namexRootSlots ≤ a - 4 := by
  unfold nameiRootSlots at h; omega

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF]
  [SleepLockG GF] [IrefslotG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]

set_option maxHeartbeats 8000000 in
/-- **THE ROOT CORNER meets its specification** (Rocq's
`NameiRootProof.wp_namei_root`), at any interrupt state and depth. -/
theorem namei_root_main (NXR : NAMEX_ROOT) (cpu : CPU) (k : KCtx) (dqp : DFrac)
    (hK : nameiRootSlots ≤ k.avail) (hnoff : k.noff + 3 < 2 ^ 31)
    (hroot : icfgDev = BitVec.ofNat 32 ROOTDEV) (hnib0 : 0 < icfgNib)
    (hit : "itable" ∉ k.locks) (hpr : "pr" ∉ k.locks) (huart : "uart1" ∉ k.locks) :
    wp_namei_root_body (hlc := hlc) (GF := GF) cpu k dqp hK hnoff hroot hnib0 hit hpr huart := by
  unfold wp_namei_root_body
  have hK4 := namei_root_slots_4 _ hK
  iintro ⟨Hk, Hpc, #Hit2, #Hiti, #Hreg, #Hpe, Hslot, Hpath, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- +0x00 .. +0x06  the prologue
  iapply (wp_prologue_namei cpu k KA.«namei» hK4)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro Hk Hpc Hframe Hlow
  k_norm_g
  icases Hlow with ⟨%w₃, %w₄, H3, H4⟩
  -- +0x08  addi a2,s0,-32 ; +0x0c  c.li a1,0 ; +0x0e  jal namex
  k_step_r (wp_s_addi cpu _ (KA.«namei» + 0x8#64) false 4064#12 12#5 8#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_addi cpu _ (KA.«namei» + 0xc#64) true 0#12 11#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_jal cpu _ (KA.«namei» + 0xe#64) false 2096634#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [namei_root_br_namex]
  iintro Hk Hpc
  -- THE CALL: namex's root corner
  have h := NXR.wp_namex_root (hlc := hlc) (GF := GF) cpu
    ((k.pushed 4).withRegs
      (((((k.regs.set (2#5) (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set (8#5) (k.regs 2#5)).set (12#5)
        (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 11#5 0#64).set (1#5) (KA.«namei» + 18#64)))
    dqp (by show namexRootSlots ≤ k.avail - 4; exact namei_root_slots_namex _ hK)
    hnoff hroot hnib0
    (by simp only [KCtx.withRegs_regs, RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true])
    hit hpr huart
  unfold wp_namex_root_body at h
  simp only [namexAddr, KCtx.withRegs_proc, KCtx.pushed_proc, KCtx.withRegs_sie, KCtx.pushed_sie,
    KCtx.withRegs_regs, RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h
  iapply h
  iframe Hk Hpc Hit2 Hiti Hreg Hpe Hslot Hpath
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro %spie %spp %R' %ipv %hsp Hk Hpc %⟨hcs, ha0⟩ Hpath Hheld
  k_norm_g [namei_root_ret_12]
  try simp only [k_norm_simps] at hsp
  unfold calleeSaved at hcs
  k_norm_g at hcs
  obtain ⟨c_2, c_8, c_9, c_18, c_19, c_20, c_21, c_22, c_23, c_24, c_25, c_26, c_27⟩ := hcs
  -- +0x12 .. +0x18  the epilogue
  have hR2E : R' 2#5 = (k.withSpie spie spp).regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    rw [c_2]; rfl
  ihave Hk := kctx_eq_mono cpu _ (((k.withSpie spie spp).pushed 4).withRegs R') (by kctx_ext) $$ Hk
  ihave Hfr := (show frame2 (GF := GF) (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) ∗
      wordPointsTo (k.regs 2#5 + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w₃ ∗
      wordPointsTo (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w₄ ⊢
      frame2 ((k.withSpie spie spp).regs 2#5) (k.regs 1#5) (k.regs 8#5) ∗
      wordPointsTo ((k.withSpie spie spp).regs 2#5 + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w₃ ∗
      wordPointsTo ((k.withSpie spie spp).regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w₄
      from .rfl) $$ [$Hframe $H3 $H4]
  icases Hfr with ⟨Hframe, H3, H4⟩
  iapply (wp_epilogue_namei cpu (k.withSpie spie spp) (KA.«namei» + 0x12#64) hK4 R' hR2E
      (k.regs 1#5) (k.regs 8#5) w₃ w₄)
    $$ [- $Hk $Hpc $Hframe $H3 $H4]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro Hk Hpc
  k_norm_g
  ihave HΦ := wpNext_at k.sie k.proc cpu cpu _ (fun _ => rfl) $$ Hnext
  iapply HΦ $$ %spie %spp %_ %ipv %hsp Hk Hpc [] Hpath Hheld
  ipureintro
  refine ⟨?_, by simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; exact ha0⟩
  unfold calleeSaved
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]
  · rw [c_9]
  · rw [c_18]
  · rw [c_19]
  · rw [c_20]
  · rw [c_21]
  · rw [c_22]
  · rw [c_23]
  · rw [c_24]
  · rw [c_25]
  · rw [c_26]
  · rw [c_27]

end

/-- THE ROOT CORNER's proof, from namex's root corner alone (Rocq's
`NameiRootProof` functor over `NamexRoot`). -/
theorem namei_root_proof (NXR : NAMEX_ROOT) : NAMEI_ROOT :=
  ⟨fun cpu k dqp hK hnoff hroot hnib0 hit hpr huart =>
    namei_root_main NXR cpu k dqp hK hnoff hroot hnib0 hit hpr huart⟩

end Xv6
