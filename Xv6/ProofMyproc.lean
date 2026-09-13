/-
Proof of `myproc`'s specification (`SpecMyproc.MYPROC`), given the
interfaces of `push_off` and `pop_off`: the four-slot prologue, the call
to `push_off`, the inlined `mycpu()` (read `tp`, index `cpus`), the load
of `c->proc` out of the context's per-cpu cells, the call to `pop_off`,
the epilogue.  The value returned is the context's current proc.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecMyproc
import Xv6.SpecPushoff
import Xv6.SpecPopoff
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! ## Arithmetic -/

/-- The hart id, sign-extended from 32 bits and scaled by `sizeof (struct cpu)`. -/
theorem hart_shift' (cpu : CPU) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (hartId cpu)) <<< 7 = BitVec.ofNat 64 (128 * cpu.val) := by
  have hv : cpu.val < 8 := cpu.isLt
  have h32 : BitVec.extractLsb' 0 32 (hartId cpu) = BitVec.ofNat 32 cpu.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [hartId, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : cpu.val < 18446744073709551616)]
  rw [h32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 cpu.val).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.add_zero,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : cpu.val < 4294967296), Nat.mod_eq_of_lt (by omega : cpu.val < 18446744073709551616)]
  omega

/-- The inlined `mycpu()` address chain lands on `&cpus[hartid].proc`:
`auipc a4; addi a4,a4,-1382` is `pid_lock` (= `cpus - 48`), plus the
hart's `128 * id`, plus the load's `48`. -/
theorem myproc_cpu_addr (cpu : CPU) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (hartId cpu)) <<< 7 +
      (0x800018ee#64 + (BitVec.signExtend 64 (17#20 ++ 0#12) + 18446744073709550282#64)) = aCpuProc cpu := by
  rw [hart_shift']
  simp only [BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceAdd]
  unfold aCpuProc cpuAddr procOff cpuSize
  have hb : (KernelGeom.cpusBase : BitVec 64) = 0x800123b8#64 := rfl
  rw [hb, BitVec.add_comm, BitVec.add_zero]

set_option maxHeartbeats 4000000 in
theorem myproc_proof (PU : PUSHOFF) (PO : POPOFF) : MYPROC := ⟨fun {hlc GF} _ _ cpu k hsie hnoff hK => by
  unfold wp_myproc_body
  iintro ⟨Hk, Hpc, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  simp only [myprocAddr, KernelSyms.«myproc»]
  k_norm
  ihave HΦ := wpNext_off _ _ _ $$ HΦ
  -- prologue
  iapply (wp_prologue4s1 cpu k hsie 0x800018da#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- jal push_off
  k_step (wp_s_jal cpu _ 0x800018e4#64 false 2093724#21 1#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- push_off (its contract, unfolded, at the callee's context)
  have hpu : ∀ (k' : KCtx) (hnoff' : k'.noff + 1 < 2 ^ 31) (hK' : 6 ≤ k'.avail),
      kctx cpu k' ∗ pcIs cpu 0x80000b80#64 ∗
      wpNext k'.sie k'.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
        ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
        kctx cpu' ((k'.pushOffAt spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R'⌝ -∗ sieArm cpu' k'.sie k'.proc -∗ wpLoop cpu')) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hnoff' hK'
    have h := PU.wp_push_off (hlc := hlc) (GF := GF) cpu k' hnoff' hK'
    unfold wp_push_off_body at h
    simp only [pushOffAddr, KernelSyms.«push_off»] at h
    exact h
  iapply (hpu _ ?hn ?hK) $$ [- $Hk $Hpc]
  rotate_right 1
  case hn => k_norm; omega
  case hK => k_norm; omega
  k_norm
  iapply wpNext_off_intro
  iintro %spie %spp %R2 %hsp Hk Hpc %hcs2 _
  obtain ⟨rfl, rfl⟩ := hsp (by trivial)
  k_norm [KCtx.pushOffAt_off']
  have hret1 : jumpPc 0x800018e8#64 = 0x800018e8#64 := by simp only [jumpPc, BitVec.reduceAnd]
  k_norm [hret1]
  -- mv a5,tp
  k_step (wp_s_add cpu _ 0x800018e8#64 true 15#5 0#5 4#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- sext.w a5,a5
  k_step (wp_s_addiw cpu _ 0x800018ea#64 true 0#12 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- slli a5,a5,7
  k_step (wp_s_slli cpu _ 0x800018ec#64 true 7#6 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- auipc a4
  k_step (wp_s_auipc cpu _ 0x800018ee#64 false 17#20 14#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- addi a4,a4,-1334
  k_step (wp_s_addi cpu _ 0x800018f2#64 false 2714#12 14#5 14#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- add a5,a5,a4
  k_step (wp_s_add cpu _ 0x800018f6#64 true 15#5 15#5 14#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  iintro Hk Hpc
  -- ld a5,48(a5): c->proc
  k_step (wp_s_ld_proc cpu _ ?hs 0x800018f8#64 true 48#12 15#5 15#5 (by decide) ?haddr) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]

  case haddr => k_norm; exact myproc_cpu_addr cpu
  iintro Hk Hpc
  -- mv s1,a5
  k_step (wp_s_add cpu _ 0x800018fa#64 true 9#5 0#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- jal pop_off
  k_step (wp_s_jal cpu _ 0x800018fc#64 false 2093822#21 1#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- pop_off (its contract, unfolded, at the callee's context)
  have hpo : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : 1 ≤ k'.noff)
      (hK' : 4 ≤ k'.avail) (hlks' : k'.locks.length ≤ k'.noff - 1)
      (reen : Bool) (hreen : reen = (decide (k'.noff = 1) && k'.intena))
      (hon' : reen = true → k'.tier = .kpt ∧ trapRes true + 2 ≤ k'.avail),
      kctx cpu k' ∗ pcIs cpu 0x80000bfa#64 ∗ popArm cpu k' reen ∗
      wpNext (k'.popExit reen).sie k'.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
        kctx cpu' ((k'.popExit reen).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu')) ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' hnoff' hK' hlks' reen hreen hon'
    have h := PO.wp_pop_off (hlc := hlc) (GF := GF) cpu k' hsie' hnoff' hK' hlks' reen hreen hon'
    unfold wp_pop_off_body at h
    simp only [popOffAddr, KernelSyms.«pop_off»] at h
    exact h
  iapply (hpo _ ?hs ?hn ?hK ?hl false ?hr ?ho) $$ [- $Hk $Hpc]
  rotate_right 1
  case hs => k_norm
  case hn => k_norm; omega
  case hK => k_norm; omega
  case hl => k_norm; exact hwf.2.2.2.1
  case hr =>
    k_norm
    cases h : k.intena
    · simp
    · have hn0 : k.noff ≠ 0 := fun h0 => by have := hwf.1 h0; rw [hsie, h] at this; cases this
      simp <;> omega
  case ho => intro h; cases h
  simp only [KCtx.popExit_false, popArm_false]
  isplitl []
  · iempintro
  k_norm [KCtx.popExit_false, popArm_false]
  iapply wpNext_off_intro
  iintro %R4 Hk Hpc %hcs4
  have hret2 : jumpPc 0x80001900#64 = 0x80001900#64 := by simp only [jumpPc, BitVec.reduceAnd]
  k_norm [hret2]
  try simp only [KCtx.withRegs_regs] at hcs2 hcs4
  -- mv a0,s1
  k_step (wp_s_add cpu _ 0x80001900#64 true 10#5 0#5 9#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- epilogue
  have hR2 : (R4.set 10#5 (R4 9#5)) 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    rw [hcs4.1]
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    rw [hcs2.1]
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
  iapply (wp_epilogue4s1 cpu k hsie 0x80001902#64 (by omega) _ hR2 (k.regs 1#5) (k.regs 8#5) (k.regs 9#5))
    $$ [- $Hk $Hpc]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc
  iapply HΦ $$ %_ Hk Hpc
  ipureintro
  obtain ⟨c4_2, c4_8, c4_9, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27⟩ := hcs4
  obtain ⟨c2_2, c2_8, c2_9, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩ := hcs2
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at c4_9 c4_18 c4_19 c4_20 c4_21 c4_22 c4_23 c4_24 c4_25 c4_26 c4_27
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at c2_18 c2_19 c2_20 c2_21 c2_22 c2_23 c2_24 c2_25 c2_26 c2_27
  constructor
  · unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
    exact ⟨c4_18.trans c2_18, c4_19.trans c2_19, c4_20.trans c2_20, c4_21.trans c2_21, c4_22.trans c2_22,
      c4_23.trans c2_23, c4_24.trans c2_24, c4_25.trans c2_25, c4_26.trans c2_26, c4_27.trans c2_27⟩
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
    exact c4_9⟩

end Xv6
