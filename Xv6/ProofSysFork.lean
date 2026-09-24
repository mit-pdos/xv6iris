/-
Proof of `sys_fork`'s specification (`SpecSysFork.SYSFORK`), given the
interface of `kfork` (Rocq `ProofSysFork.v`).

    uint64 sys_fork(void) { return kfork(); }

    2a1c: addi sp,-16; sd ra,8(sp); sd s0,0(sp); addi s0,sp,16   -- wp_prologue2_gen
    2a24: jal kfork
    2a28: ld ra,8(sp); ld s0,0(sp); addi sp,16; ret              -- wp_epilogue2_gen

As in Rocq, this is `sys_getpid`'s proof (`Xv6/ProofSysGetpid.lean`) with
the `c.lw` deleted and `myproc` replaced by `kfork`; every premise is
forwarded to `kfork` untouched.  `kfork` may sleep (`wpNext true`), so from
its return on the hart is arbitrary (`cf`), and the spec's own `wpNext true`
post is reached with `wpNext_at`, as in `Xv6/ProofSysWait.lean`.  The
save/restore of ra/s0 spans the call, so `calleeSaved` is discharged
componentwise (Rocq's `cs_through` shape).
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecSysFork
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Addresses -/

/-- `jal ra,kfork` at `+0x08`. -/
theorem sys_fork_br_kfork : KA.«sys_fork» + 0xfffffffffffff310#64 = KA.«kfork» := by decide

/-- The link register of the call. -/
theorem sys_fork_ret_0c : jumpPc (KA.«sys_fork» + 0xc#64) = KA.«sys_fork» + 0xc#64 := by decide

theorem sys_fork_pushed_withSpie (k : KCtx) (m : Nat) (a b : Bool) :
    (k.pushed m).withSpie a b = (k.withSpie a b).pushed m := rfl
theorem sys_fork_withRegs_withSpie (k : KCtx) (R : RegMap) (a b : Bool) :
    (k.withRegs R).withSpie a b = (k.withSpie a b).withRegs R := rfl

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

/-- `kfork`'s contract at its entry address. -/
theorem sys_fork_kfork (KF : KFORK) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (c : CPU) (k' : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : kforkSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt) :
    kctx c k' ∗ pcIs c KA.«kfork» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c k'.proc ∗ intrRes c ∗
    isLock γw waitLockAddr "wait_lock" waitLockPay ∗
    isLock γp pidLockAddr "nextpid" pidLockPay ∗
    isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
    procPrivNoctxAt curCtx (procAddr j) pid V M ∗
    wpNext true k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
      ⌜calleeSaved k'.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' k'.proc -∗ intrRes cpu' -∗
      procPrivNoctxAt curCtx (procAddr j) pid V M -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := KF.wp_kfork (hlc := hlc) (GF := GF) Γ c k' γw γp γl γk j pid V M
    hj hproc hK hsie hnoff hlocks htier
  unfold wp_kfork_body at h
  simp only [kforkAddr] at h
  exact h

end

/-! ## The function -/

set_option maxHeartbeats 8000000 in
theorem sys_fork_proof (KF : KFORK) : SYSFORK :=
  ⟨fun {hlc GF} _ _ _ Γ _ _ _ cpu k γw γp γl γk j pid V M hj hproc hK hsie hnoff hlocks htier => by
  unfold wp_sys_fork_body
  simp only [sysForkAddr]
  iintro ⟨Hk, Hpc, #Hpi, Htc, Hcl, Hir, #Hwl, #Hpl, #Hkl, Hav, Hpav, Hblk, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  have hK2 : 2 ≤ k.avail := by unfold sysForkSlots at hK; omega
  -- the prologue
  iapply (wp_prologue2_gen cpu k KA.«sys_fork» hK2)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %c1 %hp1 Hk Hpc Hframe
  -- jal kfork
  k_step_gen (wp_s_jal c1 _ (KA.«sys_fork» + 0x8#64) false 2093832#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [sys_fork_br_kfork] next c2 hp2
  iintro Hk Hpc
  have hc2 : c2 = cpu := (hp2 (Or.inl hsie)).trans (hp1 (Or.inl hsie))
  subst c2
  iapply (sys_fork_kfork KF Γ cpu _ γw γp γl γk j pid V M hj ?hpr ?hKf ?hs ?hn ?hl ?ht)
    $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm_g [sys_fork_ret_0c]
  iframe Hpi Htc Hcl Hir Hwl Hpl Hkl Hav Hpav Hblk
  case hpr => k_norm_g; exact hproc
  case hKf => k_norm_g; unfold sysForkSlots at hK; omega
  case hs => k_norm_g; exact hsie
  case hn => k_norm_g; exact hnoff
  case hl => k_norm_g; exact hlocks
  case ht => k_norm_g; exact htier
  -- past kfork, on some hart `cf`: the epilogue
  iapply wpNext_intro_pin
  iintro %cf %hpf %spie %spp %R1 %rv %hfacts Hk Hpc Htc Hcl Hir Hblk
  obtain ⟨hcs1, h10, hans⟩ := hfacts
  k_norm_g [sys_fork_ret_0c, sys_fork_pushed_withSpie, sys_fork_withRegs_withSpie]
  unfold calleeSaved at hcs1
  k_norm_g at hcs1
  obtain ⟨f2, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27⟩ := hcs1
  iapply (wp_epilogue2_gen cf (k.withSpie spie spp) (KA.«sys_fork» + 0xc#64)
      (by simp only [KCtx.withSpie_avail]; exact hK2) R1
      (by simp only [KCtx.withSpie_regs]; exact f2)
      (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
  rotate_right 1
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %cz %hpz Hk Hpc
  have hcz : cz = cf := hpz (Or.inl hsie)
  subst cz
  ihave Hnext := wpNext_at true k.proc cpu cf _
    (fun h => h.elim (fun h => absurd h (by decide))
      (fun h => absurd h (by rw [hproc]; exact procAddr_nonzero hj))) $$ Hnext
  k_norm_g
  iapply Hnext $$ %spie %spp %_ %rv [] Hk Hpc Htc Hcl Hir Hblk
  ipureintro
  refine ⟨?_, ?_, hans⟩
  · unfold calleeSaved
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
    exact ⟨trivial, trivial, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27⟩
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    exact h10⟩

end Xv6
