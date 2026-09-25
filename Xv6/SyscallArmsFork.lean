/-
**syscall()'s FORK ARM** (wave 8 W8-S1; Rocq `ProofSyscall.v`
`sysc_arm_fork`): table index 1, `SYSFORK.wp_sys_fork_eb` (kfork's balanced
contract, crossing `k.sie`) from the dispatch's rows, per the frozen recipe
(notes/coord/syscall_arms_interfaces.txt §2, §5 S1 fork).

* The environment: `wait_lock` is the dispatch's `γw`; `nextpid` and the
  ledger (`syscallEnv_pid`), the allocator (`syscallEnv_kmem`), the file
  table (`syscallEnv_ftable`), the inode table rows (`fsReady_icache` /
  `fsReady_region`) and `firstDone` (`syscallEnv_first`).
* The payload: `Q := UexecSG.sforkPay f`, and the kill wand out of fork's
  deposit slot `syscForkIn` (guarded by the number).
* The answer: `syscForkOut` from kfork's `kforkRet` -- the lend
  `sforkLend f` refunded on `-1` (`uforkAns`'s left arm), dropped on success
  beside the parent's `childTok` at a FRESH generation.

## Deviations from Rocq (flagged)

1. **`[ForkretIs]` is an instance argument of the arm** (SpecSysFork's
   assumed class; W8-P2's `ParkCap.park_token` retires it).  It is NOT a
   field of `SYSCALL`: the seal (W8-E2) will carry it until W8-P2 lands.
2. **PROCESS LAYER: `syscForkIn`'s child-slot wand is DROPPED** (SpecSyscall
   deviation 7): Lean's kfork threads no `uslot` / `Rc` / `park_token`, so
   the child's slot and the lend it would carry have no taker.  The lend
   stays with the parent and is refunded (failure) or dropped (success).
-/
import Xv6.SyscallRet

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- kfork's answer, sign-extended, is `-1` or a pid in `[1, PIDMAX]` read as
an `int` (the `fork` row of `SyscRows`). -/
theorem syscArmFork_ans (rv : BitVec 32) (h : kforkAns rv) :
    BitVec.signExtend 64 rv = -1#64 ∨
      (1 ≤ (BitVec.signExtend 64 rv).toInt ∧ (BitVec.signExtend 64 rv).toInt ≤ PIDMAX) := by
  rcases h with h | ⟨h1, h2⟩
  · left; subst h; decide
  · right
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    have hP : PIDMAX = 1000 := rfl
    rw [BitVec.toInt_eq_toNat_cond]
    have : 2 * rv.toNat < 2 ^ 32 := by omega
    simp only [this, if_true]
    omega

/-- **The rows of fork's arm** (Rocq `sysc_arm_fork`'s premises of
`sysc_ret_tail`): the block back at the entry record with only `a0`
stored, the children set moved (fork's own row), and fork's answer. -/
theorem syscRows_fork (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (cs cs' : ExtTreeSet GName compare) (pid : BitVec 32) (r : BitVec 64)
    (hnum : syscNum V = 1) (hl : tfArgIdx 0 < V.tf.length)
    (hans : r = -1#64 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ PIDMAX)) :
    SyscRows V M (syscStore V r) M sts sts cs cs' pid := by
  have hn : ∀ m : Int, (1 : Int) ≠ m → syscNum V ≠ m := fun m h => by rw [hnum]; exact h
  have ha0 := syscStore_a0 V r hl
  refine ⟨?_, ?_, ?_, fun h _ => absurd hnum h, hn 2 (by decide), Or.inr ⟨r, rfl⟩,
    Or.inr (Or.inr (UMemL.extSz_refl _ _)), Or.inr (Or.inr rfl), Or.inr (Or.inr rfl), rfl, rfl, rfl,
    rfl, Or.inr rfl, Or.inl (hn 12 (by decide)), Or.inr (by rw [ha0]; exact hans),
    Or.inl (hn 5 (by decide)), syscRetPid_ne _ _ _ 1 hnum (by decide), rfl⟩
  · unfold syscMemOk
    rw [if_neg (hn USYS_exec (by decide)), if_neg (hn USYS_sbrk (by decide)),
      if_neg (hn USYS_wait (by decide)), if_neg (hn USYS_pipe (by decide)),
      if_neg (hn USYS_read (by decide)), if_neg (hn USYS_fstat (by decide))]
    rfl
  · exact syscFdOk_refl_at V _ sts 1 hnum (by decide) (by decide) (by decide) (by decide)
  · exact syscPipeOk_quiet V _ _ _ sts sts (hn 4 (by decide))

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
  [Appcfg GF] [FileG GF] [SG : UexecSG GF] [Fscfg] [Icfg] [CurCtx]

/-- **Fork's answer to the channel** (Rocq `sysc_fork_out` from `kfork_post`):
the lend refunded on `-1`, the parent's token at a fresh generation on
success. -/
theorem syscArmFork_out (f : UexecSG.sfam GF) (V : ProcPriv) (j : Nat)
    (cs cs' : ExtTreeSet GName compare) (rv : BitVec 32) :
    (⌜rv = -1#32 ∧ cs' = cs⌝ ∗ UexecSG.sforkLend f) ∨
      (UexecSG.sforkLend f ∗ ∃ γc : GName, ⌜1 ≤ rv.toNat ∧ rv.toNat ≤ PIDMAX⌝ ∗ ⌜γc ∉ cs⌝ ∗
        ⌜cs' = cs ∪ {γc}⌝ ∗ childTok γc rv (UexecSG.sforkPay f)) ⊢
      syscForkOut f V (BitVec.signExtend 64 rv) cs cs' := by
  unfold syscForkOut uforkAns
  iintro H %_
  icases H with (⟨%h, Hl⟩ | ⟨-, %γc, %hr, %hf, %hcs, Ht⟩)
  · ileft
    iframe Hl
    ipureintro
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact ⟨by decide, h2⟩
  · iright
    iexists γc, rv
    iframe Ht
    ipureintro
    exact ⟨rfl, hr, hf, hcs⟩

set_option maxHeartbeats 4000000 in
/-- **Arm 1, `sys_fork`** (Rocq `sysc_arm_fork`).  Deviations 1-2 of the
header (flagged). -/
theorem syscall_arm_fork (SF : SYSFORK) [ForkretIs]
    (PT : SchedNames → IProp GF) [hPT : ∀ Γ, Persistent (PT Γ)] (Γ : SchedNames)
    [ClaimIs (hlc := hlc) GF Γ]
    (c0 cpu : CPU) (k : KCtx) (spie spp : Bool) (R : RegMap) (γw : GName) (γ : FileNames) (j : Nat)
    (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState) (gn : GName)
    (cs : ExtTreeSet GName compare) (ip : BitVec 64) (f : UexecSG.sfam GF)
    (hE : SyscSpostEmp (GF := GF))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : syscallSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) (hgn : gn = V.gen)
    (hnum : syscNum V = ((1 : Nat) : Int)) (hpins : syscPins k R) (hs1 : R 9#5 = procAddr j)
    (hs2 : R 18#5 = pageAddr V.upt.tfp) (hra : R 1#5 = syscallRet) :
    syscArmBody 1 PT Γ c0 cpu k spie spp R γw γ j pid V M sts gn cs ip f hE hj hproc hK hnoff htier hgn
      hnum hpins hs1 hs2 hra := by
  unfold syscArmBody
  iintro ⟨Hk, Hpc, Hframe, #Hpi, Hte, Hce, #Hwl, Hbs, Hip, Hfd, Hir, #Henv, Hpriv, Hfr, Hch, -, HfIn, -,
    Hslot⟩
  icases Hslot with ⟨Hnext, -⟩
  icases kctx_tier _ _ $$ Hk with ⟨%hti, Hk⟩
  have hww : ∀ (K : KCtx) (a b c d : Bool), (K.withSpie a b).withSpie c d = K.withSpie c d :=
    fun _ _ _ _ _ => rfl
  have hpsw : ∀ (K : KCtx) (m : Nat) (a b : Bool),
      (K.pushed m).withSpie a b = (K.withSpie a b).pushed m := fun _ _ _ _ => rfl
  have hn1 : syscNum V = (1 : Int) := hnum
  have hct : curTier = KTier.kpt := by rw [← hti]; exact htier
  have hprocK : (((k.withSpie spie spp).pushed 4).withRegs R).proc = procAddr j := hproc
  have hnoffK : (((k.withSpie spie spp).pushed 4).withRegs R).noff = 0 := hnoff
  icases syscall_tf_len hct γ (procAddr j) pid V M $$ Hpriv with ⟨%hl, Hpriv⟩
  -- the environment
  icases syscallEnv_pid PT Γ γ $$ Henv with ⟨⟨%γp, #Hnp⟩, #Hpav⟩
  icases syscallEnv_kmem PT Γ γ $$ Henv with ⟨#Hkl, #Hka⟩
  icases syscallEnv_ftable PT Γ γ $$ Henv with ⟨%γft, #Hft⟩
  ihave #Hrdy := syscallEnv_fsReady PT Γ γ $$ Henv
  icases fsReady_icache $$ Hrdy with ⟨#Hit2, #Hiti, -⟩
  icases fsReady_region $$ Hrdy with ⟨#Hreg, -⟩
  ihave #Hdone := syscallEnv_first PT Γ γ $$ Henv
  -- fork's deposit: the kill wand and the lend (the child's slot has no taker, deviation 2)
  unfold syscForkIn
  icases HfIn $$ %hn1 with ⟨#Hkw, Hlend, -⟩
  have hU := SF.wp_sys_fork_eb (hlc := hlc) (GF := GF) Γ cpu
    (((k.withSpie spie spp).pushed 4).withRegs R) γw γp fscKalloc fsReadyKmem γft γ j pid V M sts
    (UexecSG.sforkPay f) cs hj hprocK
    (by k_norm_g; have : sysForkSlots + 4 ≤ syscallSlots := by decide
        omega)
    hnoffK (by k_norm_g; exact htier)
  unfold wp_sys_fork_eb_body at hU
  rw [syscTarget_fork]
  iapply hU
  iframe Hk Hpi Hwl Hnp Hkl Hka Hpav Hft Hit2 Hiti Hreg Hkw Hdone Hpriv Hfr Hch Hpc
  k_next_e
  unfold kforkPost kforkPostB kforkRet
  iintro %spie2 %spp2 %R2 %rv %⟨hcs, ha0, hans⟩ Hk Hpc ⟨Hpriv, Hfr, Hret⟩
  k_norm_g [hra, syscallRet_jumpPc, hww, hpsw]
  k_norm_g at hcs
  have hpins2 := syscPins_calleeSaved k R R2 hpins hcs
  have hs2' : R2 18#5 = pageAddr V.upt.tfp := hcs.2.2.2.1.trans hs2
  -- the children set the post is keyed at, and fork's answer
  icases Hret with (⟨%hrv, Hch⟩ | ⟨%γc, %hr, %hf, Htok, Hch⟩)
  · have hrows := syscRows_fork V M sts cs cs pid (R2 10#5) hn1 (by rw [hl]; decide)
      (by rw [ha0]; exact syscArmFork_ans rv hans)
    unfold syscallRet syscallAddr at *
    iapply (syscall_ret_tail PT Γ c0 cpu k spie2 spp2 R2 γ j pid V M sts gn cs ip f V M sts cs hj hproc
      hK htier hpins2 hs2' hrows)
    iframe Hk Hpc Hframe Hte Hce Hbs Hip Hfd Hir Henv Hpriv Hfr Hch Hnext
    isplitr
    · iapply syscExecOut_ne; rw [hn1]; decide
    isplitr
    · iapply syscSysOut_fork f V M sts gn cs pid _ _ sts _ cs hn1
    isplitl [Hlend]
    · rw [syscStore_a0 V _ (by rw [hl]; decide), ha0]
      iapply syscArmFork_out f V j cs cs rv
      ileft
      iframe Hlend
      ipureintro; exact ⟨hrv, rfl⟩
    · iapply syscWaitOut_ne; rw [hn1]; decide
  · have hrows := syscRows_fork V M sts cs (cs ∪ {γc}) pid (R2 10#5) hn1 (by rw [hl]; decide)
      (by rw [ha0]; exact syscArmFork_ans rv hans)
    unfold syscallRet syscallAddr at *
    iapply (syscall_ret_tail PT Γ c0 cpu k spie2 spp2 R2 γ j pid V M sts gn cs ip f V M sts
      (cs ∪ {γc}) hj hproc hK htier hpins2 hs2' hrows)
    iframe Hk Hpc Hframe Hte Hce Hbs Hip Hfd Hir Henv Hpriv Hfr Hch Hnext
    isplitr
    · iapply syscExecOut_ne; rw [hn1]; decide
    isplitr
    · iapply syscSysOut_fork f V M sts gn cs pid _ _ sts _ _ hn1
    isplitl [Hlend Htok]
    · rw [syscStore_a0 V _ (by rw [hl]; decide), ha0]
      iapply syscArmFork_out f V j cs (cs ∪ {γc}) rv
      iright
      iframe Hlend
      iexists γc
      iframe Htok
      ipureintro; exact ⟨hr, hf, rfl⟩
    · iapply syscWaitOut_ne; rw [hn1]; decide

end

end Xv6
