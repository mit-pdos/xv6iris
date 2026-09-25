/-
**syscall()'s WAIT ARM** (wave 8 W8-S1; Rocq `ProofSyscall.v`
`sysc_arm_wait`): table index 3, `SYSWAIT.wp_sys_wait_eb` (kwait's
eb-generic contract, crossing `true`: kwait parks on the wait lock) from the
dispatch's rows, per the frozen recipe (notes/coord/syscall_arms_interfaces.txt).

* The environment: `wait_lock` is the dispatch's `γw`; `nextpid`
  (`syscallEnv_pid`), the allocator at `fsReady`'s names (`syscallEnv_kmem`),
  init's pid (`syscInitId_pidIs`).
* The rows: the image row is wait's window -- copyout's `umemWrite` over the
  faulted view, at the pages `umMapped` names, is `usysWr` of the lazy image
  (`SyscallTable.syscImg_write` + `syscImg_faulted`; the no-wrap bound from
  `umMapped_bound` at the returned table's `uptWf`); the table row is the
  post's `extSz`; the children set moves (wait's own row).
* The answer: `syscWaitOut` via `syscWaitOut_of` from kwait's `waitAns` and
  the window (`syscUwaitWr`, Rocq `uwait_wr`) from `kwaitAns`'s two guards.
-/
import Xv6.SyscallRet
import Xv6.SyscallArmsSbrk

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The copyout's window at the lazy image** (Rocq `uwait_wr`'s image
equation): kwait's `umemWrite` over the faulted view is `usysWr` of the
entry's lazy image. -/
theorem syscArmWait_img (P P' : UPtd) (sz : BitVec 64) (M : Nat → List (BitVec 8)) (v : BitVec 64)
    (bs : List (BitVec 8)) (hext : P.extSz sz P') (hmap : umMapped P' v.toNat bs.length)
    (hlen : umPageLen P' (umemWrite (viewFaulted P P' M) v.toNat bs)) (hwf : uptWf P') :
    umemLazy P' sz.toNat (umemWrite (viewFaulted P P' M) v.toNat bs) =
      usysWr (umemLazy P sz.toNat M) v bs := by
  have hlen' : umPageLen P' (viewFaulted P P' M) := fun k w h => by
    rw [← UMemL.umemWrite_length _ v.toNat bs k]; exact hlen k w h
  have hnw : v.toNat + bs.length ≤ 2 ^ 64 := by
    by_cases h0 : bs.length = 0
    · have := v.isLt; omega
    · have := UMemL.umMapped_bound hwf hmap (by omega)
      have hm : uvmMaxsz < 2 ^ 64 := by decide
      omega
  rw [syscImg_write P' sz.toNat _ v bs hmap hlen' hnw, syscImg_faulted P P' sz M hext]

/-- **The rows of wait's arm** (Rocq `sysc_arm_wait`'s premises of
`sysc_ret_tail`). -/
theorem syscRows_wait (V : ProcPriv) (M M2 : Nat → List (BitVec 8)) (P' : UPtd) (sts : List FdState)
    (cs cs' : ExtTreeSet GName compare) (pid : BitVec 32) (r : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) (ha : tfW V.tf (tfArgIdx 0) = a)
    (hnum : syscNum V = 3) (hext : V.upt.extSz V.sz P') (hbs : bs.length ≤ 4)
    (hz : a = 0#64 → bs = [])
    (himg : syscImg { V with upt := P' } M2 = usysWr (syscImg V M) a bs) :
    SyscRows V M (syscStore { V with upt := P' } r) M2 sts sts cs cs' pid := by
  have hn : ∀ m : Int, (3 : Int) ≠ m → syscNum V ≠ m := fun m h => by rw [hnum]; exact h
  refine ⟨?_, ?_, syscPipeOk_quiet V _ _ _ sts sts (hn 4 (by decide)),
    fun _ h => absurd hnum h, hn 2 (by decide), Or.inr ⟨r, rfl⟩, Or.inr (Or.inr hext),
    Or.inr (Or.inr rfl), Or.inr (Or.inr rfl), hext.1.2.1, rfl, rfl, rfl, Or.inr rfl,
    Or.inl (hn 12 (by decide)), Or.inl (hn 1 (by decide)), Or.inl (hn 5 (by decide)),
    syscRetPid_ne _ _ _ 3 hnum (by decide), rfl⟩
  · unfold syscMemOk
    rw [if_neg (hn USYS_exec (by decide)), if_neg (hn USYS_sbrk (by decide)),
      if_pos (show syscNum V = USYS_wait from hnum)]
    subst ha
    exact ⟨bs, hbs, hz, himg⟩
  · exact syscFdOk_refl_at V _ sts 3 hnum (by decide) (by decide) (by decide) (by decide)

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
  [Appcfg GF] [FileG GF] [SG : UexecSG GF] [Fscfg] [Icfg] [CurCtx]

set_option maxHeartbeats 4000000 in
/-- **Arm 3, `sys_wait`** (Rocq `sysc_arm_wait`). -/
theorem syscall_arm_wait (SW : SYSWAIT)
    (PT : SchedNames → IProp GF) [hPT : ∀ Γ, Persistent (PT Γ)] (Γ : SchedNames)
    [ClaimIs (hlc := hlc) GF Γ]
    (c0 cpu : CPU) (k : KCtx) (spie spp : Bool) (R : RegMap) (γw : GName) (γ : FileNames) (j : Nat)
    (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState) (gn : GName)
    (cs : ExtTreeSet GName compare) (ip : BitVec 64) (f : UexecSG.sfam GF)
    (hE : SyscSpostEmp (GF := GF))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : syscallSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) (hgn : gn = V.gen)
    (hnum : syscNum V = ((3 : Nat) : Int)) (hpins : syscPins k R) (hs1 : R 9#5 = procAddr j)
    (hs2 : R 18#5 = pageAddr V.upt.tfp) (hra : R 1#5 = syscallRet) :
    syscArmBody 3 PT Γ c0 cpu k spie spp R γw γ j pid V M sts gn cs ip f hE hj hproc hK hnoff htier hgn
      hnum hpins hs1 hs2 hra := by
  unfold syscArmBody
  iintro ⟨Hk, Hpc, Hframe, #Hpi, Hte, Hce, #Hwl, Hbs, #Hip, Hfd, Hir, #Henv, Hpriv, Hfr, Hch, -, -, -,
    Hslot⟩
  icases Hslot with ⟨Hnext, -⟩
  icases kctx_tier _ _ $$ Hk with ⟨%hti, Hk⟩
  have hww : ∀ (K : KCtx) (a b c d : Bool), (K.withSpie a b).withSpie c d = K.withSpie c d :=
    fun _ _ _ _ _ => rfl
  have hpsw : ∀ (K : KCtx) (m : Nat) (a b : Bool),
      (K.pushed m).withSpie a b = (K.withSpie a b).pushed m := fun _ _ _ _ => rfl
  have hn3 : syscNum V = (3 : Int) := hnum
  have hct : curTier = KTier.kpt := by rw [← hti]; exact htier
  have hprocK : (((k.withSpie spie spp).pushed 4).withRegs R).proc = procAddr j := hproc
  have hnoffK : (((k.withSpie spie spp).pushed 4).withRegs R).noff = 0 := hnoff
  icases syscall_tf_len hct γ (procAddr j) pid V M $$ Hpriv with ⟨%hl, Hpriv⟩
  obtain ⟨v, hv⟩ : ∃ v, V.tf[tfArgIdx 0]? = some v :=
    ⟨_, List.getElem?_eq_getElem (by rw [hl]; decide)⟩
  have hw0 : tfW V.tf (tfArgIdx 0) = v := by unfold tfW; rw [List.getD_eq_getElem?_getD, hv]; rfl
  -- the environment
  icases syscallEnv_pid PT Γ γ $$ Henv with ⟨⟨%γp, #Hnp⟩, -⟩
  icases syscallEnv_kmem PT Γ γ $$ Henv with ⟨#Hkl, #Hka⟩
  ihave #Hinit := syscInitId_pidIs ip $$ Hip
  have hU := SW.wp_sys_wait_eb (hlc := hlc) (GF := GF) Γ cpu
    (((k.withSpie spie spp).pushed 4).withRegs R) γw γp fscKalloc fsReadyKmem γ j pid V M v cs hj hprocK hv
    (by k_norm_g; have : sysWaitSlots + 4 ≤ syscallSlots := by decide
        omega)
    hnoffK (by k_norm_g; exact htier)
  unfold wp_sys_wait_eb_body at hU
  have hsie : (((k.withSpie spie spp).pushed 4).withRegs R).sie = k.sie := rfl
  have hpr : (((k.withSpie spie spp).pushed 4).withRegs R).proc = k.proc := rfl
  rw [hsie, hpr] at hU
  rw [syscTarget_wait]
  iapply hU
  iframe Hk Hpi Hte Hce Hwl Hnp Hkl Hka Hpriv Hch Hinit Hpc
  iapply wpNext_intro_pin
  iintro %cpu %-
  iintro %spie2 %spp2 %R2 %P' %rv %xw %d %cs' %⟨hcs, ha0, hext, hd, hans, hmap⟩ Hwa Hch Hk Hpc Hte Hce
    Hpriv
  -- the returned block's page facts
  icases procPrivFd_facts γ (procAddr j) pid _ _ $$ Hpriv with ⟨Hpriv, %⟨-, -, -, hwf⟩⟩
  icases sbrkArm_pageLen γ (procAddr j) pid _ _ $$ Hpriv with ⟨Hpriv, %hlen⟩
  k_norm_g [hra, syscallRet_jumpPc, hww, hpsw]
  k_norm_g at hcs
  have hpins2 := syscPins_calleeSaved k R R2 hpins hcs
  have hs2' : R2 18#5 = pageAddr ({ V with upt := P' } : ProcPriv).upt.tfp := by
    rw [show ({ V with upt := P' } : ProcPriv).upt.tfp = V.upt.tfp from hext.1.2.1]
    exact hcs.2.2.2.1.trans hs2
  have hbl : ((xstateBytes xw).take d).length = d := by simp; omega
  have himg := syscArmWait_img V.upt P' V.sz M v ((xstateBytes xw).take d) hext (by rw [hbl]; exact hmap)
    hlen hwf
  have hz : v = 0#64 → (xstateBytes xw).take d = [] := by
    intro h0
    have : d = 0 := hans.1 h0
    subst this; rfl
  have hrows := syscRows_wait V M _ P' sts cs cs' pid (R2 10#5) ((xstateBytes xw).take d) v hw0 hn3 hext
    (by rw [hbl]; exact hd) hz himg
  have hsa0 : syscA0 (syscStore { V with upt := P' } (R2 10#5)) = R2 10#5 :=
    syscStore_a0 _ _ (by show tfArgIdx 0 < V.tf.length; rw [hl]; decide)
  unfold syscallRet syscallAddr at *
  iapply (syscall_ret_tail PT Γ c0 cpu k spie2 spp2 R2 γ j pid V M sts gn cs ip f { V with upt := P' } _
    sts cs' hj hproc hK htier hpins2 hs2' hrows)
  iframe Hk Hpc Hframe Hte Hce Hbs Hip Hfd Hir Henv Hpriv Hfr Hch Hnext
  isplitr
  · iapply syscExecOut_ne; rw [hn3]; decide
  isplitr
  · iapply syscSysOut_quiet f V M sts hE gn cs pid _ _ sts _ cs' 3 hn3 (by decide)
  isplitr
  · iapply syscForkOut_ne; rw [hn3]; decide
  rw [hsa0]
  iapply syscWaitOut_of V M _ (R2 10#5) rv xw cs cs' pid ha0 ?hwr
  case hwr =>
    rw [hw0]
    refine ⟨d, hd, fun h0 => hans.1 h0, fun h0 hr => ?_, himg⟩
    refine hans.2 h0 (fun hrv => hr ?_)
    rw [ha0, hrv]; decide
  rw [hw0]
  iexact Hwa

end

end Xv6
