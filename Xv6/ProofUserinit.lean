/-
Proof of `userinit`'s specification (`SpecUserinit.USERINIT`), given the
interfaces of `allocproc` and `release` (and the boot `namei` arm of the
file-system boundary).

The C body (kernel/proc.c):

    void userinit(void) {
      struct proc *p = allocproc();
      initproc = p;
      p->cwd = namei("/");
      p->state = RUNNABLE;
      release(&p->lock);
    }

BOOT code: `k.proc = 0`, `k.noff = 0`, `k.locks = []`, `k.sie = false`.
`allocproc` returns the found slot USED and held; `userinit` publishes
`initproc` (the owned word, discarded to the persistent `initprocIs`),
writes `namei`'s result into `p->cwd`, sets the slot RUNNABLE, mints the
newborn's parked record (`forkret_record`) and releases `p->lock`, leaving
the slot RUNNABLE inside `procsInv`.

REFUTING `allocproc`'s failure arm.  The `r = 0` arm reports both reasons
it can fire: no free slot (`pav = none ∨ pav = some 0`, refuted by the
counted regime `procsAvail Γ (some (np + 1))`) and an empty page allocator
(`availZero (availSub (some nb) g)` for some `g ≤ procPagetableNodes + 1`,
refuted by `hnb : procPagetableNodes + 1 < nb`).  Both are PURE, so the arm
dies on its `⌜..⌝` alone.

`namei("/")` runs while `p->lock` is HELD; the contract used is the
non-blocking one, `FsEnv.nameiBoot : FsEntryNB nameiAddr`, which is generic
in `k.locks`/`k.noff`.
-/
import MachCSL.WpSmodeFrame
import MachCSL.ByteWord
import MachCSL.Lock
import Xv6.SpecUserinit
import Xv6.SpecAllocproc
import Xv6.SpecRelease
import Xv6.ForkretRecord
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Publishing a word: `own 1 → discard`

`initproc` is written once and then read forever after: `userinit` stores
`p` into the owned cell and hands it back DISCARDED, as the persistent
`initprocIs`.  There is no discard/persist lemma on `wordPointsTo` in
`MachCSL`, so we build one here from `pointsTo_persist`. -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A single byte cell is publishable. -/
theorem ctxByte_persist (ξ : CtxId) (a : PAddr) (dq : DFrac) (v : BitVec 8) :
    ctxByte (GF := GF) ξ a dq v ⊢ |==> ctxByte ξ a DFrac.discard v := by
  unfold ctxByte
  iintro ⟨%e, %H, Hpt, %hv, #Hkey⟩
  imod (pointsTo_persist (l := a) (dq := dq) (v := (e :: H))) $$ Hpt with #Hpt
  imodintro
  iexists e, H
  iframe Hpt Hkey
  ipureintro; exact hv

/-- The `n` bytes at `pa` are publishable. -/
theorem ctxBytes_persist (ξ : CtxId) (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    ctxBytes (GF := GF) ξ pa n dq w ⊢ |==> ctxBytes ξ pa n DFrac.discard w := by
  unfold ctxBytes
  iintro H
  ihave H' := BigSepL.bigSepL_mono
    (fun {_ j} _ => ctxByte_persist ξ (pa + BitVec.ofNat 64 j) dq (nthByte w j)) $$ H
  iapply BigSepL.bigSepL_bupd $$ H'

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- **A word is publishable**: give up the fraction, keep the value forever. -/
theorem wordPointsTo_persist (va : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordPointsTo (GF := GF) va n dq w ⊢ |==> wordPointsTo va n DFrac.discard w := by
  unfold wordPointsTo
  iintro ⟨%ppn, #Hcl, %hfacts, Hb⟩
  imod (ctxBytes_persist curCtx (paOf ppn va) n dq w) $$ Hb with Hb
  imodintro
  iexists ppn
  iframe Hb Hcl
  ipureintro; exact hfacts

/-- **Publish `initproc`**: the owned word becomes the persistent
`initprocIs`. -/
theorem initprocIs_publish (ip : BitVec 64) :
    wordPointsTo (GF := GF) initprocAddr 8 (DFrac.own 1) ip ⊢ |==> initprocIs ip := by
  unfold initprocIs
  exact wordPointsTo_persist initprocAddr 8 (DFrac.own 1) ip

end

/-! ## Address folds and small facts -/

/-- `&initproc` from `auipc a5,0x8 ; sd a0,1680(a5)` at `0x80001c9e`. -/
theorem ui_initproc_addr :
    KA.«userinit» + 0x86b2#64
      = initprocAddr := by decide

/-- The link registers of the three calls. -/
theorem ui_ret_bee : jumpPc (KA.«userinit» + 0xe#64) = (KA.«userinit» + 0xe#64) := by decide
theorem ui_ret_c04 : jumpPc (KA.«userinit» + 0x24#64) = (KA.«userinit» + 0x24#64) := by decide
theorem ui_ret_c12 : jumpPc (KA.«userinit» + 0x32#64) = (KA.«userinit» + 0x32#64) := by decide

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-! ## The private block, opened at `p->cwd` -/

/-- `p->cwd` comes out of the private block and goes back with a new value. -/
theorem ui_priv_cwd_acc [CurCtx] (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) :
    procPriv (GF := GF) pa pid V M ⊢
      wordPointsTo (pCwd pa) 8 (DFrac.own 1) V.cwd ∗
      (∀ w : BitVec 64, wordPointsTo (pCwd pa) 8 (DFrac.own 1) w -∗
        procPriv pa pid { V with cwd := w } M) := by
  unfold procPriv procFields
  iintro ⟨%hV, Hpid, ⟨Hks, Hsz, Hpg, Htf, Hctx, Hof, Hcwd, Hnm⟩, Hpt, Htfp⟩
  iframe Hcwd
  iintro %w Hcwd
  isplitl []
  · ipureintro; exact hV
  iframe Hpid Hks Hsz Hpg Htf Hctx Hof Hcwd Hnm Hpt Htfp

/-! ## The slot a newborn's release deposits -/

/-- The RUNNABLE arms: the parked record, the hart tag, the marker.
`parkOk RUNNABLE`, and `parkPayAt` is empty at a live state. -/
theorem ui_slots_runnable [CurCtx] (Γ : SchedNames) (ξl : CtxId) (pa : BitVec 64) :
    slotUsed (GF := GF) Γ pa ∗ procCtxAt Γ ξl pa ∗ hartAtAny Γ pa ⊢
      procSlotsAt Γ ξl pa RUNNABLE := by
  iintro ⟨#Hu, Hc, Hh⟩
  iapply (procSlots_park_gen Γ ξl pa RUNNABLE (by decide))
  rw [if_pos (show needsCtx RUNNABLE from by decide)]
  isplitl []
  · iexact Hu
  isplitl [Hc]
  · iexact Hc
  isplitl [Hh]
  · iexact Hh
  · iapply (parkPay_needsCtx ξl pa RUNNABLE (by decide))

end

/-! ## The callees, at their entry addresses -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

set_option maxHeartbeats 1000000 in
/-- `allocproc`'s contract at `0x80001b8e`. -/
theorem ui_allocproc (AP : ALLOCPROC) (Γ : SchedNames) (c : CPU) (k' : KCtx)
    (γl γp : GName) (γk : KmemNames) (on pav : Option Nat)
    (hnoff : k'.noff + 2 < 2 ^ 31) (hK : allocprocSlots ≤ k'.avail)
    (hlk : "kmem" ∉ k'.locks) (hlp : "nextpid" ∉ k'.locks) (hlq : "proc" ∉ k'.locks)
    (htier : k'.tier = KTier.kpt) :
    kctx c k' ∗ pcIs c KA.«allocproc» ∗ procsInv Γ ∗
    isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ isLock γp pidLockAddr "nextpid" pidLockPay ∗
    kallocAvail γk on ∗ procsAvail Γ pav ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      ((⌜R' 10#5 = 0#64⌝ ∗ kctx cpu' ((k'.withSpie spie spp).withRegs R')) ∨
       (⌜R' 10#5 ≠ 0#64⌝ ∗
         kctx cpu' (((k'.pushOffAt spie spp).withRegs R').withLocks ("proc" :: k'.locks)))) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      allocprocPost Γ cpu' γk on pav (R' 10#5) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := AP.wp_allocproc (hlc := hlc) (GF := GF) Γ c k' γl γp γk on pav hnoff hK hlk hlp hlq htier
  unfold wp_allocproc_body at h
  simp only [allocprocAddr] at h
  iintro ⟨Hk, Hpc, #Hpi, #Hkm, #Hpl, Hav, Hpav, Hnext⟩
  iapply h
  iframe Hk Hpc Hpi Hkm Hpl Hav Hpav
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK %spie %spp %R' %hsp Hd Hpc Hpost %hcs
  -- the success arm's `sieArm` (the acquire's pay) is not needed here
  icases Hd with (⟨%h0, Hk⟩ | ⟨%h1, Hk, _⟩)
  · iapply HK $$ %spie %spp %R' %hsp [Hk] Hpc Hpost %hcs
    ileft; iframe Hk; ipureintro; exact h0
  · iapply HK $$ %spie %spp %R' %hsp [Hk] Hpc Hpost %hcs
    iright; iframe Hk; ipureintro; exact h1

set_option maxHeartbeats 1000000 in
/-- A non-blocking fs call at `pcnum` (here `namei` at boot). -/
theorem ui_nbcall (entry pcnum : BitVec 64) (heq : entry = pcnum) (FD : FsEntryNB entry)
    (Γ : SchedNames) (c : CPU) (kk : KCtx)
    (hK : fsSlots ≤ kk.avail) (hnoff : kk.noff + 1 < 2 ^ 31) (htier : kk.tier = KTier.kpt) :
    kctx c kk ∗ pcIs c pcnum ∗ procsInv Γ ∗
    wpNext kk.sie kk.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜kk.sie = false → spie = kk.spie ∧ spp = kk.spp⌝ -∗
      kctx cpu' ((kk.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (kk.regs 1#5)) -∗
      ⌜calleeSaved kk.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := FD (hlc := hlc) (GF := GF) Γ c kk hK hnoff htier
  unfold wp_nb_blocking_body at h
  rw [heq] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- `release`'s contract at `0x80000ce0`, for `"proc"` at an explicit address. -/
theorem ui_release (RE : RELEASE) (c : CPU) (k' : KCtx) (γ : GName) (lk : BitVec 64)
    (haddr : k'.regs 10#5 = lk) (Rp : CtxId → IProp GF) [CtxMorph Rp]
    (hsie' : k'.sie = false) (hnoff' : 1 ≤ k'.noff) (hK' : 10 ≤ k'.avail)
    (reen : Bool) (hreen : reen = (decide (k'.noff = 1) && k'.intena))
    (hon : reen = true → k'.tier = .kpt ∧ trapRes true + 6 ≤ k'.avail) :
    kctx c k' ∗ pcIs c KA.«release» ∗ isLock γ lk "proc" Rp ∗ locked γ c ∗ Rp curCtx ∗
    popArm c k' reen ∗
    wpNext (k'.popExit reen).sie k'.proc c (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (((k'.popExit reen).withRegs R').withLocks (k'.locks.filter (fun x => x ≠ "proc"))) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst haddr
  have h := RE.wp_release (hlc := hlc) (GF := GF) c k' γ "proc" Rp hsie' hnoff' hK' reen hreen hon
  unfold wp_release_body at h
  simp only [releaseAddr] at h
  exact h

end

/-- `push_off` from a prologue frame, at interrupts off. -/
theorem ui_pushOffAt_pushed (k : KCtx) (hs : k.sie = false) (m : Nat) (R : RegMap) :
    ((k.pushed m).withRegs R).pushOffAt k.spie k.spp = ((k.pushed m).withRegs R).pushOff :=
  KCtx.pushOffAt_off' _ _ _ hs rfl rfl

/-- `["proc"]` is emptied by the release's filter. -/
theorem ui_filter_one : (["proc"] : List String).filter (fun x => x ≠ "proc") = [] := by
  simp


/-! ## The publish, from `(KernelSyms.«userinit» + 0x24)` -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

set_option maxHeartbeats 2000000 in
/-- **`userinit`'s publish.**  `namei` has returned in `a0`, `s1` is `p`,
`p->lock` is held at depth 1: `p->cwd = a0`, `p->state = RUNNABLE`, the
newborn's parked record, and `release(&p->lock)`. -/
theorem userinit_br_fffffffffffff052 : KA.«userinit» + 0xfffffffffffff052#64 = KA.«release» := by decide

theorem ui_finish [X : CurCtx] (RE : RELEASE) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    [ForkretIs] (cpu : CPU) (kf : KCtx) (j : Nat) (ch : BitVec 64) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hct : curTier = KTier.kpt)
    (hctx : V.context = [forkretAddr, V.kstack + 4096#64] ++ List.replicate 12 0#64)
    (hs1 : kf.regs 9#5 = procAddr j)
    (hsie : kf.sie = false) (hnoff : kf.noff = 1) (hintena : kf.intena = false)
    (hlocks : kf.locks = ["proc"]) (htier : kf.tier = KTier.kpt) (hK : 10 ≤ kf.avail) :
    kctx cpu kf ∗ pcIs cpu (KA.«userinit» + 0x24#64) ∗ procsInv Γ ∗
    procHeld Γ cpu j USED ch ∗ hartAtAny Γ (procAddr j) ∗ slotUsed Γ (procAddr j) ∗
    procPriv (procAddr j) pid V M ∗ stackOwn (V.kstack + 4096#64) 512 ∗
    (∀ R5 : RegMap,
      kctx cpu ((kf.popOff.withRegs R5).withLocks (kf.locks.filter (fun x => x ≠ "proc"))) -∗
      pcIs cpu (KA.«userinit» + 0x32#64) -∗ ⌜calleeSaved kf.regs R5⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  obtain ⟨ξ0, t0⟩ := X
  subst hct
  letI : CurCtx := ⟨ξ0, KTier.kpt⟩
  iintro ⟨Hk, Hpc, #Hpinv, Hheld, Hhart, #Hused, Hpriv, Hstack, Hcont⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  ihave #HlkI := procsInv_lookup Γ j hj $$ Hpinv
  -- open the private block at `p->cwd`
  icases ui_priv_cwd_acc (procAddr j) pid V M $$ Hpriv with ⟨Hcwd, Hback⟩
  ihave Hcwd := (show wordPointsTo (GF := GF) (pCwd (procAddr j)) 8 (DFrac.own 1) V.cwd ⊢
      wordPointsTo (procAddr j + 336#64) 8 (DFrac.own 1) V.cwd
      from by unfold pCwd; iintro H; iexact H) $$ Hcwd
  -- sd a0,336(s1) : p->cwd = namei("/")
  k_step (wp_s_sd cpu _ (KA.«userinit» + 0x24#64) false 336#12 9#5 10#5 (by decide) V.cwd)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, hs1]
  iintro Hk Hpc Hcwd
  ihave Hcwd := (show wordPointsTo (GF := GF) (procAddr j + 336#64) 8 (DFrac.own 1) (kf.regs 10#5) ⊢
      wordPointsTo (pCwd (procAddr j)) 8 (DFrac.own 1) (kf.regs 10#5)
      from by unfold pCwd; iintro H; iexact H) $$ Hcwd
  ihave Hpriv := Hback $$ %(kf.regs 10#5) Hcwd
  -- open the held slot
  icases procHeldAt_cases Γ ξ0 cpu j USED ch $$ Hheld with
    ⟨Hlocked, Hwhole, %kl, %xs, %pidx, HstateW, Hchan, Hrest⟩
  ihave HstateW := (show wordPointsTo (GF := GF) (pState (procAddr j)) 4 (DFrac.own 1) USED ⊢
      wordPointsTo (procAddr j + 24#64) 4 (DFrac.own 1) USED
      from by unfold pState; iintro H; iexact H) $$ HstateW
  -- c.li a5,3
  k_step (wp_s_addi cpu _ (KA.«userinit» + 0x28#64) true 3#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, hs1]
  iintro Hk Hpc
  -- c.sw a5,24(s1) : p->state = RUNNABLE
  k_step (wp_s_sw cpu _ (KA.«userinit» + 0x2a#64) true 24#12 9#5 15#5 (by decide) USED)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, hs1]
  iintro Hk Hpc HstateW
  ihave HstateW := (show wordPointsTo (GF := GF) (procAddr j + 24#64) 4 (DFrac.own 1) (3#32) ⊢
      wordPointsTo (pState (procAddr j)) 4 (DFrac.own 1) RUNNABLE
      from by unfold pState RUNNABLE; iintro H; iexact H) $$ HstateW
  -- ===== the ghost publish =====
  iapply wpLoop_bupd
  imod (forkret_record Γ cpu _ j pid { V with cwd := kf.regs 10#5 } M hj rfl hctx)
    $$ [$Hk $Hpinv $Hpriv $Hstack] with ⟨Hk, HprocCtx⟩
  imod (pstateWhole_update Γ (procAddr j) USED RUNNABLE) $$ Hwhole with Hwhole
  imodintro
  ihave Hslots := ui_slots_runnable Γ ξ0 (procAddr j) $$ [$Hused $HprocCtx $Hhart]
  icases (pstateWhole_split Γ (procAddr j) RUNNABLE).1 $$ Hwhole with ⟨Hpsl, -⟩
  ihave Hpay : procLockResAt Γ ξ0 (procAddr j) $$ [HstateW Hpsl Hchan Hrest Hslots]
  case' _ =>
    iapply procLockRes_intro Γ ξ0 (procAddr j) RUNNABLE ch kl xs pidx
    iframe HstateW Hpsl Hchan Hrest Hslots
  ihave Hpay := (show procLockResAt (GF := GF) Γ ξ0 (procAddr j) ⊢ procLockPay Γ j ξ0
    from by unfold procLockPay; iintro H; iexact H) $$ Hpay
  -- c.mv a0,s1 ; jal release (0x80001cbc -> 0x80000ce0), ra := 0x80001cc0
  k_step (wp_s_add cpu _ (KA.«userinit» + 0x2c#64) true 10#5 0#5 9#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, hs1]
  iintro Hk Hpc
  k_step (wp_s_jal cpu _ (KA.«userinit» + 0x2e#64) false 2093092#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [userinit_br_fffffffffffff052, KCtx.rget_eq, KCtx.setReg_eq_withRegs, hs1]
  iintro Hk Hpc
  iapply (ui_release RE cpu _ (Γ.lock j) (procAddr j) ?hRa (procLockPay Γ j)
      ?hRs ?hRn ?hRK false ?hRr ?hRo) $$ [- $Hk $Hpc $HlkI $Hlocked $Hpay]
  rotate_right 1
  · isplitl []
    · iempintro
    k_norm
    iapply wpNext_off_intro
    iintro %R5 Hk Hpc %hcs5
    have hcs5' : calleeSaved kf.regs R5 := by
      unfold calleeSaved at hcs5 ⊢
      simp only [KCtx.setReg_eq_withRegs, KCtx.withRegs_regs, KCtx.setReg_regs, RegMap.set_apply,
        BitVec.reduceEq, if_false] at hcs5
      exact hcs5
    k_norm [KCtx.setReg_eq_withRegs, KCtx.popExit_false, ui_ret_c12]
    iapply Hcont $$ %R5 Hk Hpc %hcs5'
  case hRa => k_norm [KCtx.rget_eq, hs1]
  case hRs => k_norm [KCtx.setReg_eq_withRegs]
  case hRn => k_norm [KCtx.setReg_eq_withRegs, hnoff]; omega
  case hRK => k_norm [KCtx.setReg_eq_withRegs]; exact hK
  case hRr => k_norm [KCtx.setReg_eq_withRegs, hnoff, hintena]; simp
  case hRo => simp

end

/-! ## From `(KernelSyms.«userinit» + 0xe)`: `initproc = p` and `namei("/")` -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- `calleeSaved` composes. -/
theorem ui_calleeSaved_trans {R R' R'' : RegMap} (h1 : calleeSaved R R') (h2 : calleeSaved R' R'') :
    calleeSaved R R'' := by
  unfold calleeSaved at *
  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem userinit_br_1ef6 : KA.«userinit» + 0x1ef6#64 = KA.«namei» := by decide

theorem userinit_br_550a : KA.«userinit» + 0x550a#64 = KStr.«/» := by decide

theorem userinit_br_86b2 : KA.«userinit» + 0x86b2#64 = KA.«initproc» := by decide

set_option maxHeartbeats 2000000 in
/-- **From `0x80001c9c`**: `s1 = p`, `initproc = p` (published), `a0 = "/"`,
`namei`, then `ui_finish`. -/
theorem ui_publish [X : CurCtx] (RE : RELEASE) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    [FsEnv] [ForkretIs] (cpu : CPU) (kb : KCtx) (j : Nat) (ch : BitVec 64) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hct : curTier = KTier.kpt)
    (hctx : V.context = [forkretAddr, V.kstack + 4096#64] ++ List.replicate 12 0#64)
    (ha0 : kb.regs 10#5 = procAddr j)
    (hsie : kb.sie = false) (hnoff : kb.noff = 1) (hintena : kb.intena = false)
    (hlocks : kb.locks = ["proc"]) (htier : kb.tier = KTier.kpt) (hK : fsSlots ≤ kb.avail) :
    kctx cpu kb ∗ pcIs cpu (KA.«userinit» + 0xe#64) ∗ procsInv Γ ∗
    (∃ w : BitVec 64, wordPointsTo initprocAddr 8 (DFrac.own 1) w) ∗
    procHeld Γ cpu j USED ch ∗ hartAtAny Γ (procAddr j) ∗ slotUsed Γ (procAddr j) ∗
    procPriv (procAddr j) pid V M ∗ stackOwn (V.kstack + 4096#64) 512 ∗
    (∀ R5 : RegMap,
      kctx cpu ((kb.popOff.withRegs R5).withLocks (kb.locks.filter (fun x => x ≠ "proc"))) -∗
      pcIs cpu (KA.«userinit» + 0x32#64) -∗ ⌜calleeSaved (kb.regs.set 9#5 (procAddr j)) R5⌝ -∗
      initprocIs (procAddr j) -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  obtain ⟨ξ0, t0⟩ := X
  subst hct
  letI : CurCtx := ⟨ξ0, KTier.kpt⟩
  iintro ⟨Hk, Hpc, #Hpinv, ⟨%w0, Hinit⟩, Hheld, Hhart, #Hused, Hpriv, Hstack, Hcont⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- c.mv s1,a0 : s1 = p
  k_step (wp_s_add cpu _ (KA.«userinit» + 0xe#64) true 9#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, ha0]
  iintro Hk Hpc
  -- auipc a5,0x8
  k_step (wp_s_auipc cpu _ (KA.«userinit» + 0x10#64) false 8#20 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, ha0]
  iintro Hk Hpc
  -- sd a0,1680(a5) : initproc = p
  k_step (wp_s_sd cpu _ (KA.«userinit» + 0x14#64) false 1698#12 15#5 10#5 (by decide) w0)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, KCtx.setReg_eq_withRegs, ha0, ui_initproc_addr]
  iintro Hk Hpc Hinit
  -- the word is published: it is read forever after
  iapply wpLoop_bupd
  imod (initprocIs_publish (procAddr j)) $$ Hinit with #Hinitp
  imodintro
  -- auipc a0,0x5 ; addi a0,a0,1432 : a0 = "/"
  k_step (wp_s_auipc cpu _ (KA.«userinit» + 0x18#64) false 5#20 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, KCtx.setReg_eq_withRegs]
  iintro Hk Hpc
  k_step (wp_s_addi cpu _ (KA.«userinit» + 0x1c#64) false 1266#12 10#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [userinit_br_550a, KCtx.rget_eq, KCtx.setReg_eq_withRegs]
  iintro Hk Hpc
  -- jal namei (0x80001cae -> 0x80003b84), ra := 0x80001cb2
  k_step (wp_s_jal cpu _ (KA.«userinit» + 0x20#64) false 7894#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [userinit_br_1ef6, KCtx.rget_eq, KCtx.setReg_eq_withRegs]
  iintro Hk Hpc
  iapply (ui_nbcall nameiAddr KA.«namei» (by decide) FsEnv.nameiBoot Γ cpu _
      ?hKn ?hnn ?htn) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm [KCtx.setReg_eq_withRegs]
  iframe #
  case hKn => k_norm [KCtx.setReg_eq_withRegs]; exact hK
  case hnn => k_norm [KCtx.setReg_eq_withRegs, hnoff]; omega
  case htn => k_norm [KCtx.setReg_eq_withRegs]; exact htier
  k_norm [KCtx.setReg_eq_withRegs]
  iapply wpNext_off_intro
  iintro %spie3 %spp3 %R3 %hsp3 Hk Hpc %hcs3
  obtain ⟨h3a, h3b⟩ := hsp3 trivial
  k_norm [KCtx.withSpie_self' kb spie3 spp3 h3a h3b, ui_ret_c04]
  have hcsA : calleeSaved (kb.regs.set 9#5 (procAddr j)) R3 := by
    refine ui_calleeSaved_trans ?_ hcs3
    unfold calleeSaved
    simp [RegMap.set_apply]
  have hs1 : (kb.withRegs R3).regs 9#5 = procAddr j := by
    simp only [KCtx.withRegs_regs]
    have h9 := hcsA.2.2.1
    simpa [RegMap.set_apply] using h9
  iapply (ui_finish RE Γ cpu (kb.withRegs R3) j ch pid V M hj rfl hctx hs1
      ?hsie2 ?hnoff2 ?hintena2 ?hlocks2 ?htier2 ?hK2)
    $$ [- $Hk $Hpc $Hpinv $Hheld $Hhart $Hused $Hpriv $Hstack]
  rotate_right 1
  · iintro %R5 Hk Hpc %hcs5
    have hcs5' : calleeSaved (kb.regs.set 9#5 (procAddr j)) R5 :=
      ui_calleeSaved_trans hcsA (by simpa only [KCtx.withRegs_regs] using hcs5)
    k_norm
    iapply Hcont $$ %R5 Hk Hpc %hcs5' Hinitp
  case hsie2 => simp only [KCtx.withRegs_sie]; exact hsie
  case hnoff2 => simp only [KCtx.withRegs_noff]; exact hnoff
  case hintena2 => simp only [KCtx.withRegs_intena]; exact hintena
  case hlocks2 => simp only [KCtx.withRegs_locks]; exact hlocks
  case htier2 => simp only [KCtx.withRegs_tier]; exact htier
  case hK2 => simp only [KCtx.withRegs_avail]; have hh := hK; unfold fsSlots at hh; omega

end

/-! ## The whole function -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- A context whose held set is empty drops a `withLocks []`. -/
theorem ui_withLocks_nil (k : KCtx) (h : k.locks = []) : k.withLocks [] = k := by
  rw [← h]; rfl

/-- The `withSpie` the specification's post carries is the context's own. -/
theorem ui_kctx_withSpie [CurCtx] (cpu : CPU) (k : KCtx) (R : RegMap) :
    kctx (GF := GF) cpu (k.withRegs R) ⊢ kctx cpu ((k.withSpie k.spie k.spp).withRegs R) := by
  rw [KCtx.withSpie_self' k k.spie k.spp rfl rfl]

/-- What the epilogue restores makes the whole call callee-saving. -/
theorem ui_calleeSaved_epi (R0 R5 : RegMap) (ra : BitVec 64)
    (hhi : ∀ r : BitVec 5, r = 18#5 ∨ r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨
      r = 24#5 ∨ r = 25#5 ∨ r = 26#5 ∨ r = 27#5 → R5 r = R0 r) :
    calleeSaved R0 ((((R5.set 1#5 ra).set 8#5 (R0 8#5)).set 9#5 (R0 9#5)).set 2#5 (R0 2#5)) := by
  unfold calleeSaved
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
  · exact hhi 18#5 (Or.inl rfl)
  · exact hhi 19#5 (Or.inr (Or.inl rfl))
  · exact hhi 20#5 (Or.inr (Or.inr (Or.inl rfl)))
  · exact hhi 21#5 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hhi 22#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hhi 23#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact hhi 24#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact hhi 25#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact hhi 26#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  · exact hhi 27#5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))

end

theorem userinit_br_ffffffffffffff00 : KA.«userinit» + 0xffffffffffffff00#64 = KA.«allocproc» := by decide

set_option maxHeartbeats 4000000 in
/-- **`userinit` meets its specification.** -/
theorem userinit_proof (AP : ALLOCPROC) (RE : RELEASE) : USERINIT :=
  ⟨fun {hlc GF} _ _ X Γ _ _ _ cpu k γp γl γk nb np
      hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hsie hnb => by
  obtain ⟨ξ0, t0⟩ := X
  letI : CurCtx := ⟨ξ0, t0⟩
  unfold wp_userinit_body
  simp only [userinitAddr]
  iintro ⟨Hk, Hpc, #Hpinv, #Hkml, #Hpml, Hkav, Hpav, Hinit, HPhi⟩
  icases kctx_tier cpu k $$ Hk with ⟨%hct, Hk⟩
  have ht0 : t0 = KTier.kpt := hct.symm.trans htier
  subst ht0
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  have hintena : k.intena = false := by rw [← hwf.1 hnoff0]; exact hsie
  have hKu : 4 + 64 ≤ k.avail := by
    have hh := hK; unfold userinitSlots fsSlots at hh; omega
  have hK4 : 4 ≤ k.avail := by omega
  -- the prologue
  iapply (wp_prologue4s1_gen cpu k KA.«userinit» hK4)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  k_norm
  iapply wpNext_off_intro
  iintro Hk Hpc Hframe
  -- jal allocproc (0x80001c98 -> 0x80001b8e), ra := 0x80001c9c
  k_step (wp_s_jal cpu _ (KA.«userinit» + 0xa#64) false 2096886#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [userinit_br_ffffffffffffff00]
  iintro Hk Hpc
  iapply (ui_allocproc AP Γ cpu _ γl γp γk (some nb) (some (np + 1))
      ?hna ?hKa ?hlka ?hlpa ?hlqa ?hta) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm
  iframe Hkav Hpav
  iframe #
  case hna => k_norm_g; exact hnoff
  case hKa => k_norm_g; unfold allocprocSlots; omega
  case hlka => k_norm_g; exact hlk
  case hlpa => k_norm_g; exact hlp
  case hlqa => k_norm_g; exact hlq
  case hta => k_norm_g; exact htier
  k_norm
  iapply wpNext_off_intro
  iintro %spie %spp %R2 %hsp Hkd Hpc Hpost %hcs2
  icases (show allocprocPost Γ cpu γk (some nb) (some (np + 1)) (R2 10#5) ⊢
      ((⌜R2 10#5 = 0#64 ∧ ((some (np + 1) = none ∨ some (np + 1) = some 0) ∨
            ∃ gg : Nat, gg ≤ procPagetableNodes + 1 ∧ availZero (availSub (some nb) gg))⌝ ∗
          procsAvail Γ (some (np + 1)) ∗
          ∃ on' : Option Nat, ⌜on' = some nb ∨ on' = none⌝ ∗ kallocAvail γk on') ∨
       (∃ (j : Nat) (ch : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
            (M : Nat → List (BitVec 8)) (g : Nat),
          ⌜R2 10#5 = procAddr j ∧ j < NPROC ∧ 1 ≤ pid.toNat ∧ pid.toNat ≤ PIDMAX ∧
            allocprocPriv V ∧ g ≤ procPagetableNodes + 1⌝ ∗
          procHeld Γ cpu j USED ch ∗ hartAtAny Γ (procAddr j) ∗ slotUsed Γ (procAddr j) ∗
          procsAvail Γ (pavDec (some (np + 1))) ∗ procPriv (procAddr j) pid V M ∗
          stackOwn (V.kstack + 4096#64) 512 ∗ kallocAvail γk (availSub (some nb) g)))
      from by unfold allocprocPost; iintro H; iexact H) $$ Hpost with ⟨Hfail | Hsucc⟩
  · -- the failure arm: no free slot, or no page -- both refuted by the counted regimes
    icases Hfail with ⟨%hf, -, -⟩
    exact absurd hf.2 (by
      rintro ((h | h) | ⟨gg, hgg, hz⟩)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · rw [show availSub (some nb) gg = some (nb - gg) from rfl] at hz
        rcases hz with h | h
        · exact absurd h (by simp)
        · have hnz : nb - gg = 0 := Option.some.inj h
          omega)
  icases Hsucc with
    ⟨%j, %ch, %pid, %V, %M, %g, %hfacts, Hheld, Hhart, #Hused, Hpav, Hpriv, Hstack, Hkav⟩
  obtain ⟨hrj, hj, hpid1, hpid2, hVp, hgle⟩ := hfacts
  icases Hkd with ⟨⟨%hz, Hk⟩ | ⟨%hnz, Hk⟩⟩
  · exact absurd (hrj.symm.trans hz) (procAddr_nonzero hj)
  obtain ⟨hspie, hsppv⟩ := hsp trivial
  subst hspie
  subst hsppv
  k_norm [ui_ret_bee]
  iapply (ui_publish RE Γ cpu _ j ch pid V M hj rfl hVp.2.2.2.2
      ?ha0 ?hsie2 ?hnoff2 ?hintena2 ?hlocks2 ?htier2 ?hK2)
    $$ [- $Hk $Hpc $Hpinv $Hinit $Hheld $Hhart $Hused $Hpriv $Hstack]
  rotate_right 1
  · iintro %R5 Hk Hpc %hcs5 #Hinitp
    k_norm [ui_pushOffAt_pushed k hsie, hlocks, ui_filter_one, ui_withLocks_nil k hlocks, ui_ret_c12]
    -- the register facts the epilogue and the post need
    have h2 := hcs2
    have h5 := hcs5
    unfold calleeSaved at h2 h5
    simp only [KCtx.withRegs_regs, KCtx.withLocks_regs, KCtx.pushOffAt_regs, KCtx.pushed_regs,
      RegMap.set_apply, BitVec.reduceEq, if_false, if_true] at h2 h5
    have hR5_2 : R5 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by rw [h5.1, h2.1]
    have hhi : ∀ r : BitVec 5, r = 18#5 ∨ r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨
        r = 24#5 ∨ r = 25#5 ∨ r = 26#5 ∨ r = 27#5 → R5 r = k.regs r := by
      rintro r (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      · exact h5.2.2.2.1.trans h2.2.2.2.1
      · exact h5.2.2.2.2.1.trans h2.2.2.2.2.1
      · exact h5.2.2.2.2.2.1.trans h2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h5.2.2.2.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2.2.2.2
    -- the epilogue
    iapply (wp_epilogue4s1_gen cpu k (KA.«userinit» + 0x32#64) hK4 R5 hR5_2
      (k.regs 1#5) (k.regs 8#5) (k.regs 9#5)) $$ [- $Hk $Hpc $Hframe]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    k_norm
    iapply wpNext_off_intro
    iintro Hk Hpc
    ihave Hk := ui_kctx_withSpie cpu k _ $$ Hk
    ihave HPhi := wpNext_off (GF := GF) k.proc cpu _ $$ HPhi
    ihave Hpav := (show procsAvail (GF := GF) Γ (pavDec (some (np + 1))) ⊢ procsAvail Γ (some np)
      from by rw [show pavDec (some (np + 1)) = some np from by simp [pavDec]]) $$ Hpav
    iapply HPhi $$ %(k.spie) %(k.spp) %_ %(procAddr j) %g
      %(⟨fun _ => ⟨rfl, rfl⟩, ui_calleeSaved_epi k.regs R5 (k.regs 1#5) hhi, hgle,
         ⟨j, hj, rfl⟩⟩) Hk Hpc Hinitp Hkav Hpav
  case ha0 => k_norm_g; exact hrj
  case hsie2 => k_norm_g
  case hnoff2 => k_norm_g [hnoff0]
  case hintena2 => k_norm_g; exact hintena
  case hlocks2 => k_norm_g [hlocks]
  case htier2 => k_norm_g; exact htier
  case hK2 => k_norm [trapRes]; unfold fsSlots; omega⟩

end Xv6
