/-
Weak: **the lock and the escrow AT THE WP ALTITUDE** (M3c item 3): the state
interpretation minus the latest-write authority, the acquire attempt (one
`amoswap.w.aq` through the lock invariant), the generic spin loop and the
acquire loop, the releasing store, the `started` setter, the fence step and the
escrow's reader-side delivery, the `fence ; sw` smoke test, and the same rules
over a DISCHARGED certificate.

Rocq: `iris/WeakAcquire.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (Rocq vocabulary).  M3b landed the two lock
cores (`WeakLock.wacquire_core` / `wrelease_core`) and the escrow's writer
(`WeakStarted.wstarted_set`) at the σ/σ' altitude.  This file composes them
THROUGH `WeakInstr.wp_winstr`, over a real instruction certificate, so that
what comes out is a weakest-precondition rule: one `amoswap.w.aq` = one acquire
attempt, one `sw` = one release, and a spin loop over the former.

THE THREE THINGS THAT MADE THIS WORK.
(1) THE LATEST-WRITE AUTHORITY IS WHAT A RACY LEAF BORROWS.  Exactly one
    conjunct of `wmstate_interp σ` -- `wlat_interp` -- is what a step that
    writes a shared byte has to update.  §1 splits it off as `wmstate_rest`:
    the leaf's caller keeps registers, devices, the log auth and this hart's
    `wstate` cell, while the LOCK keeps the latest-write authority across the
    step and hands it back retargeted.
(2) THE INVARIANT IS OPEN ACROSS THE STEP, AND THE MASKS ARE THE LEAF'S OWN.
    The lock invariant is opened at ⊤ (leaving ⊤∖↑wlockN for the caller's own
    fupd), held across the ▷, and closed on the way back.
(3) THE VALUE THE SWAP RETURNS IS READ OUT BEFORE THE STEP, FROM THE ELEMENTS
    (`wlat4L_flat_gen`: no view hypothesis, the AMO's read half is
    `ak_latest`), so the caller's `exec` fact can be supplied at a KNOWN lock
    word, and the post-step branch on "did I get it" is the same `v`.
§3–§8 take the instruction certificate as a PREMISE; §9 discharges it with
`WeakCert`'s trace-indexed certificates.  The BRANCH instructions of the spin
loop have no weak leaf yet, so the loop is stated over an abstract RETRY EDGE
(§4's generic Löb rule).

THE ONE THING THAT DID NOT COMPOSE (the Rocq closing note): the `started`
waiter's PLAIN load cannot go through `wp_winstr` -- a racy plain load may read
the era image while the flat projection already holds the setter's value, so no
`exec`-level fact about `wflat_st σ` describes the step.  What it needs (M4) is
a load rule quantifying over the ADMISSIBLE read results; the pieces below it
are `WeakExec.wpWexecStep` and `WeakStarted.wstartedReadTs`/`wstartedReadVrOld`.

**O2 (owner decision; `Weak/WeakCert.lean` header).**  WeakCert's whole-window
certificate form `wPEff` carries the Lean-only `fetchPin s es` (the trace's
i-cache reads are fetch-pinned, and `fetchFresh es`).  §9 SUPPLIES it here, so
its corollaries' callbacks owe exactly Rocq's `wP_eff` (`wPEffText`, below):
the fetch reads lie in the text window at `pc` (the premise Rocq already
carries), the text window is fetch-pinned (the second half of the text pin the
callback already hands over -- kernel text is never written,
`WeakInstr.wkernelTextTextPinned`), and `fetchFresh` holds of every trace
here by computation (the fetch comes first).

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below); none is in the duplicated-name
   table.  Vocabulary as `Weak/WeakInstr.lean` deviation 1 /
   `Weak/WeakCert.lean` deviation 1: Rocq's ambient `GenId`/`CpuId` are the
   explicit `gen`/`cpu` (WeakExec deviation 1); `WWP Loop` is
   `wwpTriv ⊤ (WExpr.loop gen cpu)`; `fin_to_nat cpu_id` is `cpu.val`;
   `register_lookup PC (wm_regs σ)` is `σ.wmRegs .PC`; `mstate` is `ExecSt`;
   `wflat … !! pa_add a j` is `wflatMem … (a + BitVec.ofNat 64 j)`;
   `nth_byte v j` is `nthByte (n := 4) v j`; `acc_addr` is
   `WeakInterp.accAddr`; `reg_interp`/`dev_interp` are `regInterp cpu`/
   `devInterpAt (MachGS.era)` (as in `WeakGhost.wmstateInterp`); `locked γ i`
   (Rocq `WpLock`) is `lockedEx γ i` (WeakLock deviation 2).
2. STATEMENT SHAPES (WeakInstr deviation 3): Rocq `A -∗ B -∗ C` is
   `A ⊢ B -∗ C`; a pure Rocq premise `⌜φ⌝ -∗ …` in first position is
   `⌜φ⌝ ⊢ …`; the `Example` `wwp_release_seq` is a `theorem`.  The definitions
   that mention the hart's interpretation (`wmstateRest`, `wmstateRestNonv`,
   `wacqCb`, `wrelCb`) take `cpu` (and the callbacks `gen`) explicitly.
3. O2, THE TEXT PIN (WeakInstr deviation 4): the callbacks `wacqCb`/`wrelCb`,
   `wwpFenceStep`'s and `wwpReleaseSeq`'s hand over
   `pinnedRead σ (accAddr pc j) ∧ fetchPinned σ (accAddr pc j)` per text byte
   (Rocq: `pinned_read` only), as `wpWinstr` requires.
4. O2, §9 (header): the corollaries' callbacks owe `wPEffText` (Rocq `wP_eff`
   verbatim: no fetch obligation) rather than Lean's `wPEff` (which carries
   `fetchPin`).  The Lean-only `wPEffText`, `wPEffOfText`, `fetchInWindow`,
   `fetchPinOfText`, `wstepCertText`, and the per-trace facts
   `fetchInWindowAmo`/`fetchInWindowStore`/`fetchFreshAmo`/`fetchFreshStore`
   supply it.
5. Lean-only helpers: `keepPure1` (Rocq's non-consuming `iDestruct … as %`
   for a one-premise lemma), `nvOkWlockInv`/`nvOkWstartedAt` (the `nv_ok`
   payment off the invariant bodies, Rocq's inline `iDestruct "Hbody" as …`).
   (12 Lean-only declarations: 22 Rocq + 12 = 34.)

**Rocq → Lean name map.**  `wmstate_rest` `wmstateRest`,
`wmstate_interp_split` `wmstateInterpSplit`, `wmstate_rest_facts`
`wmstateRestFacts`, `wmstate_rest_nv` `wmstateRestNv`, `wmstate_rest_nonv`
`wmstateRestNonv`, `wmstate_rest_of_nonv` `wmstateRestOfNonv`,
`wflat_word_agree` `wflatWordAgree`, `wacq_cb` `wacqCb`, `wwp_acquire_swap`
`wwpAcquireSwap`, `wwp_spin_loop` `wwpSpinLoop`, `wwp_acquire_loop`
`wwpAcquireLoop`, `wrel_cb` `wrelCb`, `wwp_release_store` `wwpReleaseStore`,
`wwp_started_set` `wwpStartedSet`, `wwp_fence_step` `wwpFenceStep`,
`wwp_started_fence_deliver_gen` `wwpStartedFenceDeliverGen`,
`wwp_started_fence_deliver` `wwpStartedFenceDeliver`, `wwp_release_seq`
`wwpReleaseSeq`, `wwp_acquire_swap_cert` `wwpAcquireSwapCert`,
`wwp_release_store_cert` `wwpReleaseStoreCert`, `wwp_started_set_cert`
`wwpStartedSetCert`, `wwp_acquire_loop_cert` `wwpAcquireLoopCert`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakCert
import Weak.WeakStarted
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- A pure consequence of one resource, keeping it (Lean-only, deviation 5). -/
theorem keepPure1 {PROP : Type _} [BI PROP] {P : PROP} {φ : Prop} (h : P ⊢ ⌜φ⌝) :
    P ⊢ ⌜φ⌝ ∗ P :=
  (and_intro h .rfl).trans
    (persistent_and_affinely_sep_left_mp.trans (sep_mono_left affinely_elim))

/-! ## 1. The state interpretation, minus the latest-write authority

What a racy leaf borrows for the duration of one step.  The split is
definitional (a reassociation of `wmstateInterp`'s conjuncts). -/

section rest

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

def wmstateRest (cpu : CPU) (σ : Wmstate) : IProp GF :=
  iprop(⌜wsBounded σ.wmWs σ.wmLog.length⌝ ∗
    -- the φ conjunct rides here, next to `wsBounded`, exactly as in `wmstateInterp`
    ⌜nvHart σ.wmLog cpu σ.wmWs⌝ ∗
    ⌜wlogWf σ.wmLog⌝ ∗
    regInterp cpu σ.wmRegs ∗
    devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) σ.wmDev ∗
    wlogAuth σ.wmLog ∗
    wwsAuth cpu σ.wmWs)

theorem wmstateInterpSplit (cpu : CPU) (σ : Wmstate) :
    wmstateInterp (hlc := hlc) (GF := GF) cpu σ ⊣⊢
      wlatInterp σ.wmImg σ.wmLog ∗ wmstateRest (hlc := hlc) (GF := GF) cpu σ := by
  unfold wmstateInterp wmstateRest
  constructor
  · iintro ⟨%hb, %hn, %hw, Hr, Hd, Hl, Hlat, Hws⟩
    isplitl [Hlat]
    · iexact Hlat
    isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hw
    iframe Hr Hd Hl Hws
  · iintro ⟨Hlat, %hb, %hn, %hw, Hr, Hd, Hl, Hws⟩
    isplitr
    · ipureintro; exact hb
    isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact hw
    iframe Hr Hd Hl Hlat Hws

theorem wmstateRestFacts (cpu : CPU) (σ : Wmstate) :
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ⊢
      ⌜wsBounded σ.wmWs σ.wmLog.length ∧ wlogWf σ.wmLog⌝ := by
  unfold wmstateRest
  iintro ⟨%hb, -, %hw, -⟩
  ipureintro
  exact ⟨hb, hw⟩

theorem wmstateRestNv (cpu : CPU) (σ : Wmstate) :
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ⊢ ⌜nvHart σ.wmLog cpu σ.wmWs⌝ := by
  unfold wmstateRest
  iintro ⟨-, %hn, -⟩
  ipureintro
  exact hn

/-- THE φ-FREE REMAINDER (φ-upgrade, deliverable C, the AMO interface).  A
racy/lock leaf holds neither the lock word's element bundle nor the
latest-write authority when it hands the borrowed state back -- both belong to
the invariant its CALLER opened -- so it cannot pay the violation-freedom
conjunct.  The callback returns everything EXCEPT the conjunct, and
`wwpAcquireSwap` supplies it, where it does hold the lock bundle at σ'. -/
def wmstateRestNonv (cpu : CPU) (σ : Wmstate) : IProp GF :=
  iprop(⌜wsBounded σ.wmWs σ.wmLog.length⌝ ∗
    ⌜wlogWf σ.wmLog⌝ ∗
    regInterp cpu σ.wmRegs ∗
    devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) σ.wmDev ∗
    wlogAuth σ.wmLog ∗
    wwsAuth cpu σ.wmWs)

theorem wmstateRestOfNonv (cpu : CPU) (σ : Wmstate) :
    ⌜nvHart σ.wmLog cpu σ.wmWs⌝ ⊢
      wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ -∗ wmstateRest (hlc := hlc) (GF := GF) cpu σ := by
  unfold wmstateRest wmstateRestNonv
  iintro %hnv ⟨%hb, %hw, Hr, Hd, Hl, Hws⟩
  isplitr
  · ipureintro; exact hb
  isplitr
  · ipureintro; exact hnv
  isplitr
  · ipureintro; exact hw
  iframe Hr Hd Hl Hws

end rest

/-! ## 2. Byte-wise identification of two readings of the same word -/

theorem wflatWordAgree (σ : Wmstate) (a : PAddr) (v v' : BitVec 32) :
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)) →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 4) v' j)) →
    v = v' := by
  intro h1 h2
  exact bvEqOfBytes (n := 4) v v' fun j hj => Option.some.inj ((h1 j hj).symm.trans (h2 j hj))

section wpLock

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [LockExG GF]

/-- The lock bundle's `nvOk` payment, off the invariant body (Lean-only, deviation 5). -/
theorem nvOkWlockInv (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (γ : GName)
    (lk : PAddr) (R : VProp GF) :
    wlatInterp (GF := GF) img log ⊢
      wlockInv (GF := GF) γ lk R -∗ ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr lk j)⌝ := by
  unfold wlockInv
  iintro Hi ⟨%st, %t, %v, Hw, -⟩
  iapply nvOkWlat4L c img log lk t v (tidOf st) $$ Hi Hw

/-- ... and off the escrow's (Lean-only, deviation 5). -/
theorem nvOkWstartedAt (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (P : VProp GF) (t : Nat) (v : BitVec 32) :
    wlatInterp (GF := GF) img log ⊢
      wstartedAt (GF := GF) a P t v -∗ ⌜∀ j : Nat, j < 4 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wstartedAt
  iintro Hi ⟨Hw, -⟩
  iapply nvOkWlat4Sync c img log a t v $$ Hi Hw

/-! ## 3. THE ACQUIRE ATTEMPT -- one `amoswap.w.aq` through the invariant

`wpWinstr` with three changes: the caller's callback runs at ⊤∖↑wlockN; it is
handed the LOCK WORD `v` the swap will return, with the flat-memory fact its
`exec` lemma needs and the latest-write authority (handed straight back); its
post-step continuation receives the ACQUIRE OUTCOME. -/

def wacqCb (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF) (pc : BitVec 64)
    (P : Wmstate → Prop) : IProp GF :=
  iprop(∀ (σ : Wmstate) (v : BitVec 32),
    ⌜∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (lk + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)⌝ -∗
    wlatInterp σ.wmImg σ.wmLog -∗
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑wlockN, ∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      -- φ-upgrade: the leaf proves the pure facts where it HOLDS the resources
      ⌜∀ j : Nat, j < 4 → nvOk σ.wmLog cpu (WeakInterp.accAddr pc j)⌝ ∗
      wlatInterp σ.wmImg σ.wmLog ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            ((⌜v = lockZero⌝ ∗ vwpHold R σ'.wmWs ∗ lockedEx (GF := GF) γ cpu) ∨
              ⌜v ≠ lockZero⌝) -∗
            |={∅, ⊤ \ ↑wlockN}=> wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))

theorem wwpAcquireSwap (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (P : Wmstate → Prop) (es : List Weff) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    -- the trace's FOOTPRINT: the fetch window and the lock word, nothing else
    (∀ a : Int, weffsTouch es a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j)) →
    wstepCert cpu.val pc P (wQFr (wQAmoAq (some cpu.val) lk lockOne) (some cpu.val) es) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      wacqCb (hlc := hlc) gen cpu γ lk R pc P -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hfoot hcert
  iintro #Hinv Hk
  unfold wacqCb
  iapply wpWinstr gen cpu pc P _ hgen haccpc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨_, hwf⟩ := hfacts
  -- open the lock: ⊤ → ⊤ ∖ ↑wlockN, held across the step
  imod (inv_acc (E := ⊤) (N := wlockN) (P := wlockInv (GF := GF) γ lk R) CoPset.subseteq_top)
    $$ Hinv with ⟨HI, Hclose⟩
  unfold wlockInv
  icases later_exists.mpr $$ HI with ⟨%st, HI⟩
  icases later_exists.mpr $$ HI with ⟨%t, HI⟩
  icases later_exists.mpr $$ HI with ⟨%v, HI⟩
  icases later_sep.mp $$ HI with ⟨>Hw, Hlk⟩
  -- the swap's return value, off the elements alone
  icases keepPure (wlat4LFlatGen σ lk t v (tidOf st) hwf hacclk) $$ Hlat Hw with ⟨%hfl, Hlat, Hw⟩
  obtain ⟨hflat, _⟩ := hfl
  imod Hk $$ %σ %v %hflat Hlat Hrest
    with ⟨%hpc, %htext, %hP, %hnvpc, Hlat, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQfr
  obtain ⟨hQ, hQeff⟩ := hQfr
  -- past the step: reassemble the invariant body and fire the core
  ihave Hbody : wlockInv (GF := GF) γ lk R $$ [Hw Hlk]
  · unfold wlockInv
    iexists st, t, v
    iframe Hw
    iexact Hlk
  icases wacquireCore γ lk R cpu (some cpu.val) σ σ' hwf hacclk hQ rfl $$ Hlat Hbody
    with ⟨%v', %hflat', Hupd⟩
  have hvv : v = v' := wflatWordAgree σ lk v v' hflat hflat'
  subst hvv
  imod Hupd with ⟨Hlat, Hbody, Harm⟩
  -- THE PAYMENT: the lock word's retargeted bundle is in `Hbody`, the fetch window's fact came up
  -- from the leaf, and the message the step appended is THIS hart's
  icases keepPure (nvOkWlockInv cpu σ'.wmImg σ'.wmLog γ lk R) $$ Hlat Hbody
    with ⟨%hnvlk, Hlat, Hbody⟩
  have hnv' : nvHart σ'.wmLog cpu σ'.wmWs := by
    apply nvHartOfWQEffOk cpu σ σ' es hQeff hnvσ
    intro a ha
    rcases hfoot a ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [hQ.2.2]
      intro n
      refine nvByteAppOwn _ _ cpu _ n (hnvpc j hj n) fun m hm => ?_
      rw [List.mem_singleton] at hm
      subst hm
      rfl
    · exact hnvlk j hj
  imod Hcont $$ %tick %σ' %hpost Harm with ⟨Hrest, Hwp⟩
  imod Hclose $$ [Hbody]
  · inext
    unfold wlockInv
    iexact Hbody
  imodintro
  isplitl [Hlat Hrest]
  · iapply (wmstateInterpSplit cpu σ').mpr
    iframe Hlat
    iapply wmstateRestOfNonv cpu σ' $$ %hnv' Hrest
  · iexact Hwp

/-! ## 4. THE SPIN LOOP

A weak-memory spinlock's loop carries no weak-memory content at all: the
acquire's whole content is in the ONE attempt that succeeds (§3).  The loop
needs only the Löb rule, and the ▷ it consumes is the one `wpWinstr` provides
at every instruction.  THE BRANCH BACK IS THE CALLER'S (no weak branch leaf
yet, M4). -/

theorem wwpSpinLoop (gen : Nat) (cpu : CPU) (K : IProp GF) :
    □ (K -∗ ▷ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) ⊢
      K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  iintro #Hbody
  iloeb as IH
  iintro HK
  iapply Hbody $$ HK
  iexact IH

/-- THE ACQUIRE LOOP.  One iteration is one `wwpAcquireSwap` whose FAILURE
branch consumes the recursive call. -/
theorem wwpAcquireLoop (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (P : Wmstate → Prop) (K : IProp GF) (es : List Weff) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    (∀ a : Int, weffsTouch es a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j)) →
    wstepCert cpu.val pc P (wQFr (wQAmoAq (some cpu.val) lk lockOne) (some cpu.val) es) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      □ (K -∗ ▷ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk R pc P) -∗
        K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hfoot hcert
  iintro #Hinv #Hatt HK
  iapply wwpSpinLoop gen cpu K $$ [] HK
  imodintro
  iintro HK Hrec
  iapply wwpAcquireSwap gen cpu γ lk R pc P es hgen haccpc hacclk hfoot hcert $$ Hinv
  iapply Hatt $$ HK Hrec

/-! ## 5. THE RELEASING STORE -- one `sw` through an invariant

The releaser's callback is the acquire's minus the branch: it hands over the
payload `R` AT ITS OWN INDEX and gets back nothing.  ONE CALLBACK SHAPE serves
the lock's release and the escrow's setter (§6); the namespace is a
parameter. -/

def wrelCb (gen : Nat) (cpu : CPU) (R : VProp GF) (pc : BitVec 64) (P : Wmstate → Prop)
    (N : Namespace) : IProp GF :=
  iprop(∀ σ : Wmstate,
    wlatInterp σ.wmImg σ.wmLog -∗
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑N, ∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ⌜∀ j : Nat, j < 4 → nvOk σ.wmLog cpu (WeakInterp.accAddr pc j)⌝ ∗
      -- φ-upgrade §1: the release site witnesses its own `fence rw,w` here
      ⌜σ.wmWs.wRelp = true⌝ ∗
      wlatInterp σ.wmImg σ.wmLog ∗
      vwpHold R σ.wmWs ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            |={∅, ⊤ \ ↑N}=> wmstateRestNonv (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))

theorem wwpReleaseStore (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (P : Wmstate → Prop) (es : List Weff) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    (∀ a : Int, weffsTouch es a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j)) →
    wstepCert cpu.val pc P (wQFr (wQStore (some cpu.val) lk lockZero) (some cpu.val) es) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      lockedEx (GF := GF) γ cpu -∗
        wrelCb (hlc := hlc) gen cpu R pc P wlockN -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hfoot hcert
  iintro #Hinv Htok Hk
  unfold wrelCb
  iapply wpWinstr gen cpu pc P _ hgen haccpc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨hbnd, _⟩ := hfacts
  imod (inv_acc (E := ⊤) (N := wlockN) (P := wlockInv (GF := GF) γ lk R) CoPset.subseteq_top)
    $$ Hinv with ⟨Hbody, Hclose⟩
  imod Hk $$ %σ Hlat Hrest
    with ⟨%hpc, %htext, %hP, %hnvpc, %hrelp, Hlat, HR, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQfr
  obtain ⟨hQ, hQeff⟩ := hQfr
  imod wreleaseCore γ lk R cpu (some cpu.val) σ σ' hQ rfl hrelp hbnd $$ Hlat Hbody Htok HR
    with ⟨Hlat, Hbody⟩
  -- the same payment as the acquire: the release's own message is THIS hart's
  icases keepPure (nvOkWlockInv cpu σ'.wmImg σ'.wmLog γ lk R) $$ Hlat Hbody
    with ⟨%hnvlk, Hlat, Hbody⟩
  have hnv' : nvHart σ'.wmLog cpu σ'.wmWs := by
    apply nvHartOfWQEffOk cpu σ σ' es hQeff hnvσ
    intro a ha
    rcases hfoot a ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · obtain ⟨_, ⟨kc, hlog', _⟩, _⟩ := hQ
      rw [hlog']
      intro n
      refine nvByteAppOwn _ _ cpu _ n (hnvpc j hj n) fun m hm => ?_
      rw [List.mem_singleton] at hm
      subst hm
      rfl
    · exact hnvlk j hj
  imod Hcont $$ %tick %σ' %hpost with ⟨Hrest, Hwp⟩
  imod Hclose $$ [Hbody]
  · inext
    iexact Hbody
  imodintro
  isplitl [Hlat Hrest]
  · iapply (wmstateInterpSplit cpu σ').mpr
    iframe Hlat
    iapply wmstateRestOfNonv cpu σ' $$ %hnv' Hrest
  · iexact Hwp

/-! ## 6. THE `started` ESCROW

THE SETTER is the release, verbatim in structure; the only difference is which
invariant is opened and that the value stored is 1.  THE WAITER'S LOAD IS NOT
HERE (header). -/

theorem wwpStartedSet (gen : Nat) (cpu : CPU) (a : PAddr) (Pl : VProp GF) (pc : BitVec 64)
    (P : Wmstate → Prop) (es : List Weff) :
    gen = 0 →
    accWf pc 4 →
    accWf a 4 →
    (∀ z : Int, weffsTouch es z →
      (∃ j, j < 4 ∧ z = WeakInterp.accAddr pc j) ∨ (∃ j, j < 4 ∧ z = WeakInterp.accAddr a j)) →
    wstepCert cpu.val pc P (wQFr (wQStore (some cpu.val) a lockOne) (some cpu.val) es) →
    inv wstartedN (wstartedBody (GF := GF) a Pl) ⊢
      wrelCb (hlc := hlc) gen cpu Pl pc P wstartedN -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacca hfoot hcert
  iintro #Hinv Hk
  unfold wrelCb
  iapply wpWinstr gen cpu pc P _ hgen haccpc hcert
  iintro %σ Hσ
  -- the escrow's one-shot conjunct is refreshed to the PRE-state's log
  icases wmstateInterpLogLb cpu σ $$ Hσ with ⟨Hσ, #Hlbσ⟩
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  icases keepPure1 (wmstateRestNv cpu σ) $$ Hrest with ⟨%hnvσ, Hrest⟩
  obtain ⟨hbnd, _⟩ := hfacts
  imod (inv_acc (E := ⊤) (N := wstartedN) (P := wstartedBody (GF := GF) a Pl)
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  imod Hk $$ %σ Hlat Hrest
    with ⟨%hpc, %htext, %hP, %hnvpc, %hrelp, Hlat, HP0, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQfr
  obtain ⟨hQ, hQeff⟩ := hQfr
  imod wstartedSet a Pl (some cpu.val) σ σ' hQ hrelp hbnd $$ Hlbσ Hlat Hbody HP0 with ⟨Hlat, Hat⟩
  -- the escrow's word is SYNC, so its bytes pay through the `WSync` arm
  icases keepPure (nvOkWstartedAt cpu σ'.wmImg σ'.wmLog a Pl (σ.wmLog.length + 1) lockOne)
    $$ Hlat Hat with ⟨%hnva, Hlat, Hat⟩
  have hnv' : nvHart σ'.wmLog cpu σ'.wmWs := by
    apply nvHartOfWQEffOk cpu σ σ' es hQeff hnvσ
    intro z hz
    rcases hfoot z hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · obtain ⟨_, ⟨kc, hlog', _⟩, _⟩ := hQ
      rw [hlog']
      intro n
      refine nvByteAppOwn _ _ cpu _ n (hnvpc j hj n) fun m hm => ?_
      rw [List.mem_singleton] at hm
      subst hm
      rfl
    · exact hnva j hj
  imod Hcont $$ %tick %σ' %hpost with ⟨Hrest, Hwp⟩
  imod Hclose $$ [Hat]
  · inext
    unfold wstartedBody
    iexists σ.wmLog.length + 1, lockOne
    iexact Hat
  imodintro
  isplitl [Hlat Hrest]
  · iapply (wmstateInterpSplit cpu σ').mpr
    iframe Hlat
    iapply wmstateRestOfNonv cpu σ' $$ %hnv' Hrest
  · iexact Hwp

/-! ## 7. THE FENCE STEP

A fence touches no memory, so the caller's callback is `wpWinstr`'s verbatim, at
the full mask ⊤; what it gets back is the instruction's ISA content in VIEW
form. -/

theorem wwpFenceStep (gen : Nat) (cpu : CPU) (pc : BitVec 64) (b : barrier_kind)
    (P : Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    wstepCert cpu.val pc P (wQFence b) →
    (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜P σ⌝ ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            ⌜wVFence b σ σ'.wmWs⌝ -∗
            ⌜barrierArms b = true → σ'.wmWs.wRelp = true⌝ ={∅,⊤}=∗
              wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hcert
  iintro Hk
  iapply wpWinstr gen cpu pc P (wQFence b) hgen haccpc hcert
  iintro %σ Hσ
  imod Hk $$ %σ Hσ with ⟨%hpc, %ht, %hP, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact ht
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQ
  iapply Hcont $$ %tick %σ' %hpost %(hQ.1) %(hQ.2)

/-- ... and the escrow's READER-SIDE payoff at that step:
`WeakStarted.wstartedDeliver` at the WP altitude's successor. -/
theorem wwpStartedFenceDeliverGen (Pl : VProp GF) (σ σ' : Wmstate) (t : Nat) (b : barrier_kind) :
    acqPredR b →
    t ≤ σ.wmWs.wVrOld →
    wQFence b σ σ' →
    Pl.monPred_at (viewScl t) ⊢ vwpHold Pl σ'.wmWs :=
  fun hb ht hQ => wstartedDeliverGen Pl σ σ'.wmWs t b hb ht hQ.1

theorem wwpStartedFenceDeliver (Pl : VProp GF) (σ σ' : Wmstate) (t : Nat) :
    t ≤ σ.wmWs.wVrOld →
    wQFence .Barrier_RISCV_rw_rw σ σ' →
    Pl.monPred_at (viewScl t) ⊢ vwpHold Pl σ'.wmWs :=
  wwpStartedFenceDeliverGen Pl σ σ' t _ acqPredR_rw_rw

/-! ## 8. SMOKE TEST: two instructions in a row, each its own `wpWinstr`

xv6's `release` is `fence rw,w ; sw zero,0(s1)`, composed at the WP altitude:
nothing glues the two steps but `wstepPost`. -/

theorem wwpReleaseSeq (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pcf pcs : BitVec 64) (Pf Ps : Wmstate → Prop) (ess : List Weff) :
    gen = 0 →
    accWf pcf 4 →
    accWf pcs 4 →
    accWf lk 4 →
    (∀ a : Int, weffsTouch ess a →
      (∃ j, j < 4 ∧ a = WeakInterp.accAddr pcs j) ∨ (∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j)) →
    wstepCert cpu.val pcf Pf (wQFence .Barrier_RISCV_rw_w) →
    wstepCert cpu.val pcs Ps (wQFr (wQStore (some cpu.val) lk lockZero) (some cpu.val) ess) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      lockedEx (GF := GF) γ cpu -∗
        (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
          ⌜σ.wmRegs .PC = pcf⌝ ∗
          ⌜∀ j : Nat, j < 4 →
            pinnedRead σ (WeakInterp.accAddr pcf j) ∧ fetchPinned σ (WeakInterp.accAddr pcf j)⌝ ∗
          ⌜Pf σ⌝ ∗
          ∃ t0 t1 : ExecSt,
            ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
            ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
            ▷ (∀ (tick : Bool) (σ' : Wmstate),
                ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
                ⌜wVFence .Barrier_RISCV_rw_w σ σ'.wmWs⌝ -∗
                ⌜σ'.wmWs.wRelp = true⌝ ={∅,⊤}=∗
                  wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
                  wrelCb (hlc := hlc) gen cpu R pcs Ps wlockN)) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccf haccs hacclk hfoot hcertf hcerts
  iintro #Hinv Htok Hk
  iapply wwpFenceStep gen cpu pcf .Barrier_RISCV_rw_w Pf hgen haccf hcertf
  iintro %σ Hσ
  imod Hk $$ %σ Hσ with ⟨%hpc, %htext, %hP, %t0, %t1, %hex0, %hex1, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists t0, t1
  isplitr
  · ipureintro; exact hex0
  isplitr
  · ipureintro; exact hex1
  inext
  iintro %tick %σ' %hpost %hQ %hQrelp
  imod Hcont $$ %tick %σ' %hpost %hQ %(hQrelp rfl) with ⟨Hσ', Hrel⟩
  imodintro
  isplitl [Hσ']
  · iexact Hσ'
  · iapply wwpReleaseStore gen cpu γ lk R pcs Ps ess hgen haccs hacclk hfoot hcerts
      $$ Hinv Htok Hrel

/-! ## 9. THE SAME THREE RULES, OVER A DISCHARGED CERTIFICATE

`WeakCert` discharges the certificate: `wcertAmoAq` / `wcertStore` prove
`wstepCert` outright for a step whose EFFECT TRACE is the given one, under
`wPEff`.  So the corollaries below have NO certificate premise: what is left for
the caller is one `execEff`-level fact per instruction, inside the σ-callback.
The fetch is left generic in kind/address/width, so a compressed 2-byte fetch
instantiates these too.

### 9a. The O2 fetch obligation, supplied here (Lean-only, deviation 4) -/

/-- Rocq's `wP_eff` verbatim: Lean's `wPEff` minus the O2 `fetchPin`. -/
def wPEffText (_tid : Option Nat) (es : List Weff) : Wmstate → Prop :=
  fun s => wlogWf s.wmLog ∧
    ∃ W : GSet PAddr,
      (∀ a, a ∈ W → paZ a ≠ 0) ∧
      (∀ a, a ∈ W → pinnedRead s (paZ a)) ∧
      (∀ tick : Bool, ∃ t' : ExecSt,
        execEff (riscvStep tick) ⟨s.wmRegs, wmemRestrict s W, s.wmDev⟩ = some ((), t', es) ∧
        bmDomSub t'.mem W)

theorem wPEffOfText (tid : Option Nat) (es : List Weff) (s : Wmstate) :
    wPEffText tid es s → fetchPin s es → wPEff tid es s := by
  rintro ⟨hwf, W, h0, hp, hrun⟩ hfp
  exact ⟨hwf, W, h0, hp, hfp, hrun⟩

/-- Every i-cache read of the trace lies in the text window at `pc`. -/
def fetchInWindow (pc : BitVec 64) (es : List Weff) : Prop :=
  ∀ (ak : AkInfo) (pa : PAddr) (n : Nat), Weff.WEread ak pa n ∈ es → ak.akIfetch = true →
    ∀ j, j < n → ∃ j', j' < 4 ∧ WeakInterp.accAddr pa j = WeakInterp.accAddr pc j'

theorem fetchPinOfText (s : Wmstate) (pc : BitVec 64) (es : List Weff) :
    fetchInWindow pc es → fetchFresh es →
    (∀ j : Nat, j < 4 → fetchPinned s (WeakInterp.accAddr pc j)) →
    fetchPin s es := by
  intro hw hf ht
  refine ⟨fun ak pa n hin hif j hj => ?_, hf⟩
  obtain ⟨j', hj', he⟩ := hw ak pa n hin hif j hj
  rw [he]
  exact ht j' hj'

/-- The certificate's own text pin (whose second half is the fetch pin of the
window) discharges `fetchPin`. -/
theorem wstepCertText (cid : Nat) (pc : BitVec 64) (es : List Weff) (Q : Wmstate → Wmstate → Prop) :
    fetchInWindow pc es → fetchFresh es →
    wstepCert cid pc (wPEff (some cid) es) Q →
    wstepCert cid pc (wPEffText (some cid) es) Q := by
  intro hw hf hc σ tick hpc hacc htext hP
  exact hc σ tick hpc hacc htext
    (wPEffOfText _ _ _ hP (fetchPinOfText σ pc es hw hf fun j hj => (htext j hj).2))

theorem fetchInWindowAmo (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    fetchInWindow pc [.WEread akf pf nf, .WEread aka ea 4, .WEwrite akw ea 4 v] := by
  intro hcoh hfetch ak pa n hin hif j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, Weff.WEread.injEq, reduceCtorEq] at hin
  rcases hin with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨j', hj', he⟩ := hfetch _ ⟨j, hj, rfl⟩
    exact ⟨j', hj', he⟩
  · rw [hcoh] at hif
    exact absurd hif (by decide)

theorem fetchInWindowStore (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    fetchInWindow pc [.WEread akf pf nf, .WEwrite akw ea 4 v] := by
  intro hfetch ak pa n hin _ j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, Weff.WEread.injEq, reduceCtorEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  obtain ⟨j', hj', he⟩ := hfetch _ ⟨j, hj, rfl⟩
  exact ⟨j', hj', he⟩

/-- The fetch comes first, the write last: nothing is fetched after a write. -/
theorem fetchFreshAmo (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo) (ea : PAddr)
    (v : BitVec 32) :
    fetchFresh [.WEread akf pf nf, .WEread aka ea 4, .WEwrite akw ea 4 v] := by
  simp [fetchFresh, weffWrites]

theorem fetchFreshStore (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) (ea : PAddr)
    (v : BitVec 32) :
    fetchFresh [.WEread akf pf nf, .WEwrite akw ea 4 v] := by
  simp [fetchFresh, weffWrites]

/-! ### 9b. The corollaries -/

theorem wwpAcquireSwapCert (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    aka.akIfetch = false →
    aka.akSync = true →
    akw.akLatest = true →
    -- the FETCH read is generic in kind/address/width, so its footprint is tied to `pc` by the caller
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      wacqCb (hlc := hlc) gen cpu γ lk R pc
        (wPEffText (some cpu.val) [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne]) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hcoh hsync hlat hfetch
  refine wwpAcquireSwap gen cpu γ lk R pc _
    [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne] hgen haccpc hacclk ?_ ?_
  · intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · right
      rcases weffsTouchCons _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j := ha
        exact ⟨j, hj, rfl⟩
      · exact weffsTouchWrite1 _ lk _ _ a ha
  · exact wstepCertText _ pc _ _ (fetchInWindowAmo pc akf pf nf aka akw lk lockOne hcoh hfetch)
      (fetchFreshAmo akf pf nf aka akw lk lockOne)
      (wstepCertFr _ pc _ _ (wcertAmoAq cpu.val pc akf pf nf aka akw lk lockOne hcoh hsync hlat))

theorem wwpReleaseStoreCert (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      lockedEx (GF := GF) γ cpu -∗
        wrelCb (hlc := hlc) gen cpu R pc
          (wPEffText (some cpu.val) [.WEread akf pf nf, .WEwrite akw lk 4 lockZero]) wlockN -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hfetch
  refine wwpReleaseStore gen cpu γ lk R pc _ [.WEread akf pf nf, .WEwrite akw lk 4 lockZero]
    hgen haccpc hacclk ?_ ?_
  · intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · exact .inr (weffsTouchWrite1 _ lk _ _ a ha)
  · exact wstepCertText _ pc _ _ (fetchInWindowStore pc akf pf nf akw lk lockZero hfetch)
      (fetchFreshStore akf pf nf akw lk lockZero)
      (wstepCertFr _ pc _ _ (wcertStore cpu.val pc akf pf nf akw lk lockZero))

theorem wwpStartedSetCert (gen : Nat) (cpu : CPU) (a : PAddr) (Pl : VProp GF) (pc : BitVec 64)
    (akf : AkInfo) (pf : PAddr) (nf : Nat) (akw : AkInfo) :
    gen = 0 →
    accWf pc 4 →
    accWf a 4 →
    (∀ z : Int, weffTouches (.WEread akf pf nf) z → ∃ j, j < 4 ∧ z = WeakInterp.accAddr pc j) →
    inv wstartedN (wstartedBody (GF := GF) a Pl) ⊢
      wrelCb (hlc := hlc) gen cpu Pl pc
        (wPEffText (some cpu.val) [.WEread akf pf nf, .WEwrite akw a 4 lockOne]) wstartedN -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacca hfetch
  refine wwpStartedSet gen cpu a Pl pc _ [.WEread akf pf nf, .WEwrite akw a 4 lockOne]
    hgen haccpc hacca ?_ ?_
  · intro z hz
    rcases weffsTouchCons _ _ z hz with hz | hz
    · exact .inl (hfetch z hz)
    · exact .inr (weffsTouchWrite1 _ a _ _ z hz)
  · exact wstepCertText _ pc _ _ (fetchInWindowStore pc akf pf nf akw a lockOne hfetch)
      (fetchFreshStore akf pf nf akw a lockOne)
      (wstepCertFr _ pc _ _ (wcertStore cpu.val pc akf pf nf akw a lockOne))

/-- ... and the loop, whose only premise is now the caller's retry edge. -/
theorem wwpAcquireLoopCert (gen : Nat) (cpu : CPU) (γ : GName) (lk : PAddr) (R : VProp GF)
    (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat) (aka akw : AkInfo) (K : IProp GF) :
    gen = 0 →
    accWf pc 4 →
    accWf lk 4 →
    aka.akIfetch = false →
    aka.akSync = true →
    akw.akLatest = true →
    (∀ a : Int, weffTouches (.WEread akf pf nf) a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    inv wlockN (wlockInv (GF := GF) γ lk R) ⊢
      □ (K -∗ ▷ (K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
          wacqCb (hlc := hlc) gen cpu γ lk R pc
            (wPEffText (some cpu.val)
              [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne])) -∗
        K -∗ wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacclk hcoh hsync hlat hfetch
  refine wwpAcquireLoop gen cpu γ lk R pc _ K
    [.WEread akf pf nf, .WEread aka lk 4, .WEwrite akw lk 4 lockOne] hgen haccpc hacclk ?_ ?_
  · intro a ha
    rcases weffsTouchCons _ _ a ha with ha | ha
    · exact .inl (hfetch a ha)
    · right
      rcases weffsTouchCons _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ a = WeakInterp.accAddr lk j := ha
        exact ⟨j, hj, rfl⟩
      · exact weffsTouchWrite1 _ lk _ _ a ha
  · exact wstepCertText _ pc _ _ (fetchInWindowAmo pc akf pf nf aka akw lk lockOne hcoh hfetch)
      (fetchFreshAmo akf pf nf aka akw lk lockOne)
      (wstepCertFr _ pc _ _ (wcertAmoAq cpu.val pc akf pf nf aka akw lk lockOne hcoh hsync hlat))

end wpLock

end Weak
