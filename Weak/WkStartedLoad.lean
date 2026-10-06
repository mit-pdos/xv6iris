/-
Weak: **the `started` WAITER -- the racy load through the escrow** (M3c/M4): the racy `lw` of
xv6's boot spin composed with the escrow's one-shot collapse, the receipt that crosses from the
load to the fence, and the pred-R fence that cashes it.

Rocq: `iris/WkStartedLoad.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).  Three landed pieces meet here and nothing else
is built: `WeakRacy.wp_wracy_load` (the load rule quantifying over the ADMISSIBLE read results),
`WeakStarted.wstarted_observe` (the escrow's ONE-SHOT COLLAPSE: a read that came back non-clear
read a timestamp at or above the escrow's deposit, and the payload is frozen at that deposit),
and `WeakAcquire.wwp_fence_step` + `WeakStarted.wstarted_deliver` (the pred-R fence that thaws the
deposit into the reader's own index).  The pairing "the timestamp at which the byte I READ was
admissible is covered by my `w_vrOld`" is `WeakRacy.wgain`, PROVED by `exec_of_wrun_gain` for a
hart that has not stored to the window (`wunwritten`); what the leaf still owes is
`WeakRacy.wreads_win` (no weak-memory content).  The other side condition,
`WeakStarted.wstarted_img_clear`, is handed out by the escrow's MINT and travels as a pure fact
returned by the caller's σ-callback.

**The kernel image (Lean, `Xv6/KernelImage.lean`).**  The comments' sites are checked against the
LEAN image: `main = 0x80000ece`; `main+0x16 = 0x80000ee4` is `c.lw a5,0(a4)` (`0x431c`,
`Weak.ksRacyLoadMain16Word`), `main+0x18 = 0x80000ee6` is `fence r,rw` (`0x0230000f`,
`Weak.ksFenceMain18Word`), then `sext.w a5,a5` at `+0x1c` and `beqz a5,main+0x16` at `+0x1e`.
**Drift: none** in the offsets (Rocq's image places `main` elsewhere -- Rocq `KernelPins` has the
load at `0x80000e94` -- but every offset this file names is the same).  The file's statements
name no kernel address (the pcs are parameters), so nothing here imports the image.

**Deviations from Rocq.**

1. NAMES / VOCABULARY: the tree's camelCase (map below); no name of this file is in
   `notes/weak-port-dupnames.json`.  As `Weak/WeakAcquire.lean` deviation 1 and
   `Weak/WeakRacy.lean` deviation 5: the ambient `GenId`/`CpuId` are the explicit `gen`/`cpu`;
   `WWP Loop` is `wwpTriv ⊤ (WExpr.loop gen cpu)`; `fin_to_nat cpu_id` is `cpu.val`;
   `register_lookup PC (wm_regs σ)` is `σ.wmRegs .PC`; `mstate` is `ExecSt`; `bv 32` is
   `BitVec 32`; `nth_byte` is `nthByte (n := 4)`; `lock_zero` is `lockZero`; `monPred_at P V` is
   `P.monPred_at V`; `ws_le` is `wsLe`; `ak_coh rak = false` is `rak.akIfetch = false` (WeakRacy
   deviation 4); `Barrier_RISCV_*` are `.Barrier_RISCV_*`.
2. STATEMENT SHAPES (WeakAcquire deviation 2): Rocq `A -∗ B -∗ C -∗ D` is `A ⊢ B -∗ C -∗ D`;
   the `Example` `wwp_started_wait_seq` is a `theorem`.  The callbacks `wstartedLdCb` /
   `wstartedFenceCb` take `gen` and `cpu` explicitly (they mention the hart's interpretation and
   `Loop`).
3. O2, THE TEXT PIN (WeakInstr deviation 4): the callbacks hand over
   `pinnedRead σ (accAddr pc j) ∧ fetchPinned σ (accAddr pc j)` per text byte (Rocq:
   `pinned_read` only), as `wpWracyLoadGain` / `wwpFenceStep` require.
4. Lean-only `WkStartedLoad.wlat4Sync_timeless`: the escrow's element bundle is timeless (Rocq's
   `iInv … as (te v) "(>Hw & Hhist)"` found the instance by unfolding; Lean has none for
   `wlat4Sync`).  (Rocq 13 declarations; Lean 13 + 1 = 14.)
5. `wwpStartedFenceGen`/`wwpStartedFence`/`wwpStartedFenceR`/`wwpStartedWaitSeq` carry
   `[LockExG GF]`: Lean's `WeakAcquire.wwpFenceStep` sits in that file's `wpLock` section and so
   takes the lock-ghost class (Rocq's `wwp_fence_step` has no such context).

**Rocq → Lean name map.**  `bv32_ne_zero_byte` `bv32NeZeroByte`, `wstarted_rcpt` `wstartedRcpt`,
`wstarted_rcpt_persistent` `wstartedRcpt_persistent`, `wstarted_rcpt_mono` `wstartedRcptMono`,
`wstarted_rcpt_deliver_gen` `wstartedRcptDeliverGen`, `wstarted_rcpt_deliver`
`wstartedRcptDeliver`, `wstarted_ld_cb` `wstartedLdCb`, `wwp_started_load` `wwpStartedLoad`,
`wstarted_fence_cb` `wstartedFenceCb`, `wwp_started_fence_gen` `wwpStartedFenceGen`,
`wwp_started_fence` `wwpStartedFence`, `wwp_started_fence_r` `wwpStartedFenceR`,
`wwp_started_wait_seq` `wwpStartedWaitSeq`.  Lean-only: `WkStartedLoad.wlat4Sync_timeless`
(deviation 4).

**Dropped:** nothing.  (`Print Assumptions` ↦ the CI axiom audit.)

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1-3 and 5.
-/
import Weak.WeakRacy
import Weak.WeakAcquire
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The byte that witnesses a non-clear word -/

/-- A word that is not the cleared one differs from it at some byte -- the witness the collapse
is applied at. -/
theorem bv32NeZeroByte (w : BitVec 32) :
    w ≠ lockZero →
    ∃ j : Nat, j < 4 ∧ nthByte (n := 4) w j ≠ nthByte (n := 4) lockZero 0 := by
  intro hne
  apply Classical.byContradiction
  intro hno
  apply hne
  apply bvEqOfBytes (n := 4) w lockZero
  intro j hj
  rw [nthByteClear j hj]
  exact Classical.byContradiction fun hb => hno ⟨j, hj, hb⟩

section wpStartedLoad

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The escrow's element bundle is timeless (Lean-only, deviation 4). -/
instance WkStartedLoad.wlat4Sync_timeless (a : PAddr) (t : Nat) (w : BitVec 32) :
    Timeless (wlat4Sync (GF := GF) a t w) := by
  unfold wlat4Sync wlat4El wlatElem syncWin syncByte wcdsEl; infer_instance

/-! ## 2. THE RECEIPT: what crosses from the load to the fence

The deposit, together with the fact that this hart's read floor already covers it.  It is
persistent whenever the payload is. -/

def wstartedRcpt (P : VProp GF) (ws : Wstate) : IProp GF :=
  iprop(∃ T : Nat, ⌜T ≤ ws.wVrOld⌝ ∗ P.monPred_at (viewScl T))

instance wstartedRcpt_persistent (P : VProp GF) [Persistent P] (ws : Wstate) :
    Persistent (wstartedRcpt P ws) := by
  unfold wstartedRcpt; infer_instance

/-- It survives the steps between the load and the fence: `wVrOld` only grows. -/
theorem wstartedRcptMono (P : VProp GF) (ws ws' : Wstate) :
    wsLe ws ws' → wstartedRcpt P ws ⊢ wstartedRcpt P ws' := by
  intro hle
  unfold wstartedRcpt
  iintro ⟨%T, %hT, HP⟩
  iexists T
  isplitr
  · ipureintro; exact Nat.le_trans hT (wsLeVrOld _ _ hle)
  · iexact HP

/-- ... and any PRED-R fence cashes it.  The kernel's is `fence r,rw` (`main+0x18`). -/
theorem wstartedRcptDeliverGen (P : VProp GF) (σ : Wmstate) (ws' : Wstate) (b : barrier_kind) :
    acqPredR b →
    wVFence b σ ws' →
    wstartedRcpt P σ.wmWs ⊢ vwpHold P ws' := by
  intro hb hQ
  unfold wstartedRcpt
  iintro ⟨%T, %hT, HP⟩
  iapply wstartedDeliverGen P σ ws' T b hb hT hQ
  iexact HP

theorem wstartedRcptDeliver (P : VProp GF) (σ : Wmstate) (ws' : Wstate) :
    wVFence .Barrier_RISCV_rw_rw σ ws' →
    wstartedRcpt P σ.wmWs ⊢ vwpHold P ws' :=
  wstartedRcptDeliverGen P σ ws' _ acqPredR_rw_rw

/-! ## 3. THE WAITER'S LOAD -- one racy `lw` through the escrow

`WeakRacy.wpWracyLoadGain` with three changes: the caller's callback runs at ⊤∖↑wstartedN and
borrows the latest-write authority; it no longer proves the flag word is in memory (the escrow's
element bundle says so); its continuation receives the READ OUTCOME. -/

def wstartedLdCb (gen : Nat) (cpu : CPU) (a : PAddr) (P : VProp GF) (pc : BitVec 64)
    (rak : AkInfo) (Pp : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) : IProp GF :=
  iprop(∀ σ : Wmstate,
    wlatInterp σ.wmImg σ.wmLog -∗
    wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑wstartedN, ∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜Pp σ⌝ ∗
      ⌜wstartedImgClear σ a⌝ ∗
      ⌜wunwritten σ.wmWs a 4⌝ ∗
      wlatInterp σ.wmImg σ.wmLog ∗
      (∃ t0 : ExecSt, ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝) ∗
      ▷ (∀ (tick : Bool) (σ' : Wmstate) (w : BitVec 32),
          ⌜wadm σ rak a 4 w⌝ -∗
          ⌜exec (riscvStep tick) (wpatchSt σ a 4 w) = some ((), wpatchSt σ' a 4 w)⌝ -∗
          ⌜wstepPostRacy σ σ'⌝ -∗
          ⌜Q σ σ'⌝ -∗
          (⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ wstartedRcpt P σ'.wmWs)) -∗
          |={∅, ⊤ \ ↑wstartedN}=> wmstateRest (hlc := hlc) (GF := GF) cpu σ' ∗
            wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))

/-- THE WAITER'S LOAD.  `rak.akIfetch = false`: a weak-tier access; the `wreadsWin` premise: the
step READS the window (kills the patch-independence arm). -/
theorem wwpStartedLoad (gen : Nat) (cpu : CPU) (a : PAddr) (P : VProp GF) [Persistent P]
    (pc : BitVec 64) (rak : AkInfo) (Pp : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    accWf a 4 →
    rak.akIfetch = false →
    (∀ σ σ' : Wmstate, Q σ σ' → σ'.wmLog = σ.wmLog) →
    (∀ (tick : Bool) (σ : Wmstate), Pp σ → wreadsWin a 4 tick σ) →
    wracyCert cpu.val pc a 4 rak wadmAny Pp Q →
    syncWin (GF := GF) a 4 ⊢
      inv wstartedN (wstartedBody (GF := GF) a P) -∗
        wstartedLdCb (hlc := hlc) gen cpu a P pc rak Pp Q -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hacca hakc hquiet hreads hcert
  iintro #Hsync #Hinv Hk
  unfold wstartedLdCb
  iapply wpWracyLoadGain gen cpu pc a 4 rak wadmAny Pp Q hgen haccpc hacca hakc hcert
  isplitr
  · iexact Hsync
  iintro %σ Hσ
  -- the log lower bound the escrow's snapshot is read against
  icases wmstateInterpLogLb cpu σ $$ Hσ with ⟨Hσ, #Hlbσ⟩
  icases (wmstateInterpSplit cpu σ).mp $$ Hσ with ⟨Hlat, Hrest⟩
  icases keepPure1 (wmstateRestFacts cpu σ) $$ Hrest with ⟨%hfacts, Hrest⟩
  obtain ⟨_, hwf⟩ := hfacts
  -- open the escrow at ⊤, keep it across the step; the element bundle comes out now
  imod (inv_acc (E := ⊤) (N := wstartedN) (P := wstartedBody (GF := GF) a P)
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  unfold wstartedBody wstartedAt
  icases later_exists.mpr $$ Hbody with ⟨%te, Hbody⟩
  icases later_exists.mpr $$ Hbody with ⟨%v, Hbody⟩
  icases later_sep.mp $$ Hbody with ⟨>Hw, Hhist⟩
  icases keepPure (wlat4SyncFlatGen σ a te v hwf hacca) $$ Hlat Hw with ⟨%hfl, Hlat, Hw⟩
  obtain ⟨hflat, _⟩ := hfl
  imod Hk $$ %σ Hlat Hrest with ⟨%hpc, %htext, %hP, %himg, %hun, Hlat, ⟨%t0, %hex0⟩, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  isplitr
  · ipureintro; exact hun
  -- the flag's value is unconstrained: the code branches on it itself
  isplitr
  · ipureintro; exact wadmFilterAny σ rak a 4
  isplitr
  · ipureintro
    rw [readBytesOfBytes (wflatMem σ.wmImg σ.wmLog) a 4 v hflat]
    rfl
  isplitr
  · iexists t0; ipureintro; exact hex0
  inext
  iintro %tick %σ' %w %hadm %hex %hpost %hQ %hgd
  -- the patch-independence arm cannot happen at a LOAD
  have hgain : wgain σ σ' rak a 4 w :=
    hgd.elim id fun huni => (hreads tick σ hP ⟨σ', huni⟩).elim
  ihave Hbody : wstartedBody (GF := GF) a P $$ [Hw Hhist]
  · unfold wstartedBody wstartedAt
    iexists te, v
    isplitl [Hw]
    · iexact Hw
    · iexact Hhist
  -- THE COLLAPSE, in the non-clear arm
  ihave Harm : (wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ wstartedBody (GF := GF) a P ∗
      (⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ wstartedRcpt P σ'.wmWs))) $$ [Hlat Hbody]
  · by_cases hw0 : w = lockZero
    · isplitl [Hlat]
      · iexact Hlat
      isplitl [Hbody]
      · iexact Hbody
      ileft; ipureintro; exact hw0
    · obtain ⟨j, hj, hbne⟩ := bv32NeZeroByte w hw0
      obtain ⟨t, hok, hcov⟩ := hgain j hj
      icases wstartedObserve a P σ rak j t (nthByte (n := 4) w j) himg hj hok hbne
        $$ Hlbσ Hlat Hbody with ⟨Hlat, Hbody, -, %T, %hTle, #HP0⟩
      isplitl [Hlat]
      · iexact Hlat
      isplitl [Hbody]
      · iexact Hbody
      iright
      isplitr
      · ipureintro; exact hw0
      unfold wstartedRcpt
      iexists T
      isplitr
      · ipureintro; omega
      · iexact HP0
  icases Harm with ⟨Hlat, Hbody, Harm⟩
  imod Hcont $$ %tick %σ' %w %hadm %hex %hpost %hQ Harm with ⟨Hrest, Hwp⟩
  imod Hclose $$ [Hbody]
  · inext
    unfold wstartedBody wstartedAt
    iexact Hbody
  imodintro
  isplitl [Hlat Hrest]
  · iapply (wmstateInterpSplit cpu σ').mpr
    isplitl [Hlat]
    · rw [hpost.1, hquiet σ σ' hQ]
      iexact Hlat
    · iexact Hrest
  · iexact Hwp

/-! ## 4. THE WAITER'S FENCE -- one pred-R fence that cashes the receipt -/

def wstartedFenceCb (gen : Nat) (cpu : CPU) (P : VProp GF) (pc : BitVec 64)
    (Pf : Wmstate → Prop) : IProp GF :=
  iprop(∀ σ : Wmstate,
    wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤,∅}=∗
      ⌜σ.wmRegs .PC = pc⌝ ∗
      ⌜∀ j : Nat, j < 4 →
        pinnedRead σ (WeakInterp.accAddr pc j) ∧ fetchPinned σ (WeakInterp.accAddr pc j)⌝ ∗
      ⌜Pf σ⌝ ∗
      wstartedRcpt P σ.wmWs ∗
      ∃ t0 t1 : ExecSt,
        ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝ ∗
        ⌜exec (riscvStep true) (wflatSt σ) = some ((), t1)⌝ ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate),
            ⌜wstepPost σ σ' (if tick then t1 else t0)⌝ -∗
            vwpHold P σ'.wmWs -∗
            |={∅,⊤}=> wmstateInterp (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)))

theorem wwpStartedFenceGen [LockExG GF] (gen : Nat) (cpu : CPU) (P : VProp GF) (pc : BitVec 64)
    (Pf : Wmstate → Prop) (b : barrier_kind) :
    gen = 0 →
    accWf pc 4 →
    acqPredR b →
    wstepCert cpu.val pc Pf (wQFence b) →
    wstartedFenceCb (hlc := hlc) gen cpu P pc Pf ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccpc hb hcert
  iintro Hk
  unfold wstartedFenceCb
  iapply wwpFenceStep gen cpu pc b Pf hgen haccpc hcert
  iintro %σ Hσ
  imod Hk $$ %σ Hσ with ⟨%hpc, %htext, %hP, Hrcpt, %t0, %t1, %hex0, %hex1, Hcont⟩
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
  iintro %tick %σ' %hpost %hQ %_hrelp
  icases wstartedRcptDeliverGen P σ σ'.wmWs b hb hQ $$ Hrcpt with Hh
  iapply Hcont $$ %tick %σ' %hpost Hh

theorem wwpStartedFence [LockExG GF] (gen : Nat) (cpu : CPU) (P : VProp GF) (pc : BitVec 64)
    (Pf : Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    wstepCert cpu.val pc Pf (wQFence .Barrier_RISCV_rw_rw) →
    wstartedFenceCb (hlc := hlc) gen cpu P pc Pf ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  fun hgen haccpc hcert =>
    wwpStartedFenceGen gen cpu P pc Pf _ hgen haccpc acqPredR_rw_rw hcert

/-- THE KERNEL'S OWN FENCE: `fence r,rw` at `main+0x18` (Lean image `0x80000ee6`). -/
theorem wwpStartedFenceR [LockExG GF] (gen : Nat) (cpu : CPU) (P : VProp GF) (pc : BitVec 64)
    (Pf : Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    wstepCert cpu.val pc Pf (wQFence .Barrier_RISCV_r_rw) →
    wstartedFenceCb (hlc := hlc) gen cpu P pc Pf ⊢
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) :=
  fun hgen haccpc hcert =>
    wwpStartedFenceGen gen cpu P pc Pf _ hgen haccpc acqPredR_r_rw hcert

/-! ## 5. SMOKE TEST: `lw` ; `fence r,rw`, the handoff end to end

xv6's secondary-hart wait `while (__atomic_load_n(&started, __ATOMIC_ACQUIRE) == 0) ;` is
`lw a5,0(a4) ; fence r,rw ; sext.w ; beqz` (Lean image: `main+0x16 .. +0x1e`).  Its LAST
iteration: the racy load observes a non-clear flag and collapses the escrow into a receipt, the
fence cashes it, and the payload arrives at the reader's own index. -/

theorem wwpStartedWaitSeq [LockExG GF] (gen : Nat) (cpu : CPU) (a : PAddr) (P : VProp GF) [Persistent P]
    (pcl pcf : BitVec 64) (rak : AkInfo) (Pl Pf : Wmstate → Prop)
    (Ql : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pcl 4 →
    accWf pcf 4 →
    accWf a 4 →
    rak.akIfetch = false →
    (∀ σ σ' : Wmstate, Ql σ σ' → σ'.wmLog = σ.wmLog) →
    (∀ (tick : Bool) (σ : Wmstate), Pl σ → wreadsWin a 4 tick σ) →
    wracyCert cpu.val pcl a 4 rak wadmAny Pl Ql →
    wstepCert cpu.val pcf Pf (wQFence .Barrier_RISCV_r_rw) →
    syncWin (GF := GF) a 4 ⊢
      inv wstartedN (wstartedBody (GF := GF) a P) -∗
        (∀ σ : Wmstate,
          wlatInterp σ.wmImg σ.wmLog -∗
          wmstateRest (hlc := hlc) (GF := GF) cpu σ ={⊤ \ ↑wstartedN, ∅}=∗
            ⌜σ.wmRegs .PC = pcl⌝ ∗
            ⌜∀ j : Nat, j < 4 →
              pinnedRead σ (WeakInterp.accAddr pcl j) ∧ fetchPinned σ (WeakInterp.accAddr pcl j)⌝ ∗
            ⌜Pl σ⌝ ∗
            ⌜wstartedImgClear σ a⌝ ∗
            ⌜wunwritten σ.wmWs a 4⌝ ∗
            wlatInterp σ.wmImg σ.wmLog ∗
            (∃ t0 : ExecSt, ⌜exec (riscvStep false) (wflatSt σ) = some ((), t0)⌝) ∗
            ▷ (∀ (tick : Bool) (σ' : Wmstate) (w : BitVec 32),
                ⌜wadm σ rak a 4 w⌝ -∗
                ⌜exec (riscvStep tick) (wpatchSt σ a 4 w) = some ((), wpatchSt σ' a 4 w)⌝ -∗
                ⌜wstepPostRacy σ σ'⌝ -∗
                ⌜Ql σ σ'⌝ -∗
                (⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ wstartedRcpt P σ'.wmWs)) -∗
                |={∅, ⊤ \ ↑wstartedN}=>
                  wmstateRest (hlc := hlc) (GF := GF) cpu σ' ∗
                  -- the CLEARED arm is the spin loop's retry edge; the other exits to the fence
                  (wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) ∨
                    wstartedFenceCb (hlc := hlc) gen cpu P pcf Pf))) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen haccl haccf hacca hakc hquiet hreads hcertl hcertf
  iintro #Hsync #Hinv Hk
  iapply wwpStartedLoad gen cpu a P pcl rak Pl Ql hgen haccl hacca hakc hquiet hreads hcertl
    $$ Hsync Hinv
  unfold wstartedLdCb
  iintro %σ Hlat Hrest
  imod Hk $$ %σ Hlat Hrest with ⟨%hpc, %htext, %hP, %himg, %hun, Hlat, ⟨%t0, %hex0⟩, Hcont⟩
  imodintro
  isplitr
  · ipureintro; exact hpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  isplitr
  · ipureintro; exact himg
  isplitr
  · ipureintro; exact hun
  isplitl [Hlat]
  · iexact Hlat
  isplitr
  · iexists t0; ipureintro; exact hex0
  inext
  iintro %tick %σ' %w %hadm %hex %hpost %hQ Harm
  imod Hcont $$ %tick %σ' %w %hadm %hex %hpost %hQ Harm with ⟨Hrest, Hnext⟩
  imodintro
  isplitl [Hrest]
  · iexact Hrest
  icases Hnext with (Hloop | Hf)
  · iexact Hloop
  · iapply wwpStartedFenceR gen cpu P pcf Pf hgen haccf hcertf $$ Hf

end wpStartedLoad

end Weak
