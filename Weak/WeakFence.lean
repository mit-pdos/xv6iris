/-
Weak: **the fence frontier, the AMO read half, and the release→acquire transfer** (M2b, items 1
and 2).

Rocq: `iris/WeakFence.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance:
- WHAT A FENCE DOES.  `WeakInterp.barrierPost` with kind `rw,rw` sets
  `wVrNew ⊔= wVrOld ⊔ wVwOld`: the hart's INDEX (`wsView ws = ⟨wVrNew, wCoh⟩`) jumps EXACTLY to
  the ACQUIRE FRONTIER `acqView ws := ⟨max wVrNew (max wVrOld wVwOld), wCoh⟩`
  (`wsView_fence_rw`, `rfl`).  So the FSL-lineage "acquire-pending" modality `∇ P` is, here,
  `P.monPred_at (acqView ws)`.
- IT CANNOT BE A `VProp` CONNECTIVE: the index `(wVrNew, wCoh)` does not mention
  `wVrOld`/`wVwOld`, so the frontier is not a function of the index.  iRC11 pays for a real `∇` with
  a TRIPLE index; here `∇` is given at the `vwpHold` altitude, `vwpAcq P ws`, a deliberate deferral.
- THE WRITER SIDE IS A LEMMA, NOT A MODALITY: in the promise-free machine a predecessor-W fence
  constrains nothing; what the handoff needs is that the releasing store's timestamp DOMINATES the
  releaser's whole index, which is `wsBounded` plus arithmetic (`release_deposit`).
- THE AMO READ HALF: an `amoswap.w.aq` read is `akLatest`, whose admissibility IS
  `WeakMem.latest`: the value is the LATEST write with no view hypothesis (`wamo_read_latest`, fires
  off an element held in an INVARIANT), and the acquire's post-view carries the read timestamp into
  the hart's SCALAR floor (`amo_acq_gain`).
- WHAT THEY COMPOSE INTO: `release_acquire_transfer` (the spinlock) and `release_fence_transfer`
  (plain read + succ-R fence, the `started`/MP shape) — the M3 lock/escrow skeleton at the view
  altitude.

**O2 Stage B (owner decision D2).**  This file is "unaffected" by O2 (design §4): every lemma is
about the DATA views, which `fence.i` does not move (`barrierPost ws .Barrier_RISCV_i = ws`).  The
Lean-only §7 records the Stage-B counterpart of the frontier story at the INSTRUCTION view
(`WeakInterp.itvPost`/`wbarrierPost`): `fence.i` delivers nothing to the data index
(`wsView_barrier_i`), and raises the hart's `wmItv` past its data floor and its own last store; in
particular an acquire read of `t` followed by `fence.i` makes `t` fetch-visible (`amo_acq_fenceI`).

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below); vocabulary as `Weak/WeakVProp.lean` deviation 6
   (`ws_view` ↦ `wsView`, `view_scl` ↦ `viewScl`, `w_vrNew ws` ↦ `ws.wVrNew`, `⊑` ↦ `≤`,
   `S (length log)` ↦ `log.length + 1`, `wm_ws σ` ↦ `σ.wmWs`, `ak_coh` ↦ `akIfetch` (O2 rename,
   `Weak/WeakInterp.lean`)).  `View a m` ↦ `⟨a, m⟩`.
2. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped; §2/§3/§5/§6 are stated without
   `[WeakGS GF]` (unused, as `WeakVProp` deviation 2); §4's AMO rules take `[WeakGS GF]`.
3. `vwp_acq_ne` / `vwp_acq_mono'` (Rocq `Global Instance`s) are the theorems `vwpAcq_ne` /
   `vwpAcq_mono'` (as `WeakVProp` deviation 4).
4. STATEMENT SHAPES (`WeakVProp` deviation 1): Rocq `P -∗ Q -∗ ⌜φ⌝` is `P ∗ Q ⊢ ⌜φ⌝`
   (`wamo_read_latest`, `wpt_amo_read`).
5. The Rocq `Example`s `mp_transfer`/`mp_transfer_aq` are named `theorem`s.  `mp_transfer`'s
   unused binders `x y rl` are kept (`y` is used; `x`, `rl` are dead in Rocq too).
6. `flr_acq_view` states the RHS with `coh ws a`, which is `flr`'s map lookup by `rfl`.
7. Lean-only §7 (Stage B, above): `wsView_barrier_i`, `acqPredR_not_i`, `itvPost_fenceI_vrNew`,
   `itvPost_fenceI_vwOld`, `amo_acq_fenceI`, `wbarrierPost_fenceI_ws`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `acq_view` `acqView`, `flr_acq_view` `flr_acqView`,
`ws_view_acq_view` `wsView_acqView`, `ws_view_fence_rw` `wsView_fence_rw`,
`ws_view_barrier_rw_rw` `wsView_barrier_rw_rw`, `ws_view_barrier_rw_r` `wsView_barrier_rw_r`,
`acq_view_r` `acqViewR`, `ws_view_fence_r` `wsView_fence_r`, `ws_view_barrier_r_r`
`wsView_barrier_r_r`, `acq_view_r_acq_view` `acqViewR_acqView`, `view_scl_acq_vrOld`
`viewScl_acq_vrOld`, `view_scl_acq_vwOld` `viewScl_acq_vwOld`, `acq_pred_r` `acqPredR`,
`acq_pred_r_rw_rw/rw_r/r_rw/r_r` `acqPredR_rw_rw/rw_r/r_rw/r_r`, `view_scl_acq_pred_r`
`viewScl_acqPredR`, `vwp_acq` `vwpAcq`, `vwp_acq_r` `vwpAcqR`, `vwp_acq_ne` `vwpAcq_ne`,
`vwp_acq_mono'` `vwpAcq_mono'`, `vwp_acq_fence` `vwpAcq_fence`, `vwp_acq_barrier`
`vwpAcq_barrier`, `vwp_acq_r_fence` `vwpAcqR_fence`, `vwp_acq_r_barrier` `vwpAcqR_barrier`,
`vwp_hold_acq` `vwpHold_acq`, `vwp_acq_r_acq` `vwpAcqR_acq`, `vwp_acq_intro` `vwpAcq_intro`,
`vwp_acq_r_intro` `vwpAcqR_intro`, `vwp_acq_view_at` `vwpAcq_view_at`, `vwp_acq_sep/exist/pure/
embed` `vwpAcq_sep/exist/pure/embed`, `fence_delivers_scl` `fence_delivers_scl`,
`ws_bounded_view_scl` `wsBounded_viewScl`, `ws_view_store_dom` `wsView_store_dom`,
`release_deposit(_at)` same, `amo_acq_gain` same, `load_byte_gain` same, `wamo_read_latest` same,
`wpt_amo_read` same, `wpt_amo_seen` same, `release_acquire_transfer` same,
`release_fence_transfer` same, `mp_transfer(_aq)` same.

**Dropped:** nothing.
-/
import Weak.WeakGhost
import Weak.WeakInterp
import Weak.WeakMem
import Weak.WeakView
import Weak.WeakVProp
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! ## 1. The acquire frontier -/

/-- The index a succ-R fence with pred-RW will deliver.  Spelled with exactly `fencePost`'s own
nesting, so the fence law below is `rfl`. -/
def acqView (ws : Wstate) : View :=
  ⟨max ws.wVrNew (max ws.wVrOld ws.wVwOld), ws.wCoh⟩

theorem flr_acqView (ws : Wstate) (a : Int) :
    flr (acqView ws) a = max (max ws.wVrNew (max ws.wVrOld ws.wVwOld)) (coh ws a) := rfl

/-- The hart's index is below its own frontier ... -/
theorem wsView_acqView (ws : Wstate) : wsView ws ≤ acqView ws := fun a => by
  rw [flr_wsView, flr_acqView]; omega

/-- ... and a full fence puts it exactly there. -/
theorem wsView_fence_rw (ws : Wstate) (sw : Bool) :
    wsView (fencePost ws true true true sw) = acqView ws := rfl

theorem wsView_barrier_rw_rw (ws : Wstate) :
    wsView (barrierPost ws .Barrier_RISCV_rw_rw) = acqView ws := rfl

theorem wsView_barrier_rw_r (ws : Wstate) :
    wsView (barrierPost ws .Barrier_RISCV_rw_r) = acqView ws := rfl

/-- A weaker pred set delivers less: an `r,r` fence carries the READ frontier only. -/
def acqViewR (ws : Wstate) : View :=
  ⟨max ws.wVrNew ws.wVrOld, ws.wCoh⟩

theorem wsView_fence_r (ws : Wstate) (sw : Bool) :
    wsView (fencePost ws true false true sw) = acqViewR ws := by
  simp only [wsView, fencePost, acqViewR, ↓reduceIte, Bool.false_eq_true]
  congr 1; omega

theorem wsView_barrier_r_r (ws : Wstate) :
    wsView (barrierPost ws .Barrier_RISCV_r_r) = acqViewR ws :=
  wsView_fence_r ws false

theorem acqViewR_acqView (ws : Wstate) : acqViewR ws ≤ acqView ws := fun a => by
  show max (max ws.wVrNew ws.wVrOld) (coh ws a) ≤ _
  rw [flr_acqView]; omega

/-- THE DELIVERY FACTS.  A timestamp the hart has already READ (in `wVrOld`) — or already WRITTEN
(`wVwOld`) — is covered by the frontier, hence by the hart's index after the fence. -/
theorem viewScl_acq_vrOld (ws : Wstate) (t : Nat) (ht : t ≤ ws.wVrOld) :
    viewScl t ≤ acqViewR ws := fun a => by
  rw [flr_scl_eq]
  show t ≤ max (max ws.wVrNew ws.wVrOld) (coh ws a)
  omega

theorem viewScl_acq_vwOld (ws : Wstate) (t : Nat) (ht : t ≤ ws.wVwOld) :
    viewScl t ≤ acqView ws := fun a => by
  rw [flr_scl_eq, flr_acqView]; omega

/-- WHICH FENCE KINDS DELIVER A READ: the read frontier `acqViewR` is below the hart's index after
the fence (xv6's `main` spin loop executes `fence r,rw`). -/
def acqPredR (b : barrier_kind) : Prop :=
  ∀ ws : Wstate, acqViewR ws ≤ wsView (barrierPost ws b)

theorem acqPredR_rw_rw : acqPredR .Barrier_RISCV_rw_rw := fun ws => by
  rw [wsView_barrier_rw_rw]; exact acqViewR_acqView ws

theorem acqPredR_rw_r : acqPredR .Barrier_RISCV_rw_r := fun ws => by
  rw [wsView_barrier_rw_r]; exact acqViewR_acqView ws

theorem acqPredR_r_rw : acqPredR .Barrier_RISCV_r_rw := fun ws => by
  show acqViewR ws ≤ wsView (fencePost ws true false true true)
  rw [wsView_fence_r ws true]; exact Std.IsPreorder.le_refl _

theorem acqPredR_r_r : acqPredR .Barrier_RISCV_r_r := fun ws => by
  rw [wsView_barrier_r_r]; exact Std.IsPreorder.le_refl _

/-- ... and the delivery itself, at any such kind. -/
theorem viewScl_acqPredR (b : barrier_kind) (ws : Wstate) (t : Nat) :
    acqPredR b → t ≤ ws.wVrOld → viewScl t ≤ wsView (barrierPost ws b) := fun hb ht =>
  Std.IsPreorder.le_trans _ _ _ (viewScl_acq_vrOld ws t ht) (hb ws)

/-! ## 2. `∇` at the `vwpHold` altitude, and the fence rule -/

section Fence
variable {GF : BundledGFunctors}

/-- "`P` holds at the frontier a succ-R fence will deliver to this hart." -/
def vwpAcq (P : VProp GF) (ws : Wstate) : IProp GF := P.monPred_at (acqView ws)

def vwpAcqR (P : VProp GF) (ws : Wstate) : IProp GF := P.monPred_at (acqViewR ws)

theorem vwpAcq_ne (ws : Wstate) : OFE.NonExpansive (fun P : VProp GF => vwpAcq P ws) :=
  ⟨fun _ _ _ h => dist_at.mp h _⟩

theorem vwpAcq_mono' (ws : Wstate) {P Q : VProp GF} (h : P ⊢ Q) : vwpAcq P ws ⊢ vwpAcq Q ws :=
  entails_at.mp h _

/-- THE FENCE RULE: `∇P` before a `fence rw,rw` is `P` after it. -/
theorem vwpAcq_fence (P : VProp GF) (ws : Wstate) (sw : Bool) :
    vwpAcq P ws ⊢ vwpHold P (fencePost ws true true true sw) := by
  unfold vwpAcq vwpHold; rw [wsView_fence_rw]

theorem vwpAcq_barrier (P : VProp GF) (ws : Wstate) :
    vwpAcq P ws ⊢ vwpHold P (barrierPost ws .Barrier_RISCV_rw_rw) := by
  unfold vwpAcq vwpHold; rw [wsView_barrier_rw_rw]

theorem vwpAcqR_fence (P : VProp GF) (ws : Wstate) (sw : Bool) :
    vwpAcqR P ws ⊢ vwpHold P (fencePost ws true false true sw) := by
  unfold vwpAcqR vwpHold; rw [wsView_fence_r]

theorem vwpAcqR_barrier (P : VProp GF) (ws : Wstate) :
    vwpAcqR P ws ⊢ vwpHold P (barrierPost ws .Barrier_RISCV_r_r) := by
  unfold vwpAcqR vwpHold; rw [wsView_barrier_r_r]

/-- ... and the trivial direction: a fence never LOSES anything. -/
theorem vwpHold_acq (P : VProp GF) (ws : Wstate) : vwpHold P ws ⊢ vwpAcq P ws :=
  P.monPred_mono (wsView_acqView ws)

theorem vwpAcqR_acq (P : VProp GF) (ws : Wstate) : vwpAcqR P ws ⊢ vwpAcq P ws :=
  P.monPred_mono (acqViewR_acqView ws)

/-- THE INTRODUCTION FORM a leaf uses: an assertion frozen at a view the frontier covers is
`∇`-held. -/
theorem vwpAcq_intro (V : View) (P : VProp GF) (ws : Wstate) (h : V ≤ acqView ws) :
    P.monPred_at V ⊢ vwpAcq P ws :=
  P.monPred_mono h

theorem vwpAcqR_intro (V : View) (P : VProp GF) (ws : Wstate) (h : V ≤ acqViewR ws) :
    P.monPred_at V ⊢ vwpAcqR P ws :=
  P.monPred_mono h

theorem vwpAcq_view_at (P : VProp GF) (V : View) (ws : Wstate) :
    vwpAcq (P @@ V) ws ⊣⊢ P.monPred_at V := .rfl

/-- The structural laws — all `monPred_at` unfoldings, as at `vwpHold`. -/
theorem vwpAcq_sep (P Q : VProp GF) (ws : Wstate) :
    vwpAcq iprop(P ∗ Q) ws ⊣⊢ vwpAcq P ws ∗ vwpAcq Q ws := .rfl
theorem vwpAcq_exist {A : Type _} (Φ : A → VProp GF) (ws : Wstate) :
    vwpAcq iprop(∃ x, Φ x) ws ⊣⊢ ∃ x, vwpAcq (Φ x) ws := monPred_at_exist _ Φ
theorem vwpAcq_pure (φ : Prop) (ws : Wstate) : vwpAcq (iprop(⌜φ⌝) : VProp GF) ws ⊣⊢ ⌜φ⌝ := .rfl
theorem vwpAcq_embed (R : IProp GF) (ws : Wstate) : vwpAcq (iprop(⎡R⎤) : VProp GF) ws ⊣⊢ R :=
  .rfl

/-- THE READER-SIDE PACKAGE: an assertion deposited at the SCALAR view of a timestamp this hart has
read is delivered by a succ-R fence. -/
theorem fence_delivers_scl (P : VProp GF) (ws : Wstate) (t : Nat) (sw : Bool)
    (ht : t ≤ ws.wVrOld) :
    P.monPred_at (viewScl t) ⊢ vwpHold P (fencePost ws true false true sw) :=
  (vwpAcqR_intro _ P ws (viewScl_acq_vrOld ws t ht)).trans (vwpAcqR_fence P ws sw)

end Fence

/-! ## 3. The writer side: the release deposit

A store lands at `log.length + 1`, which DOMINATES the whole of the releaser's index (`wsBounded`),
so the releaser may freeze anything it holds at the single SCALAR view `viewScl (log.length + 1)`:
the Decision-5 scalar-deposit argument, as a lemma. -/

theorem wsBounded_viewScl (ws : Wstate) (n : Nat) (hb : wsBounded ws n) :
    wsView ws ≤ viewScl n := fun a => by
  rw [flr_wsView, flr_scl_eq]; exact wsBoundedScl ws n hb a

theorem wsView_store_dom (ws : Wstate) (log : List Wmsg) (hb : wsBounded ws log.length) :
    wsView ws ≤ viewScl (log.length + 1) := fun a => by
  rw [flr_wsView, flr_scl_eq]
  have := wsBoundedScl ws log.length hb a
  omega

section Release
variable {GF : BundledGFunctors}

/-- THE DEPOSIT.  Everything the releaser holds becomes an OBJECTIVE `P @@ viewScl t` at the
timestamp its store is about to take. -/
theorem release_deposit (P : VProp GF) (ws : Wstate) (log : List Wmsg)
    (hb : wsBounded ws log.length) :
    vwpHold P ws ⊢ P.monPred_at (viewScl (log.length + 1)) :=
  P.monPred_mono (wsView_store_dom ws log hb)

theorem release_deposit_at (P : VProp GF) (ws : Wstate) (log : List Wmsg)
    (hb : wsBounded ws log.length) :
    vwpHold P ws ⊢ vwpHold (P @@ viewScl (log.length + 1)) ws :=
  (release_deposit P ws log hb).trans (vwpHold_view_at P _ ws).mpr

end Release

/-! ## 4. The AMO read half -/

/-- THE ACQUIRE'S INDEX GAIN.  An acquire read of timestamp `t` raises the hart's SCALAR floor to
`t`, so it delivers everything deposited at `viewScl t` — with no fence. -/
theorem amo_acq_gain (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    viewScl t ≤ wsView (loadPostAt ws true vpre a t) := fun a' => by
  rw [flr_scl_eq, flr_wsView]
  have := loadPostAtVrNewAq ws vpre a t
  omega

/-- A PLAIN load gains the timestamp only at the BYTE it read (its coherence floor), which is what
makes MP need the fence. -/
theorem load_byte_gain (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    viewByte a t ≤ wsView (loadPostAt ws aq vpre a t) := by
  rw [viewByte_le, flr_wsView]
  have := loadPostAtCoh ws aq vpre a t
  omega

section Amo
variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE AMO READ RULE, base altitude.  An `akLatest` access must read the global latest write, so
an element of the latest-write map pins BOTH the value and the timestamp — with NO hypothesis about
the reader's views (so it fires off an element held in an INVARIANT). -/
theorem wamo_read_latest (σ : Wmstate) (ak : AkInfo) (a : Int) (dq : DFrac) (t : Nat)
    (v : BitVec 8) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    ak.akLatest = true →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ wlatPointsto (GF := GF) a dq t v ⊢
      ⌜t' = t ∧ b = v⌝ := by
  intro hcoh hlatk hok
  refine (wlatLookup σ.wmImg σ.wmLog a dq t v).trans (pure_mono fun hlat => ?_)
  obtain ⟨hv, hadm⟩ := hok
  rw [hcoh] at hadm
  obtain ⟨-, hlt⟩ := hadm
  have ht' : t' = t :=
    latestUnique (wimg σ) σ.wmLog a t' t ⟨by rw [hv]; rfl, hlt hlatk⟩
      (latestValLatest _ _ _ _ _ hlat)
  refine ⟨ht', ?_⟩
  subst ht'
  have h1 : some b = some v := hv.symm.trans hlat.1
  exact Option.some.inj h1

/-- ... and the owned form, at the `VProp` altitude: the AMO returns the value of the byte I own. -/
theorem wpt_amo_read (σ : Wmstate) (ak : AkInfo) (a : Int) (dq : DFrac) (v : BitVec 8) (t' : Nat)
    (b : BitVec 8) :
    ak.akIfetch = false →
    ak.akLatest = true →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wpt (GF := GF) a dq v) σ.wmWs ⊢ ⌜b = v⌝ := by
  intro hcoh hlatk hok
  refine (sep_mono_right (wpt_at a dq v σ.wmWs).mp).trans ?_
  iintro ⟨Hi, ⟨%t, He, -⟩⟩
  ihave %h := wamo_read_latest σ ak a dq t v t' b hcoh hlatk hok $$ [Hi He]
  · iframe Hi He
  ipureintro; exact h.2

/-- The post-state seen-assertion the acquire produces: after an acquire read of timestamp `t`,
the hart has observed the SCALAR view `viewScl t`. -/
theorem wpt_amo_seen (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    ⊢ vwpHold (⊒(viewScl t) : VProp GF) (loadPostAt ws true vpre a t) := by
  exact (pure_intro (amo_acq_gain ws vpre a t)).trans (vwpHold_seen _ _).mpr

end Amo

/-! ## 5. THE HANDOFF — what M3 will quote -/

section Handoff
variable {GF : BundledGFunctors}

/-- RELEASE → ACQUIRE (the spinlock).  Whatever the releasing hart held at its own index when its
store took timestamp `log.length + 1`, the acquiring hart holds after an acquire-AMO that reads that
timestamp.  No invariant, no ghost state, no fence. -/
theorem release_acquire_transfer (P : VProp GF) (wsR wsA : Wstate) (log : List Wmsg) (vpre : Nat)
    (a' : Int) (hb : wsBounded wsR log.length) :
    vwpHold P wsR ⊢ vwpHold P (loadPostAt wsA true vpre a' (log.length + 1)) :=
  (release_deposit P wsR log hb).trans (P.monPred_mono (amo_acq_gain _ _ _ _))

/-- RELEASE → PLAIN READ + succ-R FENCE (the `started` escrow, MP). -/
theorem release_fence_transfer (P : VProp GF) (wsR wsA : Wstate) (log : List Wmsg) (sw : Bool)
    (hb : wsBounded wsR log.length) (ht : log.length + 1 ≤ wsA.wVrOld) :
    vwpHold P wsR ⊢ vwpHold P (fencePost wsA true false true sw) :=
  (release_deposit P wsR log hb).trans (fence_delivers_scl P wsA _ sw ht)

end Handoff

/-! ## 6. Smoke test: the MP shape, composed at the machine's own steps -/

section MpSmoke
variable {GF : BundledGFunctors}

theorem mp_transfer (P : VProp GF) (wsW wsR : Wstate) (log : List Wmsg) (x y : Int) (rl : Bool)
    (vpre : Nat) (hb : wsBounded wsW log.length) (hfwd : wsR.wFwd = ∅) :
    vwpHold P wsW ⊢
      vwpHold P (fencePost (loadPostAt wsR false vpre y (log.length + 1)) true false true false) :=
  release_fence_transfer P wsW _ log false hb
    (loadPostAtVrOldNofwd wsR false vpre y (log.length + 1) hfwd)

/-- ... and the acquire variant, with no fence at all. -/
theorem mp_transfer_aq (P : VProp GF) (wsW wsR : Wstate) (log : List Wmsg) (y : Int) (vpre : Nat)
    (hb : wsBounded wsW log.length) :
    vwpHold P wsW ⊢ vwpHold P (loadPostAt wsR true vpre y (log.length + 1)) :=
  release_acquire_transfer P wsW wsR log vpre y hb

end MpSmoke

/-! ## 7. (Lean-only, O2 Stage B) `fence.i` and the instruction view

`fence.i` moves no DATA view, so it delivers nothing at the index; it raises the hart's instruction
view `wmItv` (`WeakInterp.itvPost`) past the data floor `wVrNew` and the hart's own last store
`wVwOld`.  So what the hart has ACQUIRED, or WRITTEN, becomes fetch-visible after `fence.i`. -/

theorem wsView_barrier_i (ws : Wstate) : wsView (barrierPost ws .Barrier_RISCV_i) = wsView ws := rfl

/-- `fence.i` is not a read-delivering fence (on the data views). -/
theorem acqPredR_not_i : ¬ acqPredR .Barrier_RISCV_i := by
  intro h
  let ws : Wstate := { wsInit with wVrOld := 1 }
  have := h ws 0
  rw [wsView_barrier_i, flr_wsView] at this
  simp [ws, acqViewR, flr, coh, wsInit, lookupEmpty] at this

theorem itvPost_fenceI_vrNew (ws : Wstate) (itv : Nat) :
    ws.wVrNew ≤ itvPost ws itv .Barrier_RISCV_i := by
  rw [itvPostI]; omega

theorem itvPost_fenceI_vwOld (ws : Wstate) (itv : Nat) :
    ws.wVwOld ≤ itvPost ws itv .Barrier_RISCV_i := by
  rw [itvPostI]; omega

/-- An acquire read of `t` followed by `fence.i` makes `t` visible to the i-cache. -/
theorem amo_acq_fenceI (ws : Wstate) (vpre : Nat) (a : Int) (t itv : Nat) :
    t ≤ itvPost (loadPostAt ws true vpre a t) itv .Barrier_RISCV_i :=
  Nat.le_trans (loadPostAtVrNewAq ws vpre a t) (itvPost_fenceI_vrNew _ itv)

/-- At the machine state: `fence.i` leaves the data index and raises `wmItv`. -/
theorem wbarrierPost_fenceI_ws (s : Wmstate) :
    wsView (wbarrierPost s .Barrier_RISCV_i).wmWs = wsView s.wmWs ∧
    max s.wmWs.wVrNew s.wmWs.wVwOld ≤ (wbarrierPost s .Barrier_RISCV_i).wmItv := by
  refine ⟨rfl, ?_⟩
  rw [wbarrierPostItv, itvPostI]; omega

end Weak
