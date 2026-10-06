/-
Weak: **what goes IN a lock invariant**, and the two one-line conversions at acquire and release —
the published points-to `wptPub T a dq v` ("the element, published no later than `T`"), its
identification with the points-to frozen at the scalar view `viewScl T` (`wptPubFrozen`), the
seam `cobjPtAcquire` / `cobjPtRelease`, their region forms over `[∗map]`, and the end-to-end
handoff between two contexts (`cobjPtRegionHandoff`).

Rocq: `iris/WeakPtPub.v` @ xxvzwolszwmp (1cc222280).

Rocq header (in substance, Rocq vocabulary).  An objective points-to carries a floor, and a floor
is a statement about somebody's view — so a whole objective points-to must NOT go in a shared
invariant.  THE LOCK ALREADY HOLDS THE RIGHT THING: [WeakLock]'s invariant carries [monPred_at R V]
— the payload frozen at a view — at the timestamp the releaser's store takes and the acquirer's
[amoswap.w.aq] reads.  Computing that frozen payload for a points-to gives, at [view_scl T],

  [monPred_at (a ↦w{dq} v) (view_scl T)  ⊣⊢  ∃ t, ⌜t ≤ T⌝ ∗ wlat_pointsto a dq t v]

which is objective, hart-free, CONTEXT-free: [wpt_pub T a dq v].  IT IS NOT A NEW CONSTRUCT.  The
seam is two conversions: RELEASE [cobj ξA] → [wpt_pub T] (side condition [∀ a, flr V a ≤ T]) and
ACQUIRE [wpt_pub T] → [cobj ξB] (side condition [∀ a, T ≤ flr V a], the SCALAR gain
[WeakFence.amo_acq_gain] delivers — quantified over EVERY byte, which is the formal content of "the
scalar is the whole difference between an acquire and a plain load").  The release bound is over
all addresses because [cobj ξ R] existentially quantifies the view and has no footprint; for a
REGION the two coincide.  What is assumed, not proved, is the identification of [T] across the
boundary — [WeakLock]'s existing protocol obligation — which is why [T] is a parameter here.

(The section comments of the Rocq file — §1 the points-to at an arbitrary frozen view, §2 the
published points-to, §3 the seam, §4 a whole region, §5 the handoff, "the only place two contexts
are named" — are kept on the corresponding Lean declarations below.)

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).  None of this file's names is in
   `notes/weak-port-dupnames.json`.
2. STATEMENT SHAPES (the `WeakGhost` deviation 9 / `WeakCtx` deviation 2 convention): Rocq
   `P -∗ Q` is `P ⊢ Q`, `P -∗ Q -∗ R` is `P ∗ Q ⊢ R`, `P -∗ Q -∗ R -∗ S` is `P ∗ Q ∗ R ⊢ S`;
   `monPred_at R V` is `R.monPred_at V`; `view_scl` is `viewScl`.
3. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped (nothing here uses it); the ghost
   state is `[WeakGS GF]` (which supplies `WeakCtx`'s `[WeakViewG GF]` through `WeakGS.pre`).
4. `Z` is `Int`, `bv 8` is `BitVec 8`, `dfrac` is `DFrac`, `DfracDiscarded` is `DFrac.discard`,
   `gmap Z (bv 8)` is `GMapF Int (BitVec 8)`; `[∗ map]` is iris-lean's `[∗map]`.
5. `wpt_view_at` is literally `WeakVProp.wpt_at_view` (the Rocq file re-proves `wpt_at`'s
   argument at an arbitrary view; the Lean `WeakVProp` already states it there), so it is that
   theorem.
6. `wpt_pub_timeless` / `wpt_pub_persistent` (Rocq `Global Instance`s) are Lean `instance`s.

**Rocq → Lean name map.**  §1 `wpt_view_at`→`wptViewAt`.  §2 `wpt_pub`→`wptPub`,
`wpt_pub_timeless`→`wptPubTimeless`, `wpt_pub_persistent`→`wptPubPersistent`, `wpt_pub_frozen`→
`wptPubFrozen`, `wpt_pub_mono`→`wptPubMono`, `wpt_pub_unfold`→`wptPubUnfold`, `wpt_pub_0`→
`wptPub0`.  §3 `cobj_pt_acquire`→`cobjPtAcquire`, `cobj_pt_release`→`cobjPtRelease`.  §4
`wpt_pub_region`→`wptPubRegion`, `cobj_pt_region`→`cobjPtRegion`, `cobj_pt_region_acquire`→
`cobjPtRegionAcquire`, `cobj_pt_region_release`→`cobjPtRegionRelease`.  §5
`cobj_pt_region_handoff`→`cobjPtRegionHandoff`.

**Not ported:** nothing.

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakCtx
import Weak.WeakVProp
import Weak.WeakView
import MachCSL.StdppMap
import MachCSL.MonPredExtra

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

section pub

variable {GF : BundledGFunctors} [WeakGS GF]

/-! ## 1. The points-to at an arbitrary frozen view

`WeakVProp.wpt_at` is this at `wsView ws`; the invariant needs it at `viewScl T`, so here it is in
general (deviation 5). -/

theorem wptViewAt (a : Int) (dq : DFrac) (v : BitVec 8) (V : View) :
    (wpt (GF := GF) a dq v).monPred_at V ⊣⊢
      ∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ⌜t ≤ flr V a⌝ :=
  wpt_at_view a dq v V

/-! ## 2. The published points-to — what the invariant holds -/

/-- "The element, published no later than `T`."  Objective, hart-free, context-free, and
admissible in a shared invariant. -/
def wptPub (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8) : IProp GF :=
  iprop(∃ t : Nat, ⌜t ≤ T⌝ ∗ wlatPointsto (GF := GF) a dq t v)

instance wptPubTimeless (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8) :
    Timeless (wptPub (GF := GF) T a dq v) := by
  unfold wptPub; infer_instance

instance wptPubPersistent (T : Nat) (a : Int) (v : BitVec 8) :
    Persistent (wptPub (GF := GF) T a DFrac.discard v) := by
  unfold wptPub; infer_instance

/-- THE POINT: `wptPub` is not a new construct, it is the normal form of the payload `WeakLock`
already freezes at `viewScl T`. -/
theorem wptPubFrozen (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8) :
    (wpt (GF := GF) a dq v).monPred_at (viewScl T) ⊣⊢ wptPub T a dq v := by
  refine (wptViewAt a dq v (viewScl T)).trans ?_
  unfold wptPub
  rw [flr_scl_eq]
  constructor
  · iintro ⟨%t, He, %h⟩
    iexists t
    iframe He
    ipureintro; exact h
  · iintro ⟨%t, %h, He⟩
    iexists t
    iframe He
    ipureintro; exact h

/-- A later deposit publishes no less. -/
theorem wptPubMono (T T' : Nat) (a : Int) (dq : DFrac) (v : BitVec 8) (hle : T ≤ T') :
    wptPub (GF := GF) T a dq v ⊢ wptPub T' a dq v := by
  unfold wptPub
  iintro ⟨%t, %ht, He⟩
  iexists t
  iframe He
  ipureintro; omega

theorem wptPubUnfold (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8) :
    wptPub (GF := GF) T a dq v ⊣⊢ ∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ⌜t ≤ T⌝ := by
  unfold wptPub
  constructor
  · iintro ⟨%t, %h, He⟩
    iexists t
    iframe He
    ipureintro; exact h
  · iintro ⟨%t, He, %h⟩
    iexists t
    iframe He
    ipureintro; exact h

/-- `wptPub 0` IS the era-image points-to: the element at timestamp 0, which is
`WeakVProp.wptImg`'s body.  So `wptPub` is the generalisation of `wptImg` from "never written" to
"published no later than `T`", and it is at `T = 0` — and only there — that the invariant's
resource needs no synchronisation to localise, because a floor of 0 is below every view at every
byte. -/
theorem wptPub0 (a : Int) (dq : DFrac) (v : BitVec 8) :
    wptPub (GF := GF) 0 a dq v ⊣⊢ wlatPointsto (GF := GF) a dq 0 v := by
  unfold wptPub
  constructor
  · iintro ⟨%t, %ht, He⟩
    have h0 : t = 0 := by omega
    subst h0
    iexact He
  · iintro He
    iexists 0
    iframe He
    ipureintro; exact Nat.le_refl 0

/-! ## 3. THE SEAM, in two lemmas

Both are one line on top of `WeakCtx`'s generic `cobjAcquire` / `cobjRelease` plus
`wptPubFrozen`'s identification — the evidence that the seam really is generic in the payload and
that a points-to is not a special case.  A lock whose payload is an arbitrary `VProp` uses
`cobjAcquire`/`cobjRelease` directly; these two exist because the points-to is the payload
everyone writes first. -/

/-- ACQUIRE.  The published element plus the acquiring context's gain IS that context's objective
points-to.  The client never sees a view: this is the whole of "the lock pays the weak-memory cost
once, on behalf of every client". -/
theorem cobjPtAcquire (ξ : CtxId) (V : View) (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8)
    (hT : ∀ b, T ≤ flr V b) :
    ctxAuth (GF := GF) ξ V ∗ wptPub T a dq v ⊢ ctxAuth ξ V ∗ cobj ξ (wpt a dq v) :=
  (sep_mono_right (wptPubFrozen T a dq v).mpr).trans (cobjAcquire ξ V T _ hT)

/-- RELEASE.  The releasing context's own floor bounds its elements, so publishing at any `T`
above that floor is sound.  `T` is the releasing store's timestamp; `WeakInstr.wwp_release_deposit`
is where it comes from. -/
theorem cobjPtRelease (ξ : CtxId) (V : View) (T : Nat) (a : Int) (dq : DFrac) (v : BitVec 8)
    (hT : ∀ b, flr V b ≤ T) :
    ctxAuth (GF := GF) ξ V ∗ cobj ξ (wpt a dq v) ⊢ ctxAuth ξ V ∗ wptPub T a dq v :=
  (cobjRelease ξ V T _ hT).trans (sep_mono_right (wptPubFrozen T a dq v).mp)

/-! ## 4. A whole protected region

A lock protects bytes, not a byte.  Both conversions commute with `[∗map]` for free — the acquire
because one scalar floor serves every byte (again: the SCALAR is what an acquire gains), the
release because the bound is already stated at every address. -/

def wptPubRegion (T : Nat) (dq : DFrac) (m : GMapF Int (BitVec 8)) : IProp GF :=
  iprop([∗map] a ↦ v ∈ m, wptPub (GF := GF) T a dq v)

def cobjPtRegion (ξ : CtxId) (dq : DFrac) (m : GMapF Int (BitVec 8)) : IProp GF :=
  iprop([∗map] a ↦ v ∈ m, cobj ξ (wpt (GF := GF) a dq v))

theorem cobjPtRegionAcquire (ξ : CtxId) (V : View) (T : Nat) (dq : DFrac)
    (m : GMapF Int (BitVec 8)) (hT : ∀ b, T ≤ flr V b) :
    ctxAuth (GF := GF) ξ V ∗ wptPubRegion T dq m ⊢ ctxAuth ξ V ∗ cobjPtRegion ξ dq m := by
  unfold wptPubRegion cobjPtRegion
  refine mapInd (P := fun m : GMapF Int (BitVec 8) =>
    (ctxAuth (GF := GF) ξ V ∗ iprop([∗map] a ↦ v ∈ m, wptPub (GF := GF) T a dq v)) ⊢
      ctxAuth ξ V ∗ iprop([∗map] a ↦ v ∈ m, cobj ξ (wpt (GF := GF) a dq v))) ?_ ?_ m
  · iintro ⟨Ha, -⟩
    iframe Ha
    iapply (BigSepM.bigSepM_empty (M := GMapF Int)
      (Φ := fun a v => cobj (GF := GF) ξ (wpt (GF := GF) a dq v))).mpr
    iempintro
  · intro a v m hnew IH
    rw [(BigSepM.bigSepM_insert (Φ := fun a v => wptPub (GF := GF) T a dq v) hnew).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun a v => cobj (GF := GF) ξ (wpt (GF := GF) a dq v))
        hnew).to_eq]
    iintro ⟨Ha, Hp, Hm⟩
    ihave ⟨Ha, Hc⟩ := cobjPtAcquire ξ V T a dq v hT $$ [Ha Hp]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hp
    ihave ⟨Ha, Hm⟩ := IH $$ [Ha Hm]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hm
    iframe Ha Hc Hm

theorem cobjPtRegionRelease (ξ : CtxId) (V : View) (T : Nat) (dq : DFrac)
    (m : GMapF Int (BitVec 8)) (hT : ∀ b, flr V b ≤ T) :
    ctxAuth (GF := GF) ξ V ∗ cobjPtRegion ξ dq m ⊢ ctxAuth ξ V ∗ wptPubRegion T dq m := by
  unfold wptPubRegion cobjPtRegion
  refine mapInd (P := fun m : GMapF Int (BitVec 8) =>
    (ctxAuth (GF := GF) ξ V ∗ iprop([∗map] a ↦ v ∈ m, cobj ξ (wpt (GF := GF) a dq v))) ⊢
      ctxAuth ξ V ∗ iprop([∗map] a ↦ v ∈ m, wptPub (GF := GF) T a dq v)) ?_ ?_ m
  · iintro ⟨Ha, -⟩
    iframe Ha
    iapply (BigSepM.bigSepM_empty (M := GMapF Int)
      (Φ := fun a v => wptPub (GF := GF) T a dq v)).mpr
    iempintro
  · intro a v m hnew IH
    rw [(BigSepM.bigSepM_insert (Φ := fun a v => wptPub (GF := GF) T a dq v) hnew).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun a v => cobj (GF := GF) ξ (wpt (GF := GF) a dq v))
        hnew).to_eq]
    iintro ⟨Ha, Hc, Hm⟩
    ihave ⟨Ha, Hp⟩ := cobjPtRelease ξ V T a dq v hT $$ [Ha Hc]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hc
    ihave ⟨Ha, Hm⟩ := IH $$ [Ha Hm]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hm
    iframe Ha Hp Hm

end pub

/-! ## 5. THE HANDOFF, end to end — THE ONLY PLACE TWO CONTEXTS ARE NAMED.

Everywhere else the context is a parameter threaded through one execution.  Here it cannot be,
because the whole content of the lemma is that the region CHANGES HANDS.  When the objective layer
was indexed by a HART (`WeakPtOwn`, deleted) the same statement took two `CpuId`s and two
`ws_auth`s and needed both authorities present in a single step — exactly what a real handoff
through an invariant denies.  Here the two halves split cleanly — `cobjPtRegionRelease` under ξA
at release time, `cobjPtRegionAcquire` under ξB at acquire time — and this lemma composes them
only to state the end-to-end shape. -/

section handoff

variable {GF : BundledGFunctors} [WeakGS GF]

/-- Context A holds the region objectively and releases at `T`; the region sits in the invariant
as `wptPubRegion T`, with no context named and no view crossing the boundary; context B's acquire
gains `viewScl T` and takes the region out objectively.  This is the shape a lock's client-facing
spec should have: `cobj` in, `cobj` out, weak memory confined to the two conversions of §3.
`hT`: the releaser's floor is below the timestamp its store takes; `hacq`: exactly what the
acquirer's `amo_acq_gain` delivers, `viewScl T ≤ VB` unfolded by `flr_scl_eq`. -/
theorem cobjPtRegionHandoff (ξA ξB : CtxId) (VA VB : View) (T : Nat) (dq : DFrac)
    (m : GMapF Int (BitVec 8)) (hT : ∀ a, flr VA a ≤ T) (hacq : ∀ a, T ≤ flr VB a) :
    ctxAuth (GF := GF) ξA VA ∗ ctxAuth ξB VB ∗ cobjPtRegion ξA dq m ⊢
      ctxAuth ξA VA ∗ ctxAuth ξB VB ∗ cobjPtRegion ξB dq m := by
  iintro ⟨HA, HB, Hm⟩
  ihave ⟨HA, Hpub⟩ := cobjPtRegionRelease ξA VA T dq m hT $$ [HA Hm]
  · isplitl [HA]
    · iexact HA
    · iexact Hm
  ihave ⟨HB, Hm⟩ := cobjPtRegionAcquire ξB VB T dq m hacq $$ [HB Hpub]
  · isplitl [HB]
    · iexact HB
    · iexact Hpub
  iframe HA HB Hm

end handoff

end Weak
