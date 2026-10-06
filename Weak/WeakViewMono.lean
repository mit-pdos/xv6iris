/-
Weak: **the hart's weak state as MONOTONE ghost state** (PROTOTYPE), so it can be threaded as
an OPAQUE token with persistent lower bounds.

Rocq: `iris/WeakViewMono.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary):

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §2 — this file is
    obligation 1 of §5.  NOT wired into anything yet; [WeakGhost.hart_ws] is
    still the exact-valued [ghost_var] the tree uses.

    THE POINT.  [WeakGhost.hart_ws c ws := ghost_var (weak_ws_name c) (1/2) ws]
    is EXACT-valued, and a [ghost_var] can only be updated by naming both the
    old and the new value.  That is the sole reason every leaf reads [ws] in,
    [ws'] out, and carries [⌜ws_le ws ws'⌝] — even for an instruction that
    touches no data, since every instruction fetches its own text and the
    fetch is a view-raising weak read.  [ws_le] is pointwise [≤] on every
    field with no non-monotone component, so the state is a product of
    monotone pieces and the exactness is simply not needed above a leaf.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).
2. CAMERAS.  iris-lean has no `gFunctors` lists and no `subG`: a camera is an `ElemG GF F`
   instance field of a class over `GF : BundledGFunctors` (the `MachCSL.Resources` precedent).
   So
   * `weakViewScalarG`'s SEVEN `mono_natG` fields collapse into ONE `MonoNatG GF` field: the
     seven floors are seven ghost NAMES (`WsNames`) in one camera, exactly as the tree's own
     `MachFixedGS.mono` serves every counter.  (Rocq's seven fields were all discharged from
     the same `mono_natΣ` anyway.)
   * `weakViewG`'s `inG Σ (authR cohUR)` / `inG Σ (authR ctxwrUR)` are
     `ElemG GF CohRF` / `ElemG GF CtxwrRF`, with `CohRF := constOF (Auth CohUR)` and
     `CtxwrRF := constOF (Auth CtxwrUR)` (the `MachCSL.CtxBox.StampsRF` pattern).
   * `weakViewΣ`, `subG_weakViewScalarG`, `subG_weakViewG` are NOT PORTED: superseded by
     the classes, as iris-lean's own `#rocq_ignore mono_natΣ`/`subG_mono_natΣ` record.
3. `cohUR := discrete_funUR (λ _ : Z, max_natUR)` is `CohUR := Int → MaxNat` (iris-lean's
   `ucmraDiscreteFunO` instance); `ctxwrUR := gmapUR nat max_natUR` is
   `CtxwrUR := GMapF Nat MaxNat` (iris-lean's `Heap.instStoreUCMRA`).  `MaxNat t` is
   `MaxNat.ofNat t`.  iris-lean's `MaxNat` instances are `scoped` in `Iris`: a client of
   these cameras must `open Iris`.
4. STATEMENT SHAPES: Rocq `P -∗ Q` is `P ⊢ Q`, `P -∗ Q -∗ ⌜φ⌝` is `P ∗ Q ⊢ ⌜φ⌝`, and
   `P ==∗ Q` is `P ⊢ |==> Q` (the `WeakView` / `WeakVProp` convention).
5. `coh_fun_incl` is proved through iris-lean's `DiscreteFun.inc_iff` (pointwise inclusion,
   proved by choice upstream) — the header note on `Finite` below no longer applies; the
   statement is unchanged.
6. Lean-only helper (no Rocq twin): the private `cohValidInc`, the inclusion step that
   `coh_lb_valid` and `ws_coh_lb_valid` both inline in Rocq.
7. `ws_alloc_cpus`'s `EqDecision A` is `DecidableEq A`; `NoDup cs` is `cs.Nodup`; the dummy
   names for the empty list are all `0` (Rocq `1%positive`; iris-lean `GName = Nat`).

**Drift:** none (no SC dependency).

**Name map** (Rocq → Lean): `weakViewScalarG`→`WeakViewScalarG` (field `mono`, deviation 2),
`ws_names`/`WsNames`→`WsNames`/`WsNames.mk` (fields `wsn_X`→`wsnX`), `ws_scal_auth`→
`wsScalAuth`, `ws_scal_lb`→`wsScalLb`, `ws_scal_lb_persistent`→`wsScalLbPersistent`,
`ws_scal_lb_get`→`wsScalLbGet`, `ws_scal_update`→`wsScalUpdate`, `ws_scal_lb_valid`→
`wsScalLbValid`, `cohUR`→`CohUR`, `coh_fun`→`cohFun`, `coh_fun_incl`→`cohFunIncl`,
`coh_fun_local_update`→`cohFunLocalUpdate`, `coh_fun_core_id`→`cohFunCoreId`, `ctxwrUR`→
`CtxwrUR`, (new) `CohRF`/`CtxwrRF`, `weakViewG`→`WeakViewG` (fields `wv_scal/coh/wr`→
`wvScal/wvCoh/wvWr`), `wview_names`/`WvNames`→`WviewNames`/`WviewNames.mk` (fields
`wvnScal`/`wvnCoh`), `ws_coh_auth`→`wsCohAuth`, `ws_coh_lb`→`wsCohLb`, `ws_auth`→`wsAuth`,
`ws_lb`→`wsLb`, `ws_coh_lb_persistent`→`wsCohLbPersistent`, `ws_lb_persistent`→
`wsLbPersistent`, `ws_lb_timeless`→`wsLbTimeless`, `ws_coh_lb_get`→`wsCohLbGet`,
`ws_lb_get`→`wsLbGet`, `ws_coh_update`→`wsCohUpdate`, `ws_update`→`wsUpdate`, `coh_lb`→
`cohLb`, `coh_lb_persistent`→`cohLbPersistent`, `coh_lb_timeless`→`cohLbTimeless`,
`coh_lb_valid`→`cohLbValid`, `coh_lb_le`→`cohLbLe`, `coh_lb_get`→`cohLbGet`,
`ws_coh_lb_valid`→`wsCohLbValid`, `ws_lb_valid`→`wsLbValid`, `ws_lb_mono`→`wsLbMono`,
`ws_alloc`→`wsAlloc`, `wview_tok`→`wviewTok`, `wview_tok_intro`→`wviewTokIntro`,
`wview_tok_step`→`wviewTokStep`, `wview_tok_snapshot`→`wviewTokSnapshot`,
`ws_alloc_cpus`→`wsAllocCpus`.

**Not ported:** `weakViewΣ`, `subG_weakViewScalarG`, `subG_weakViewG` (deviation 2;
superseded by the `ElemG` classes — uses checked: `weakViewΣ` is consumed only by Rocq
`WeakAdequacy`'s Σ list, whose Lean port lists the class instead).

**Statements checked** (diffed against Rocq by hand): every lemma above.
-/
import Weak.WeakMem
import Iris.BI.Lib.MonoNat
import Iris.Algebra.Functions
import Iris.Algebra.Heap
import Iris.Std.HeapInstances
import Iris.ProofMode
import Iris.Instances.IProp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. The seven scalar floors.

`wVrOld` / `wVwOld` / `wVrNew` / `wVwNew` / `wVRel` / `wPub` / `wVcap` are plain `Nat`s
ordered by `≤`, i.e. seven `mono_nat`s.  This half is entirely standard and uses the same
library the tree already uses (`MachFixedGS.mono`).

`wPub` (M6's inert publication watermark, D-M6-6) joined the list with the field sweep: it is
a monotone component of `wsLe` exactly like the other five, so it rides the same pattern.  Its
SIBLING `wRelp` does NOT appear here and must not: it toggles (set by a `pw ∧ sw` fence,
cleared by the next store), so it is deliberately absent from `wsLe`.

`wVcap` (PARM's control view, D2) joined with the dependency track, for the same reason:
`loadPostRunD`/`storePostRunD`/`ctrlPost` only ever JOIN into it, so it is a conjunct of
`wsLe`.  Its two D2 siblings `wRegv` and `wLdv` do NOT appear here and must not, exactly as
`wRelp` does not: `regwPost` OVERWRITES a register's view and `instrPost` RESETS `wLdv`, so
neither is monotone (see `WeakMem`'s `wsLe` note, where the refutation is spelled out). -/

/-- The scalar floors' camera (deviation 2: one `MonoNatG`, seven names). -/
class WeakViewScalarG (GF : BundledGFunctors) where
  mono : MonoNatG GF

attribute [reducible, instance] WeakViewScalarG.mono

/-- The seven floors' ghost names. -/
structure WsNames where
  wsnVrOld : GName
  wsnVwOld : GName
  wsnVrNew : GName
  wsnVwNew : GName
  wsnVRel : GName
  wsnPub : GName
  wsnVcap : GName

section scalars

variable {GF : BundledGFunctors} [WeakViewScalarG GF]

/-- The AUTHORITY on the scalars, at an exact state — internal. -/
def wsScalAuth (γ : WsNames) (w : Wstate) : IProp GF := iprop(
  MonoNat.auth_own γ.wsnVrOld (DFrac.own 1) (.ofNat w.wVrOld) ∗
  MonoNat.auth_own γ.wsnVwOld (DFrac.own 1) (.ofNat w.wVwOld) ∗
  MonoNat.auth_own γ.wsnVrNew (DFrac.own 1) (.ofNat w.wVrNew) ∗
  MonoNat.auth_own γ.wsnVwNew (DFrac.own 1) (.ofNat w.wVwNew) ∗
  MonoNat.auth_own γ.wsnVRel (DFrac.own 1) (.ofNat w.wVRel) ∗
  MonoNat.auth_own γ.wsnPub (DFrac.own 1) (.ofNat w.wPub) ∗
  MonoNat.auth_own γ.wsnVcap (DFrac.own 1) (.ofNat w.wVcap))

/-- The persistent LOWER BOUND — duplicable, and (the whole point) it survives every
intervening step for free, with no `vwpHold_mono`. -/
def wsScalLb (γ : WsNames) (w : Wstate) : IProp GF := iprop(
  MonoNat.lb_own γ.wsnVrOld (.ofNat w.wVrOld) ∗
  MonoNat.lb_own γ.wsnVwOld (.ofNat w.wVwOld) ∗
  MonoNat.lb_own γ.wsnVrNew (.ofNat w.wVrNew) ∗
  MonoNat.lb_own γ.wsnVwNew (.ofNat w.wVwNew) ∗
  MonoNat.lb_own γ.wsnVRel (.ofNat w.wVRel) ∗
  MonoNat.lb_own γ.wsnPub (.ofNat w.wPub) ∗
  MonoNat.lb_own γ.wsnVcap (.ofNat w.wVcap))

instance wsScalLbPersistent (γ : WsNames) (w : Wstate) : Persistent (wsScalLb (GF := GF) γ w) := by
  unfold wsScalLb; infer_instance

theorem wsScalLbGet (γ : WsNames) (w : Wstate) : wsScalAuth (GF := GF) γ w ⊢ wsScalLb γ w := by
  unfold wsScalAuth wsScalLb
  iintro ⟨H1, H2, H3, H4, H5, H6, H7⟩
  ihave #L1 := MonoNat.lb_own_get $$ H1
  ihave #L2 := MonoNat.lb_own_get $$ H2
  ihave #L3 := MonoNat.lb_own_get $$ H3
  ihave #L4 := MonoNat.lb_own_get $$ H4
  ihave #L5 := MonoNat.lb_own_get $$ H5
  ihave #L6 := MonoNat.lb_own_get $$ H6
  ihave #L7 := MonoNat.lb_own_get $$ H7
  iframe L1 L2 L3 L4 L5 L6 L7

/-- THE UPDATE.  Note what it does NOT need: the caller does not name the old state.  Any
`wsLe`-larger state is reachable, which is exactly the obligation a leaf can discharge
internally. -/
theorem wsScalUpdate (γ : WsNames) (w w' : Wstate) (h : wsLe w w') :
    wsScalAuth (GF := GF) γ w ⊢ |==> wsScalAuth γ w' := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold wsScalAuth
  iintro ⟨A1, A2, A3, A4, A5, A6, A7⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVrOld) (by simpa [MaxNat.le_toNat] using h1) $$ A1
    with ⟨A1, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVwOld) (by simpa [MaxNat.le_toNat] using h2) $$ A2
    with ⟨A2, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVrNew) (by simpa [MaxNat.le_toNat] using h3) $$ A3
    with ⟨A3, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVwNew) (by simpa [MaxNat.le_toNat] using h4) $$ A4
    with ⟨A4, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVRel) (by simpa [MaxNat.le_toNat] using h5) $$ A5
    with ⟨A5, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wPub) (by simpa [MaxNat.le_toNat] using h6) $$ A6
    with ⟨A6, -⟩
  imod MonoNat.own_update _ _ (.ofNat w'.wVcap) (by simpa [MaxNat.le_toNat] using h7) $$ A7
    with ⟨A7, -⟩
  imodintro
  iframe A1 A2 A3 A4 A5 A6 A7

/-- The lower bound is SOUND: what it tells you is a floor, which is the direction owned memory
needs (knowing your view is AT LEAST `w` is what rules out reading stale; a larger real view
only makes reads fresher). -/
theorem wsScalLbValid (γ : WsNames) (w w0 : Wstate) :
    wsScalAuth (GF := GF) γ w ∗ wsScalLb γ w0 ⊢
      ⌜w0.wVrOld ≤ w.wVrOld ∧ w0.wVwOld ≤ w.wVwOld ∧
       w0.wVrNew ≤ w.wVrNew ∧ w0.wVwNew ≤ w.wVwNew ∧
       w0.wVRel ≤ w.wVRel ∧ w0.wPub ≤ w.wPub ∧
       w0.wVcap ≤ w.wVcap⌝ := by
  unfold wsScalAuth wsScalLb
  iintro ⟨⟨A1, A2, A3, A4, A5, A6, A7⟩, ⟨L1, L2, L3, L4, L5, L6, L7⟩⟩
  ihave %h1 := MonoNat.auth_lb_own_valid $$ A1 L1
  ihave %h2 := MonoNat.auth_lb_own_valid $$ A2 L2
  ihave %h3 := MonoNat.auth_lb_own_valid $$ A3 L3
  ihave %h4 := MonoNat.auth_lb_own_valid $$ A4 L4
  ihave %h5 := MonoNat.auth_lb_own_valid $$ A5 L5
  ihave %h6 := MonoNat.auth_lb_own_valid $$ A6 L6
  ihave %h7 := MonoNat.auth_lb_own_valid $$ A7 L7
  ipureintro
  simp only [MaxNat.le_toNat] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2⟩

end scalars

/-! ## 2. THE PER-BYTE COHERENCE FLOOR — and the trap in encoding it.

`wCoh : GMapF Int Nat` with `coh w a := (get? w.wCoh a).getD 0`, ordered by
`∀ a, coh w1 a ≤ coh w2 a`.  The obvious camera is `auth (gmapUR Z max_natUR)` — but the
obvious ENCODING `MaxNat <$> w_coh w` is WRONG, and quietly so:

  `gmap` inclusion is pointwise inclusion in `option`, and `Some x ≼ None` is FALSE.  So a
  state whose map carries an EXPLICIT zero entry (`w_coh w1 = {[a := 0]}`) is not included in
  one that omits the key (`w_coh w2 = ∅`) — even though `ws_le w1 w2` HOLDS, since both have
  `coh _ a = 0`.

So `wsLe` and `≼` disagree exactly on explicit-zero entries, and any `wsLe → ≼` lemma proved
against the naive encoding is unprovable.  Two ways out:

  (a) NORMALISE: encode by `MaxNat <$> filter (fun kv => kv.2 ≠ 0) (w_coh w)`, and carry a
      normalisation lemma `coh w a` is preserved.  Keeps one camera; costs a filter-lookup
      lemma.
  (b) TOTALISE: do not use `gmap` inclusion at all — use a camera of FUNCTIONS
      `Z → max_nat` (`discrete_fun`), for which pointwise `≤` IS inclusion on the nose.
      Costs a non-finite camera, which is fine for a ghost floor that is only ever read at
      finitely many keys.

(b) IS WHAT IS BUILT BELOW: `wsLe`'s coherence conjunct is already stated over the TOTAL
`coh`, not over the map, so the function camera matches the intended semantics on the nose
and (a)'s normalisation is an artifact of the representation.

(Rocq's NOTE on `Finite` — `discrete_fun_included_spec` needs a finite index — does not apply
to iris-lean, whose `DiscreteFun.inc_iff` is proved by choice; deviation 5.) -/

/-- The per-byte coherence floor as a camera of FUNCTIONS.  Pointwise `≤` is inclusion
definitionally — no normalisation, no explicit-zero trap. -/
abbrev CohUR : Type := Int → MaxNat

def cohFun (w : Wstate) : CohUR := fun a => .ofNat (coh w a)

section cohAlg

/-- Pointwise `≤` gives inclusion. -/
theorem cohFunIncl (w1 w2 : Wstate) (h : wsLe w1 w2) : cohFun w1 ≼ cohFun w2 :=
  DiscreteFun.inc_iff.mpr fun a => MaxNat.inc_iff.mpr (by
    simp only [cohFun, MaxNat.le_toNat]; exact h.1 a)

/-- The local update behind the authority's frame-preserving update — the `discrete_fun`
twin of `max_nat_local_update`, proved the same way. -/
theorem cohFunLocalUpdate (w w' : Wstate) (g : CohUR) (h : wsLe w w') :
    (cohFun w, g) ~l~> (cohFun w', cohFun w') := by
  refine (local_update_unital_discrete _ _ _ _).mpr fun z _ heq => ⟨fun _ => trivial, ?_⟩
  funext a
  have ha : coh w a = Nat.max (g a).toNat (z a).toNat := congrArg MaxNat.toNat (congrFun heq a)
  have hc := h.1 a
  apply (MaxNat.eq_toNat _ _).mpr
  show coh w' a = Nat.max (coh w' a) (z a).toNat
  simp only [Nat.max_def] at ha ⊢
  (try split at ha) <;> (try split) <;> omega

/-- `cohFun` is a core element, so the fragment is persistent. -/
instance cohFunCoreId (w : Wstate) : CMRA.CoreId (cohFun w) where
  core_id := congrArg some (funext fun a => CMRA.core_eqv_self (cohFun w a))

end cohAlg

/-! ## 3. The two halves assembled: the authority, and the persistent floor.

`wsAuth` carries the fragment at the same value, exactly as `mono_nat_auth` does, so that
`wsLbGet` is `inc_op_right` rather than a frame-preserving update. -/

/-- THE PER-HART WRITE WATERMARK of a CONTEXT (φ-upgrade §1.6).  A map from a hart's index to
the highest log position that context wrote through it, as a `max_nat` auth: the AUTHORITY
rides in the context's running bundle (`WeakCtx.ctx_migr`) and the FRAGMENT is the persistent
breadcrumb (`WeakGhost.ctx_wrote`) an owned points-to carries.  `max_nat` because the
breadcrumb must be a LOWER bound that stays true as the context keeps writing, and a map
rather than a function because only the harts a context has actually run on ever appear. -/
abbrev CtxwrUR : Type := GMapF Nat MaxNat

/-- The coherence floor's functor (deviation 2). -/
abbrev CohRF : COFE.OFunctorPre := constOF (Auth CohUR)

/-- The write watermark's functor (deviation 2). -/
abbrev CtxwrRF : COFE.OFunctorPre := constOF (Auth CtxwrUR)

class WeakViewG (GF : BundledGFunctors) where
  wvScal : WeakViewScalarG GF
  wvCoh : ElemG GF CohRF
  wvWr : ElemG GF CtxwrRF

attribute [reducible, instance] WeakViewG.wvScal WeakViewG.wvCoh WeakViewG.wvWr

structure WviewNames where
  wvnScal : WsNames
  wvnCoh : GName

section view

variable {GF : BundledGFunctors} [WeakViewG GF]

def wsCohAuth (γ : GName) (w : Wstate) : IProp GF :=
  iOwn (F := CohRF) γ ((● cohFun w) • ◯ cohFun w)

def wsCohLb (γ : GName) (w : Wstate) : IProp GF :=
  iOwn (F := CohRF) γ (◯ cohFun w)

/-- The authority on a hart's whole weak state, at an exact value.  This is what the state
interpretation holds; it is NOT what a client threads. -/
def wsAuth (γ : WviewNames) (w : Wstate) : IProp GF :=
  iprop(wsScalAuth γ.wvnScal w ∗ wsCohAuth γ.wvnCoh w)

/-- THE CLIENT-FACING FACT: a persistent, duplicable floor.  Unlike `hart_ws`, this survives
every intervening step for free — that is the whole point, and the reason nothing above a leaf
has to name a `Wstate` or carry a `wsLe`. -/
def wsLb (γ : WviewNames) (w : Wstate) : IProp GF :=
  iprop(wsScalLb γ.wvnScal w ∗ wsCohLb γ.wvnCoh w)

instance wsCohLbPersistent (γ : GName) (w : Wstate) : Persistent (wsCohLb (GF := GF) γ w) := by
  unfold wsCohLb; infer_instance

instance wsLbPersistent (γ : WviewNames) (w : Wstate) : Persistent (wsLb (GF := GF) γ w) := by
  unfold wsLb; infer_instance

instance wsLbTimeless (γ : WviewNames) (w : Wstate) : Timeless (wsLb (GF := GF) γ w) := by
  unfold wsLb wsScalLb wsCohLb; infer_instance

theorem wsCohLbGet (γ : GName) (w : Wstate) : wsCohAuth (GF := GF) γ w ⊢ wsCohLb γ w :=
  iOwn_mono (CMRA.inc_op_right _ _)

theorem wsLbGet (γ : WviewNames) (w : Wstate) : wsAuth (GF := GF) γ w ⊢ wsLb γ w := by
  unfold wsAuth wsLb
  iintro ⟨Hs, Hc⟩
  ihave #Ls := wsScalLbGet γ.wvnScal w $$ Hs
  ihave #Lc := wsCohLbGet γ.wvnCoh w $$ Hc
  iframe Ls Lc

theorem wsCohUpdate (γ : GName) (w w' : Wstate) (h : wsLe w w') :
    wsCohAuth (GF := GF) γ w ⊢ |==> wsCohAuth γ w' :=
  iOwn_update (Auth.auth_update (cohFunLocalUpdate w w' _ h))

/-- THE UPDATE, whole-state.  Again: the caller does not name the old value.  A leaf holding
the authority discharges "there EXISTS a larger `Wstate`" internally, which is what lets the
token above it be opaque. -/
theorem wsUpdate (γ : WviewNames) (w w' : Wstate) (h : wsLe w w') :
    wsAuth (GF := GF) γ w ⊢ |==> wsAuth γ w' := by
  unfold wsAuth
  iintro ⟨Hs, Hc⟩
  imod wsScalUpdate γ.wvnScal w w' h $$ Hs with Hs
  imod wsCohUpdate γ.wvnCoh w w' h $$ Hc with Hc
  imodintro
  iframe Hs Hc

/-- THE SINGLE-BYTE FLOOR — "the duplicable view lower-bound resource".  `cohLb γ a t` says
this hart's coherence floor at byte `a` is at least `t`, and nothing else.  It is the `IProp`
twin of `WeakVProp`'s `⊒(viewByte a t)` receipt: same content, but a ghost fact about a NAMED
hart rather than a constraint on the ASSERTION'S OWN index — which is exactly what makes an
assertion carrying it objective. -/
def cohLb (γ : GName) (a : Int) (t : Nat) : IProp GF :=
  iOwn (F := CohRF) γ (◯ (discreteFunSingleton a (MaxNat.ofNat t) : CohUR))

instance cohLbPersistent (γ : GName) (a : Int) (t : Nat) : Persistent (cohLb (GF := GF) γ a t) := by
  unfold cohLb; infer_instance

instance cohLbTimeless (γ : GName) (a : Int) (t : Nat) : Timeless (cohLb (GF := GF) γ a t) := by
  unfold cohLb; infer_instance

/-- From the validity of an authority-with-fragment joined with another fragment, the second
fragment is pointwise below the authority. -/
private theorem cohValidInc {x s : CohUR}
    (hv : ✓ (((● x : Auth CohUR) • ◯ x) • ◯ s)) (a : Int) : s a ≼ x a := by
  rw [← CMRA.assoc, ← Auth.frag_op] at hv
  have hinc := (Auth.auth_both_valid_discrete.mp hv).1
  exact CMRA.inc_trans (CMRA.inc_op_right _ _) (DiscreteFun.inc_apply hinc a)

theorem cohLbValid (γ : GName) (w : Wstate) (a : Int) (t : Nat) :
    wsCohAuth (GF := GF) γ w ∗ cohLb γ a t ⊢ ⌜t ≤ coh w a⌝ := by
  unfold wsCohAuth cohLb
  iintro ⟨Ha, Hf⟩
  icases iOwn_cmraValid_op $$ [$Ha $Hf] with %hv
  ipureintro
  have h := MaxNat.inc_iff.mp (cohValidInc hv a)
  simpa [MaxNat.le_toNat, cohFun] using h

/-- Weakening one.  Needed wherever a floor is JOINED with another: the join of two floors is
whichever is larger, so the smaller one is always reached by this. -/
theorem cohLbLe (γ : GName) (a : Int) (t t' : Nat) (h : t ≤ t') :
    cohLb (GF := GF) γ a t' ⊢ cohLb γ a t := by
  unfold cohLb
  refine iOwn_mono (Auth.frag_inc_of_inc (DiscreteFun.inc_iff.mpr fun b => ?_))
  by_cases hb : a = b
  · subst hb
    simp only [discreteFunSingleton_self]
    exact MaxNat.inc_iff.mpr (by simpa [MaxNat.le_toNat] using h)
  · simp only [discreteFunSingleton_of_ne _ hb]
    exact CMRA.inc_refl _

/-- Minting one: any floor the authority actually has may be handed out, and being persistent
it never has to be handed back. -/
theorem cohLbGet (γ : GName) (w : Wstate) (a : Int) (t : Nat) (h : t ≤ coh w a) :
    wsCohAuth (GF := GF) γ w ⊢ cohLb γ a t := by
  unfold wsCohAuth cohLb
  refine iOwn_mono (CMRA.inc_trans (Auth.frag_inc_of_inc ?_) (CMRA.inc_op_right _ _))
  refine DiscreteFun.inc_iff.mpr fun b => ?_
  by_cases hb : a = b
  · subst hb
    simp only [discreteFunSingleton_self]
    exact MaxNat.inc_iff.mpr (by simpa [MaxNat.le_toNat, cohFun] using h)
  · simp only [discreteFunSingleton_of_ne _ hb]
    exact ⟨cohFun w b, (CMRA.unit_left_id).symm⟩

theorem wsCohLbValid (γ : GName) (w w0 : Wstate) :
    wsCohAuth (GF := GF) γ w ∗ wsCohLb γ w0 ⊢ ⌜∀ a, coh w0 a ≤ coh w a⌝ := by
  unfold wsCohAuth wsCohLb
  iintro ⟨Ha, Hf⟩
  icases iOwn_cmraValid_op $$ [$Ha $Hf] with %hv
  ipureintro
  intro a
  have h := MaxNat.inc_iff.mp (cohValidInc hv a)
  simpa [MaxNat.le_toNat, cohFun] using h

/-- Soundness of the floor, in the shape client code wants to consume it: what you snapshotted
is `wsLe` below what is actually there. -/
theorem wsLbValid (γ : WviewNames) (w w0 : Wstate) :
    wsAuth (GF := GF) γ w ∗ wsLb γ w0 ⊢ ⌜wsLe w0 w⌝ := by
  unfold wsAuth wsLb
  iintro ⟨⟨Hs, Hc⟩, ⟨Ls, Lc⟩⟩
  ihave %hs := wsScalLbValid γ.wvnScal w w0 $$ [Hs Ls]
  · isplitl [Hs]
    · iexact Hs
    · iexact Ls
  ihave %hc := wsCohLbValid γ.wvnCoh w w0 $$ [Hc Lc]
  · isplitl [Hc]
    · iexact Hc
    · iexact Lc
  ipureintro
  exact ⟨hc, hs⟩

/-- A floor may always be weakened — the `wsLe`-monotone reading. -/
theorem wsLbMono (γ : WviewNames) (w w' : Wstate) (h : wsLe w w') :
    wsLb (GF := GF) γ w' ⊢ wsLb γ w := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold wsLb wsScalLb
  iintro ⟨⟨L1, L2, L3, L4, L5, L6, L7⟩, Lc⟩
  isplitl [L1 L2 L3 L4 L5 L6 L7]
  · isplitl [L1]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h1) $$ L1
    isplitl [L2]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h2) $$ L2
    isplitl [L3]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h3) $$ L3
    isplitl [L4]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h4) $$ L4
    isplitl [L5]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h5) $$ L5
    isplitl [L6]
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h6) $$ L6
    · iapply MonoNat.lb_own_le _ _ _ (by simpa [MaxNat.le_toNat] using h7) $$ L7
  · unfold wsCohLb
    iapply iOwn_mono (Auth.frag_inc_of_inc (cohFunIncl w w' ⟨‹_›, h1, h2, h3, h4, h5, h6, h7⟩))
    iexact Lc

/-- Allocation. -/
theorem wsAlloc (w : Wstate) : ⊢@{IProp GF} |==> ∃ γ, wsAuth γ w := by
  imod MonoNat.own_alloc (.ofNat w.wVrOld) with ⟨%g1, A1, -⟩
  imod MonoNat.own_alloc (.ofNat w.wVwOld) with ⟨%g2, A2, -⟩
  imod MonoNat.own_alloc (.ofNat w.wVrNew) with ⟨%g3, A3, -⟩
  imod MonoNat.own_alloc (.ofNat w.wVwNew) with ⟨%g4, A4, -⟩
  imod MonoNat.own_alloc (.ofNat w.wVRel) with ⟨%g5, A5, -⟩
  imod MonoNat.own_alloc (.ofNat w.wPub) with ⟨%g6, A6, -⟩
  imod MonoNat.own_alloc (.ofNat w.wVcap) with ⟨%g7, A7, -⟩
  imod iOwn_alloc (F := CohRF) ((● cohFun w : Auth CohUR) • ◯ cohFun w)
    (Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, fun _ => trivial⟩) with ⟨%gc, Ac⟩
  imodintro
  iexists ⟨⟨g1, g2, g3, g4, g5, g6, g7⟩, gc⟩
  unfold wsAuth wsScalAuth wsCohAuth
  iframe A1 A2 A3 A4 A5 A6 A7 Ac

end view

/-! ## 4. The authority-only token.

`wviewTok` is the authority with its value EXISTENTIALLY HIDDEN — the shape that makes a
client stop naming `Wstate`s.  It is NOT the token the tree threads: the real one
(`WeakGhost.hart_view`) additionally bundles the hart's `hart_ws` half, because the monotone
authority alone says nothing about the machine.  What is here is the view half of that bundle,
proved once so `WeakGhost` can just pair it up.

NAMING.  This used to be called `hart_view`; the name moved to the real token in `WeakGhost`
when `weak_view_name` landed. -/

section token

variable {GF : BundledGFunctors} [WeakViewG GF]

def wviewTok (γ : WviewNames) : IProp GF := iprop(∃ w, wsAuth γ w)

theorem wviewTokIntro (γ : WviewNames) (w : Wstate) : wsAuth (GF := GF) γ w ⊢ wviewTok γ := by
  unfold wviewTok
  iintro H
  iexists w
  iexact H

/-- What a leaf does: open the token, learn the current state, step it to any `wsLe`-larger
one, close it.  The caller sees `wviewTok γ` in and `wviewTok γ` out — no values at all. -/
theorem wviewTokStep (γ : WviewNames) (step : Wstate → Wstate) (hstep : ∀ w, wsLe w (step w)) :
    wviewTok (GF := GF) γ ⊢ |==> wviewTok γ := by
  unfold wviewTok
  iintro ⟨%w, Hauth⟩
  imod wsUpdate γ w (step w) (hstep w) $$ Hauth with Hauth
  imodintro
  iexists step w
  iexact Hauth

/-- Snapshotting through the token: a client that DOES care about views (the lock, the escrow)
takes a persistent floor and keeps it across arbitrarily many later steps. -/
theorem wviewTokSnapshot (γ : WviewNames) :
    wviewTok (GF := GF) γ ⊢ |==> ∃ w, wviewTok γ ∗ wsLb γ w := by
  unfold wviewTok
  iintro ⟨%w, Hauth⟩
  ihave #Hlb := wsLbGet γ w $$ Hauth
  imodintro
  iexists w
  iframe Hlb
  iexists w
  iexact Hauth

end token

/-! ## 5. Allocation for the whole hart enumeration.

The `ghost_var_alloc_halves_cpus` analogue: one fresh `WviewNames` per hart.  Kept generic in
the index type so this file still needs nothing but `WeakMem` — `WeakAdequacy` instantiates it
at `CPU`. -/

theorem wsAllocCpus {GF : BundledGFunctors} [WeakViewG GF] {A : Type _} [DecidableEq A]
    (w : Wstate) (cs : List A) (hnd : cs.Nodup) :
    ⊢@{IProp GF} |==> ∃ f : A → WviewNames, [∗list] c ∈ cs, wsAuth (f c) w := by
  induction cs with
  | nil =>
    imodintro
    iexists fun _ => ⟨⟨0, 0, 0, 0, 0, 0, 0⟩, 0⟩
    iempintro
  | cons c cs' ih =>
    obtain ⟨hc, hnd'⟩ := List.nodup_cons.mp hnd
    imod ih hnd' with ⟨%fr, Hrest⟩
    imod wsAlloc (GF := GF) w with ⟨%γ, Hg⟩
    imodintro
    iexists fun c' => if c' = c then γ else fr c'
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · simp only [if_true]
      iexact Hg
    · iapply BigSepL.bigSepL_mono ?_ $$ Hrest
      intro k c' hk
      have hne : c' ≠ c := fun he => hc (he ▸ List.mem_of_getElem? hk)
      simp only [hne, if_false]
      exact .rfl

end Weak
