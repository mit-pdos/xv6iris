/-
Weak: THE WEAK BYTE POINTS-TO, THE `vwpHold` DISCIPLINE, AND THE LOAD AND STORE RULES (M2a).

Rocq: `iris/WeakVProp.v` @ xxvzwolszwmp (1cc222280).

`WeakView` gives the index and the `VProp` core; this file gives the surface layer's first
inhabitant — the byte points-to, in its clean (`a ↦w{dq} v`), context-owned (`wptOwn ξ a v`, the
ambient `a ↦wo v`) and hart-owned (`wptOwnH c a v`, M-mode only) forms — and the two memory rules,
at the two altitudes the M2a design call fixes.

Rocq header (verbatim, Rocq vocabulary; the design call):

    THE vProp LAYER IS A DISCIPLINE OVER THE BASE LOGIC FIRST, AND A
    monPred-LEVEL LIBRARY SECOND.  There is deliberately NO new [WP]
    connective here.  The reason is structural, not economical: every WP in
    this tree is [WP (Loop : expr …) {{ _, False }}] — a hart's non-returning
    fetch-execute loop — and a leaf lemma does not *state* a WP, it
    TRANSFORMS one ([WeakExec.wp_wexec_step]: give me the hart's state
    interpretation and a continuation for every admissible successor, and I
    give you back the loop's WP).  A [vProp]-level WP would therefore be a
    monPred wrapper around a connective whose only user is a rule that hands
    out an iProp-level obligation at the hart's CURRENT weak state.  So we
    make the hart's weak state the primary object instead:

        [vwp_hold P ws := monPred_at P (ws_view ws)]

    read as "[P] holds AT the hart whose weak state is [ws]".  A leaf rule is
    an iProp lemma parameterised by the hart's [ws], taking [vwp_hold P ws]
    premises and producing [vwp_hold Q ws'] conclusions with [ws_le ws ws']
    available; [vwp_hold_mono] then carries every UNTOUCHED premise across
    the step for free, which is the property that makes the discipline pay.
    The pretty monPred-level statements ([P @@ ws_view ws]-shaped, §6) are
    one-liners on top and are what the M3 lock library will quote.

    VERDICT ON THE TWO ALTITUDES (M2a): the split works, and the split point
    is [vwp_hold_mono] + [wpt_at].  [wpt_at] decodes the points-to into
    exactly "an element of the latest-write map, plus a floor inequality on
    the hart's index", after which BOTH rules are pure [WeakMem]/[WeakGhost]
    reasoning with no monPred in sight; and every frame condition of a step
    is discharged by [vwp_hold_mono] from [WeakInterp]'s own
    [wread_post_ws_le] / [wwrite_post_ws_le].  The monPred altitude is
    re-entered only at §6, in three lines.

(The Rocq file's closing note — "where the instruction altitude starts" — says the rules above stop
at the MEMORY EVENT, the `wreadOk` / `wwritePost` obligations one `MemRead` / `MemWrite` produces;
a whole-instruction leaf additionally needs the weak fetch over `wptImg` (§3b), the
register-side, hence objective, `sconf`/PMP/translation tower, and `WeakExec.wexec_covers` — none of
it weak-memory work.)

**Deviations from Rocq.**

1. STATEMENT SHAPES (the `WeakGhost` deviation 9 convention): Rocq `P -∗ Q -∗ R` is `P ∗ Q ⊢ R`,
   `P -∗ Q ==∗ R` is `P ∗ Q ⊢ |==> R`; the lemmas the earlier spike ported (`wlatElem_agree`,
   `wlatPointsto_agree`, `wlatPointsto_valid_2`) keep their `P ⊢ Q -∗ R` form.
   PRECEDENCE PITFALL (measured): iris-lean's `|==> P ∗ Q` parses as `(|==> P) ∗ Q`; Rocq's is
   `|==> (P ∗ Q)`.  Every such conclusion is parenthesised.
2. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is dropped (nothing here uses it); the ghost
   state is `[WeakGS GF]`.  §2 (`vwpHold` and its laws) is stated without `[WeakGS GF]` because it
   does not use it (Lean would otherwise include the section instance).
3. Rocq's dfrac notation `a ↦w{dq} v` / `a ↦w□ v` / `a ↦w{# q} v` / `a ↦w v` becomes the Lean
   notations `a ↦w{dq} v` / `a ↦w□ v` / `a ↦w{DFrac.own q} v` / `a ↦w v` (no custom dfrac
   entry); the address is an `Int` (Rocq `Z`), the byte a `BitVec 8` (Rocq `bv 8`).
4. `vwp_hold_ne` / `vwp_hold_proper` / `vwp_hold_mono'` (setoid instances) are the theorems
   `vwpHold_ne` / `vwpHold_proper` / `vwpHold_mono'`; iris-lean's OFE equality is Leibniz, so
   `proper` is stated over `⊣⊢`.
5. ACCESS-KIND VOCABULARY (O2, `Weak/WeakInterp.lean`): Rocq `ak_coh ak = false` is
   `ak.akIfetch = false` (the record's first field, renamed); `ak_sync` is `akSync`.  The non-fetch
   arm of `wbyteOk` is Rocq's `wbyte_ok` arm verbatim, so the load rules' content is unchanged.
6. MACHINE VOCABULARY (`WeakMem`/`WeakInterp`/`WeakGhost` deviations): `wm_img σ` ↦ `σ.wmImg`,
   `wm_log` ↦ `wmLog`, `wm_ws` ↦ `wmWs`, `wm_tid m = Some (fin_to_nat c)` ↦ `m.wmTid = some c.val`,
   `wm_ak` ↦ `wmAk`, `S (length l)` ↦ `l.length + 1`, `acc_addr` ↦ `WeakInterp.accAddr`, `pa_z`
   ↦ `paZ`, `bs !!! j` ↦ `bs[j]!`, `n : N` (access width) ↦ `n : Nat`.  `wpt_store_post(_own)`
   instantiate the post-machine-state as `{ σ with wmLog := …, wmWs := … }` (Rocq spells the
   five-field `WMState` literal; the Lean `Wmstate` has the sixth field `wmItv`, kept).
7. `wpt_wread_word`'s conclusion `w = Z_to_bv (8 * n) (assemble_bytes bs)` is
   `w = assembleBytes n (fun j => bs[j]!)`: the Lean `WeakInterp.assembleBytes` is the
   little-endian assembly over a byte function (`WeakInterp` deviation 9), and its byte lemma
   `nthByteAssembleBytes` replaces Rocq's `nth_byte_assemble_len` (so the length side condition is
   needed only by `wpt_wread_bytes`, where it is kept).  Same word.
8. `CurCtx` (Rocq `Class CurCtx := cur_ctx : CtxId`, a bare singleton class) is the Lean class
   `CurCtx` with the one field `curCtx`, inside `namespace Weak` (so it is `Weak.CurCtx`, distinct
   from `MachCSL.CurCtx`).  `Typeclasses Opaque cur_ctx` has no Lean counterpart: Lean's instance
   search does not unfold a structure projection.  `a ↦wo v` is the notation
   `wptOwn CurCtx.curCtx a v`.  THE ONE-CONTEXT CONVENTION of the Rocq file holds verbatim: never
   bind a second `[CurCtx]`; quantify over `CtxId` and use `wptOwn ξ …` where two contexts meet.
9. `wwrite_msg_byte1_none`'s proof and `wpt_wwrite_byte`'s floor obligation go through the Lean
   `storePostRun` = `ctrlPost (storePostBytes …) wTbank` (the `ctrlPost` only moves `wVcap`, which
   the index does not read).
10. Lean-only helpers: `wlatStoreOwnStep` (the ghost half of `wpt_store_rule_own`: both
   `ghost_map_update`s and the re-established ties, which the Rocq proof inlines) and the private
   `loadPin` (the two load rules' shared pure `assert`s: `t' = t` by `readableLatestPin`, then
   `b = v`).

**Rocq → Lean name map.**  §1 `ws_view`→`wsView`, `flr_ws_view`→`flr_wsView`, `ws_view_mono`→
`wsView_mono`, `ws_view_init`→`wsView_init`, `flr_store_post`→`flr_storePost`,
`flr_load_post_at`→`flr_loadPostAt`.  §2 `vwp_hold`→`vwpHold`, `vwp_hold_*`→`vwpHold_*` (`ne`,
`proper`, `mono'`, `mono`, `intro`, `sep`, `exist`, `pure`, `embed`, `bupd`, `seen`, `seen_self`,
`view_at`, `freeze`, `thaw`); `vwp_hold_ent`→`WeakVProp.vwpHold_ent` (FILE-QUALIFIED,
`notes/weak-port-dupnames.json`).  §3 `wpt`→`wpt`, `wpt_own`→`wptOwn`, `CurCtx`/`cur_ctx`→
`CurCtx`/`CurCtx.curCtx`, `wpt_at_view`/`wpt_at`/`wpt_at_intro`→ same, `wlat_elem_agree`→
`wlatElem_agree`, `wlat_pointsto_agree/valid_2/persist/split/persistent/timeless`→
`wlatPointsto_agree/valid_2/persist/split/persistent/timeless`,
`wpt_persistent/timeless/agree/valid_2/split/persist`→ same, `wpt_img`→`wptImg`,
`wpt_img_objective/persistent/wpt/at`→`wptImg_objective/persistent/wpt/at`,
`wpt_own_at_view/at/at_intro/of_wpt/mono`→`wptOwn_at_view/at/at_intro/of_wpt/mono`, `wpt_own_h`→
`wptOwnH`, `wpt_own_h_at_view/at/at_intro/of_wpt`→`wptOwnH_at_view/at/at_intro/of_wpt`,
`nv_ok_of_wpt_own(_at)`→`nvOk_of_wptOwn(_at)`.  §4/§5 `wpt_load_rule(_own)`, `wpt_load_wread(_own)`,
`wpt_store_rule(_own)`, `wpt_store_post(_own)`→ same.  §5b `wpt_own_of_wpt_cur`→
`wptOwn_of_wpt_cur`, `wpt_load_rule_own_cur`, `wpt_load_wread_own_cur`, `wpt_store_rule_own_cur`,
`wpt_store_post_own_cur`→ same, `nv_ok_of_wpt_own(_at)_cur`→`nvOk_of_wptOwn(_at)_cur`.  §6
`vwp_hold_view_at_iff`→`vwpHold_view_at_iff`, `wpt_load_vprop`, `wpt_store_vprop`→ same.  §7
`wpt_wread_byte/bytes/word`→ same, `wwrite_msg_byte1(_none)`→`wwriteMsg_byte1(_none)`,
`wpt_wwrite_byte`→ same.

**Not ported:** nothing.  (The notation `↦w` / `↦wo` are notations, not declarations.)

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakGhost
import Weak.WeakInterp
import Weak.WeakMem
import Weak.WeakView
import MachCSL.MonPredExtra
import Iris.Instances.Lib.GhostMap

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap
open Iris.Std.LawfulPartialMap MachCSL MachCSL.Stdpp
open Wcds

/-! ## 1. The hart index

A hart's LOGICAL INDEX at a program point is its semantic read floor: the scalar pre-view
`wVrNew` joined with the per-byte coherence map `wCoh` (design doc, Decision 5).  That is exactly a
`View`, and the correspondence is definitional. -/

/-- Rocq `ws_view`. -/
def wsView (ws : Wstate) : View := ⟨ws.wVrNew, ws.wCoh⟩

theorem flr_wsView (ws : Wstate) (a : Int) : flr (wsView ws) a = max ws.wVrNew (coh ws a) := rfl

/-- MONOTONICITY: the machine's own per-field `wsLe` IS the index order.  Every `WeakInterp` step
lemma (`wreadPostWsLe`, `wwritePostWsLe`, `barrierPostLe`, `wrunWsLe`) therefore lands directly on
`≤`. -/
theorem wsView_mono (ws ws' : Wstate) : wsLe ws ws' → wsView ws ≤ wsView ws' := by
  intro h
  obtain ⟨hcoh, -, -, hrN, -⟩ := h
  refine (View.le_spec _ _).2 fun a => ?_
  rw [flr_wsView, flr_wsView]
  have := hcoh a
  omega

theorem wsView_init (a : Int) : flr (wsView wsInit) a = 0 := by
  simp [flr_wsView, coh, wsInit, lookupEmpty]

/-- The floor a STORE leaves at the byte it wrote — the premise the store rule's post-view side
condition is discharged with. -/
theorem flr_storePost (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    t ≤ flr (wsView (storePost ws rl a t)) a := by
  rw [flr_wsView]
  have := storePostCoh ws rl a t
  omega

/-- ... and the floor a LOAD leaves: the timestamp read is covered too. -/
theorem flr_loadPostAt (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    t ≤ flr (wsView (loadPostAt ws aq vpre a t)) a := by
  rw [flr_wsView]
  have := loadPostAtCoh ws aq vpre a t
  omega

/-! ## 2. `vwpHold` — the discipline

"`P` holds at the hart whose weak state is `ws`".  Everything below is stated through it; the
monPred layer is re-entered only at §6. -/

section Rules
variable {GF : BundledGFunctors}

/-- Rocq `vwp_hold`. -/
def vwpHold (P : VProp GF) (ws : Wstate) : IProp GF := P.monPred_at (wsView ws)

theorem vwpHold_ne (ws : Wstate) : OFE.NonExpansive (fun P : VProp GF => vwpHold P ws) :=
  ⟨fun _ _ _ h => dist_at.mp h _⟩

theorem vwpHold_proper (ws : Wstate) {P Q : VProp GF} (h : P ⊣⊢ Q) :
    vwpHold P ws ⊣⊢ vwpHold Q ws :=
  ⟨entails_at.mp h.mp _, entails_at.mp h.mpr _⟩

theorem vwpHold_mono' (ws : Wstate) {P Q : VProp GF} (h : P ⊢ Q) : vwpHold P ws ⊢ vwpHold Q ws :=
  entails_at.mp h _

/-- THE WORKHORSE.  A step only ever raises the hart's views, so every premise the step did not
touch survives it with no work at all.  This is what makes the leaf rules below need side
conditions only about the byte they act on. -/
theorem vwpHold_mono (P : VProp GF) {ws ws' : Wstate} (h : wsLe ws ws') :
    vwpHold P ws ⊢ vwpHold P ws' :=
  P.monPred_mono (wsView_mono ws ws' h)

/-- A `VProp` entailment used INSIDE the discipline (the `apply`-shaped twin of `vwpHold_mono'`). -/
theorem WeakVProp.vwpHold_ent {P Q : VProp GF} (ws : Wstate) (h : P ⊢ Q) :
    vwpHold P ws ⊢ vwpHold Q ws :=
  vwpHold_mono' ws h

/-- ... and its index-level twin: an obligation stated at an index BELOW the hart's is an obligation
at the hart.  This is the seam a future `VProp`-level WP would be defined over (Cosmo's
`∀ V' ⊒ V`). -/
theorem vwpHold_intro (V : View) (P : VProp GF) (ws : Wstate) (h : V ≤ wsView ws) :
    P.monPred_at V ⊢ vwpHold P ws :=
  P.monPred_mono h

/-- The structural laws — all definitional unfoldings of `monPred_at`. -/
theorem vwpHold_sep (P Q : VProp GF) (ws : Wstate) :
    vwpHold iprop(P ∗ Q) ws ⊣⊢ vwpHold P ws ∗ vwpHold Q ws := .rfl
theorem vwpHold_exist {A : Type _} (Φ : A → VProp GF) (ws : Wstate) :
    vwpHold iprop(∃ x, Φ x) ws ⊣⊢ ∃ x, vwpHold (Φ x) ws := monPred_at_exist _ Φ
theorem vwpHold_pure (φ : Prop) (ws : Wstate) : vwpHold (iprop(⌜φ⌝) : VProp GF) ws ⊣⊢ ⌜φ⌝ := .rfl
theorem vwpHold_embed (R : IProp GF) (ws : Wstate) : vwpHold (iprop(⎡R⎤) : VProp GF) ws ⊣⊢ R :=
  .rfl
theorem vwpHold_bupd (P : VProp GF) (ws : Wstate) :
    vwpHold iprop(|==> P) ws ⊣⊢ |==> vwpHold P ws := .rfl

/-- The seen assertion at the hart IS the index inequality. -/
theorem vwpHold_seen (V : View) (ws : Wstate) :
    vwpHold (⊒V : VProp GF) ws ⊣⊢ ⌜V ≤ wsView ws⌝ := .rfl

theorem vwpHold_seen_self (ws : Wstate) : ⊢ vwpHold (⊒(wsView ws) : VProp GF) ws :=
  seen_at_self (wsView ws)

/-- THE SPLIT AXIOM, transported to the discipline.  `P @@ V` is index-free (objective), so its
value at the hart is just `P`'s value at `V`. -/
theorem vwpHold_view_at (P : VProp GF) (V : View) (ws : Wstate) :
    vwpHold (P @@ V) ws ⊣⊢ P.monPred_at V := .rfl

theorem vwpHold_freeze (P : VProp GF) (ws : Wstate) :
    vwpHold P ws ⊣⊢ vwpHold (P @@ wsView ws) ws :=
  .rfl

theorem vwpHold_thaw (V : View) (P : VProp GF) (ws : Wstate) (h : V ≤ wsView ws) :
    vwpHold (P @@ V) ws ⊢ vwpHold P ws :=
  vwpHold_intro V P ws h

end Rules

/-! ## 3. The byte points-to

`a ↦w{dq} v` — "the LATEST write to byte `a` is `(t, v)` for some timestamp `t`, AND I have
observed `t`".  The first conjunct is the base-layer element (`WeakGhost.wlatPointsto`, objective —
it is an embedded `IProp`); the second is the receipt that makes the assertion SUBJECTIVE, and is
the entire difference between this and the SC points-to.  Mutable RAM bytes are the only subjective
footprint in the whole design (design doc, Decision 5). -/

section PointsTo
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wpt`. -/
def wpt (a : Int) (dq : DFrac) (v : BitVec 8) : VProp GF :=
  iprop(∃ t : Nat, ⎡wlatPointsto (GF := GF) a dq t v⎤ ∗ ⊒(viewByte a t))

/-- ### 3'. THE OWNED FORM (the φ-upgrade's C-or-D points-to)

A byte a thread owns EXCLUSIVELY and may have plain-stored to: the value element at full fraction,
plus a state element that is CLEAN or DIRTY — and, if dirty, the persistent breadcrumb naming the
hart that dirtied it (`WeakGhost.wownCtx`).  This is the postcondition shape of every owned store —
it absorbs both outcomes, so no call site case-splits on the access class — and the only shape a
plain store accepts on the way in.

IT IS INDEXED BY THE EXECUTION CONTEXT `ξ`, NOT BY A HART (φ-upgrade §1.6), and that is what makes
it FRAME across a migration: nothing in the assertion changes when the thread is rescheduled, so
the caller's resource is literally the same proposition on both sides of a yield.  The hart that
dirtied the byte is recorded inside, in the breadcrumb, where only the LEAF ever looks at it —
`WeakGhost.wownCtxRetarget` turns it back into an ordinary `wownSt c` out of the scheduler's
migration invariant. -/
def wptOwn (ξ : CtxId) (a : Int) (v : BitVec 8) : VProp GF :=
  iprop(∃ t : Nat, ⎡wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownCtx (GF := GF) ξ a t⎤ ∗
    ⊒(viewByte a t))

end PointsTo

notation:50 a:50 " ↦w{" dq "} " v:50 => wpt a dq v
notation:50 a:50 " ↦w□ " v:50 => wpt a DFrac.discard v
notation:50 a:50 " ↦w " v:50 => wpt a (DFrac.own 1) v

/-! ## 3''. THE AMBIENT CONTEXT — `CurCtx` and the bare `↦wo` (φ-upgrade §1.7)

`wptOwn` is indexed by the execution context, and a function's context is the SAME value at every
one of its access sites.  So it is supplied the way a hart is: by a per-lemma or per-section
instance binder (deviation 8), and the surface form is a notation over the primitive, filling the
class argument by resolution.

WHY THE AMBIENT TRICK IS SOUND HERE AND WAS NOT FOR THE HART: a WP's hart is NOT invariant across a
function (a timer trap parks the thread and any hart may resume it); `ξ` is — that is the entire
content of §1.6.  So the `↦wo` before a yield and the `↦wo` after it are the SAME proposition
because they resolve to the SAME instance.

THE ONE-CONTEXT CONVENTION: the bare notation is for code with exactly one context in scope.  Where
two contexts meet — the scheduler / `WeakCtx` machinery, any yield-shaped spec, ANY LEMMA THAT
WOULD JOIN THE TWO SIDES OF A TRANSFER, and the primitive rules of §4/§5 themselves — spell `ξ`
explicitly as `wptOwn ξ …`.  THE HAZARD (measured in Rocq, 2026-08-12, and silent): with TWO
`CurCtx` hypotheses in scope the projection resolves to one of them and NOTHING IS REPORTED.  Never
introduce a second `CurCtx` binder. -/

/-- Rocq `CurCtx`: the ambient execution context, a bare singleton class (no global instance
anywhere). -/
class CurCtx where
  curCtx : CtxId

/-- The bare owned points-to: `wptOwn` with the context filled in ambiently.  `a ↦w v` is its
clean sibling; the HART-indexed `wptOwnH` (§3c'') is not this and is not the API. -/
notation:50 a:50 " ↦wo " v:50 => wptOwn CurCtx.curCtx a v

section PointsToLaws
variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE DECODE LEMMA, and the seam between the two altitudes: at an index, the points-to is exactly
"an element of the latest-write map, whose timestamp the index's floor for `a` covers".  Every rule
below is proved through this and never mentions `MonPred` again.  Stated at an ARBITRARY index,
because the framing pattern (φ-upgrade §1.5) needs the decode at a FROZEN index: a fact a thread
parks with is `P.monPred_at V` for the parking hart's `V`, an objective `IProp` which survives the
migration untouched.  `wpt_at` is the `V := wsView ws` instance. -/
theorem wpt_at_view (a : Int) (dq : DFrac) (v : BitVec 8) (V : View) :
    (wpt (GF := GF) a dq v).monPred_at V ⊣⊢
      ∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ⌜t ≤ flr V a⌝ := by
  unfold wpt
  constructor
  · iintro ⟨%t, He, %h⟩
    iexists t
    iframe He
    ipureintro; exact (viewByte_le a t V).mp h
  · iintro ⟨%t, He, %h⟩
    iexists t
    iframe He
    ipureintro; exact (viewByte_le a t V).mpr h

theorem wpt_at (a : Int) (dq : DFrac) (v : BitVec 8) (ws : Wstate) :
    vwpHold (wpt (GF := GF) a dq v) ws ⊣⊢
      ∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ⌜t ≤ flr (wsView ws) a⌝ :=
  wpt_at_view a dq v (wsView ws)

/-- The introduction form: owning the element and covering its timestamp is the points-to. -/
theorem wpt_at_intro (a : Int) (dq : DFrac) (v : BitVec 8) (t : Nat) (ws : Wstate)
    (ht : t ≤ flr (wsView ws) a) :
    wlatPointsto (GF := GF) a dq t v ⊢ vwpHold (wpt (GF := GF) a dq v) ws := by
  refine BIBase.Entails.trans ?_ (wpt_at a dq v ws).mpr
  iintro He
  iexists t
  iframe He
  ipureintro; exact ht

/-! ### 3a. fractions, agreement, persistence -/

/-- TIMESTAMP AGREEMENT ACROSS FRACTIONS, at the base altitude: two elements for the same byte
agree on BOTH components.  (The timestamp cannot be stated at the `VProp` altitude — it is
existentially bound there — which is precisely why this one is a base-logic lemma.) -/
theorem wlatElem_agree (a : Int) (dq1 : DFrac) (t1 : Nat) (v1 : BitVec 8) (dq2 : DFrac) (t2 : Nat)
    (v2 : BitVec 8) :
    wlatElem (GF := GF) a dq1 t1 v1 ⊢ wlatElem (GF := GF) a dq2 t2 v2 -∗ ⌜t1 = t2 ∧ v1 = v2⌝ := by
  unfold wlatElem
  iintro H1 H2
  icases ghost_map_elem_agree _ _ _ _ _ _ $$ [$H1 $H2] with %h
  ipureintro
  exact Prod.mk.inj h

theorem wlatPointsto_agree (a : Int) (dq1 : DFrac) (t1 : Nat) (v1 : BitVec 8) (dq2 : DFrac)
    (t2 : Nat) (v2 : BitVec 8) :
    wlatPointsto (GF := GF) a dq1 t1 v1 ⊢
      wlatPointsto (GF := GF) a dq2 t2 v2 -∗ ⌜t1 = t2 ∧ v1 = v2⌝ := by
  unfold wlatPointsto
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply wlatElem_agree $$ H1 H2

theorem wlatPointsto_valid_2 (a : Int) (dq1 : DFrac) (t1 : Nat) (v1 : BitVec 8) (dq2 : DFrac)
    (t2 : Nat) (v2 : BitVec 8) :
    wlatPointsto (GF := GF) a dq1 t1 v1 ⊢
      wlatPointsto (GF := GF) a dq2 t2 v2 -∗ ⌜✓ (dq1 • dq2) ∧ t1 = t2 ∧ v1 = v2⌝ := by
  unfold wlatPointsto wlatElem
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  icombine H1 H2 gives %⟨hv, heq⟩
  ipureintro
  exact ⟨hv, Prod.mk.inj heq⟩

theorem wlatPointsto_persist (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlatPointsto (GF := GF) a dq t v ⊢ |==> wlatPointsto (GF := GF) a DFrac.discard t v := by
  unfold wlatPointsto wclean wcdsEl wlatElem
  iintro ⟨H1, H2⟩
  imod ghost_map_elem_persist _ _ _ _ $$ H1 with H1
  imod ghost_map_elem_persist _ _ _ _ $$ H2 with H2
  imodintro
  iframe H1 H2

/-- FRACTION SPLIT at the base altitude: both halves of the points-to are ghost-map elements, so
the split is the algebra's, twice. -/
theorem wlatPointsto_split (a : Int) (q1 q2 : Qp) (t : Nat) (v : BitVec 8) :
    wlatPointsto (GF := GF) a (DFrac.own (q1 + q2)) t v ⊣⊢
      wlatPointsto (GF := GF) a (DFrac.own q1) t v ∗ wlatPointsto (GF := GF) a (DFrac.own q2) t v := by
  unfold wlatPointsto wclean wcdsEl wlatElem
  have hE := (ghost_map_elem_fractional (GF := GF) (WeakGS.latName (GF := GF)) a (t, v)).fractional
    q1 q2
  have hC := (ghost_map_elem_fractional (GF := GF) (WeakGS.cdsName (GF := GF)) a WClean).fractional
    q1 q2
  refine (sep_congr hE hC).trans ?_
  constructor
  · iintro ⟨⟨E1, E2⟩, ⟨C1, C2⟩⟩
    isplitl [E1 C1]
    · iframe E1 C1
    · iframe E2 C2
  · iintro ⟨⟨E1, C1⟩, ⟨E2, C2⟩⟩
    isplitl [E1 E2]
    · iframe E1 E2
    · iframe C1 C2

instance wlatPointsto_persistent (a : Int) (t : Nat) (v : BitVec 8) :
    Persistent (wlatPointsto (GF := GF) a DFrac.discard t v) := by
  unfold wlatPointsto wclean wcdsEl wlatElem; infer_instance

instance wlatPointsto_timeless (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    Timeless (wlatPointsto (GF := GF) a dq t v) := by
  unfold wlatPointsto wclean wcdsEl wlatElem; infer_instance

instance wpt_persistent (a : Int) (v : BitVec 8) : Persistent (a ↦w□ v : VProp GF) := by
  unfold wpt; infer_instance

instance wpt_timeless (a : Int) (q : Qp) (v : BitVec 8) :
    Timeless (a ↦w{DFrac.own q} v : VProp GF) := by
  unfold wpt; infer_instance

/-- VALUE AGREEMENT at the surface altitude.  NOTE the two points-to need NOT be at the same index
for this: the conclusion is pure, so the statement is a `VProp` entailment and the proofmode reads
both sides at whatever index it is instantiated at. -/
theorem wpt_agree (a : Int) (dq1 : DFrac) (v1 : BitVec 8) (dq2 : DFrac) (v2 : BitVec 8) :
    iprop(a ↦w{dq1} v1 ∗ a ↦w{dq2} v2) ⊢ (⌜v1 = v2⌝ : VProp GF) := by
  istart (IProp GF)
  iintro %V ⟨H1, H2⟩
  icases (wpt_at_view a dq1 v1 V).mp $$ H1 with ⟨%t1, He1, -⟩
  icases (wpt_at_view a dq2 v2 V).mp $$ H2 with ⟨%t2, He2, -⟩
  icases wlatPointsto_agree $$ He1 He2 with %⟨_, h⟩
  ipureintro; exact h

theorem wpt_valid_2 (a : Int) (dq1 : DFrac) (v1 : BitVec 8) (dq2 : DFrac) (v2 : BitVec 8) :
    iprop(a ↦w{dq1} v1 ∗ a ↦w{dq2} v2) ⊢ (⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ : VProp GF) := by
  istart (IProp GF)
  iintro %V ⟨H1, H2⟩
  icases (wpt_at_view a dq1 v1 V).mp $$ H1 with ⟨%t1, He1, -⟩
  icases (wpt_at_view a dq2 v2 V).mp $$ H2 with ⟨%t2, He2, -⟩
  icases wlatPointsto_valid_2 $$ He1 He2 with %⟨hv, _, h⟩
  ipureintro; exact ⟨hv, h⟩

/-- FRACTION SPLIT / JOIN.  Both directions hold — and the ← direction is not free: two points-to
for the same byte may a priori carry DIFFERENT timestamps, and it is the element agreement above
that forces them equal before the fractions can be combined. -/
theorem wpt_split (a : Int) (q1 q2 : Qp) (v : BitVec 8) :
    (a ↦w{DFrac.own (q1 + q2)} v : VProp GF) ⊣⊢
      iprop(a ↦w{DFrac.own q1} v ∗ a ↦w{DFrac.own q2} v) := by
  istart (IProp GF)
  iintro %V
  isplit
  · iintro H
    icases (wpt_at_view a _ v V).mp $$ H with ⟨%t, He, %ht⟩
    icases (wlatPointsto_split a q1 q2 t v).mp $$ He with ⟨He1, He2⟩
    isplitl [He1]
    · iapply (wpt_at_view a _ v V).mpr
      iexists t
      iframe He1
      ipureintro; exact ht
    · iapply (wpt_at_view a _ v V).mpr
      iexists t
      iframe He2
      ipureintro; exact ht
  · iintro ⟨H1, H2⟩
    icases (wpt_at_view a _ v V).mp $$ H1 with ⟨%t1, He1, %ht1⟩
    icases (wpt_at_view a _ v V).mp $$ H2 with ⟨%t2, He2, -⟩
    icases wlatPointsto_agree $$ He1 He2 with %⟨heq, -⟩
    subst heq
    iapply (wpt_at_view a _ v V).mpr
    iexists t1
    isplitl [He1 He2]
    · iapply (wlatPointsto_split a q1 q2 t1 v).mpr
      iframe He1 He2
    · ipureintro; exact ht1

theorem wpt_persist (a : Int) (dq : DFrac) (v : BitVec 8) :
    (a ↦w{dq} v : VProp GF) ⊢ |==> a ↦w□ v := by
  istart (IProp GF)
  iintro %V H
  icases (wpt_at_view a dq v V).mp $$ H with ⟨%t, He, %ht⟩
  imod wlatPointsto_persist $$ He with He
  imodintro
  iapply (wpt_at_view a _ v V).mpr
  iexists t
  iframe He
  ipureintro; exact ht

/-! ### 3b. THE OBJECTIVITY SPECIAL CASE — an era-image byte

A byte whose latest write is the ERA-INITIAL IMAGE — timestamp 0, i.e. a byte no message has ever
written: kernel text, kernel rodata, any write-once boot datum — carries a points-to with NO
receipt, because `viewByte a 0` is the bottom view and every index is above it.  That makes it a
plain embedded `IProp`, hence OBJECTIVE, hence admissible inside an invariant and freely shareable
across harts.

THE CONVERSE IS FALSE AND THE DISTINCTION MATTERS: a `↦w□` whose timestamp is > 0 is PERSISTENT but
NOT objective — a hart that has not observed that timestamp cannot read the byte, so putting one in
an invariant would be unsound.  Persistence and objectivity are independent here. -/

/-- Rocq `wpt_img`. -/
def wptImg (a : Int) (dq : DFrac) (v : BitVec 8) : VProp GF :=
  iprop(⎡wlatPointsto (GF := GF) a dq 0 v⎤)

instance wptImg_objective (a : Int) (dq : DFrac) (v : BitVec 8) :
    Objective (wptImg (GF := GF) a dq v) := by
  unfold wptImg; infer_instance

instance wptImg_persistent (a : Int) (v : BitVec 8) :
    Persistent (wptImg (GF := GF) a DFrac.discard v) := by
  unfold wptImg; infer_instance

/-- An era-image points-to IS a points-to, at every index. -/
theorem wptImg_wpt (a : Int) (dq : DFrac) (v : BitVec 8) :
    wptImg (GF := GF) a dq v ⊢ a ↦w{dq} v := by
  unfold wptImg wpt
  iintro He
  iexists 0
  iframe He
  iapply seen_byte_0

/-- ... and conversely, a points-to whose element sits at timestamp 0 is objective — stated at the
base altitude, where the timestamp is visible. -/
theorem wptImg_at (a : Int) (dq : DFrac) (v : BitVec 8) (ws : Wstate) :
    vwpHold (wptImg (GF := GF) a dq v) ws ⊣⊢ wlatPointsto (GF := GF) a dq 0 v := .rfl

/-! ### 3c. the algebra of the OWNED form

`wptOwn`'s decode is `wpt_at`'s with the state element carried alongside; it is the shape both
memory rules of §4/§5 destruct to. -/

theorem wptOwn_at_view (ξ : CtxId) (a : Int) (v : BitVec 8) (V : View) :
    (wptOwn (GF := GF) ξ a v).monPred_at V ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownCtx (GF := GF) ξ a t ∗
        ⌜t ≤ flr V a⌝ := by
  unfold wptOwn
  constructor
  · iintro ⟨%t, ⟨He, Hs⟩, %h⟩
    iexists t
    iframe He Hs
    ipureintro; exact (viewByte_le a t V).mp h
  · iintro ⟨%t, He, Hs, %h⟩
    iexists t
    isplitl [He Hs]
    · iframe He Hs
    · ipureintro; exact (viewByte_le a t V).mpr h

theorem wptOwn_at (ξ : CtxId) (a : Int) (v : BitVec 8) (ws : Wstate) :
    vwpHold (wptOwn (GF := GF) ξ a v) ws ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownCtx (GF := GF) ξ a t ∗
        ⌜t ≤ flr (wsView ws) a⌝ :=
  wptOwn_at_view ξ a v (wsView ws)

theorem wptOwn_at_intro (ξ : CtxId) (a : Int) (v : BitVec 8) (t : Nat) (ws : Wstate)
    (ht : t ≤ flr (wsView ws) a) :
    wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownCtx (GF := GF) ξ a t ⊢
      vwpHold (wptOwn (GF := GF) ξ a v) ws := by
  refine BIBase.Entails.trans ?_ (wptOwn_at ξ a v ws).mpr
  iintro ⟨He, Hs⟩
  iexists t
  iframe He Hs
  ipureintro; exact ht

/-! ### 3c''. THE HART-INDEXED BYTE FORM — `wptOwnH`, M-MODE ONLY

Stage 1.5's owned points-to, kept under a distinguishing name for ONE purpose: it is what the four-
and eight-byte OWNED TOWERS (`WeakStore.wpt4_own`, `WeakWord8.wpt8_own`) and the M-mode store
leaves built on them are stated over, and those never cross a migration (the M-mode boot chain runs
one context per hart from reset to `wp_next`).

IT IS NOT THE API.  A resource that names a hart does not frame across a yield, which is the whole
content of §1.6; anything that can be rescheduled must use `wptOwn`.  The two forms do not
interconvert except through the clean form `a ↦w v`, which both accept. -/

/-- Rocq `wpt_own_h`. -/
def wptOwnH (c : CPU) (a : Int) (v : BitVec 8) : VProp GF :=
  iprop(∃ t : Nat, ⎡wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownSt (GF := GF) c a⎤ ∗
    ⊒(viewByte a t))

theorem wptOwnH_at_view (c : CPU) (a : Int) (v : BitVec 8) (V : View) :
    (wptOwnH (GF := GF) c a v).monPred_at V ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownSt (GF := GF) c a ∗
        ⌜t ≤ flr V a⌝ := by
  unfold wptOwnH
  constructor
  · iintro ⟨%t, ⟨He, Hs⟩, %h⟩
    iexists t
    iframe He Hs
    ipureintro; exact (viewByte_le a t V).mp h
  · iintro ⟨%t, He, Hs, %h⟩
    iexists t
    isplitl [He Hs]
    · iframe He Hs
    · ipureintro; exact (viewByte_le a t V).mpr h

theorem wptOwnH_at (c : CPU) (a : Int) (v : BitVec 8) (ws : Wstate) :
    vwpHold (wptOwnH (GF := GF) c a v) ws ⊣⊢
      ∃ t : Nat, wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownSt (GF := GF) c a ∗
        ⌜t ≤ flr (wsView ws) a⌝ :=
  wptOwnH_at_view c a v (wsView ws)

theorem wptOwnH_at_intro (c : CPU) (a : Int) (v : BitVec 8) (t : Nat) (ws : Wstate)
    (ht : t ≤ flr (wsView ws) a) :
    wlatElem (GF := GF) a (DFrac.own 1) t v ∗ wownSt (GF := GF) c a ⊢
      vwpHold (wptOwnH (GF := GF) c a v) ws := by
  refine BIBase.Entails.trans ?_ (wptOwnH_at c a v ws).mpr
  iintro ⟨He, Hs⟩
  iexists t
  iframe He Hs
  ipureintro; exact ht

theorem wptOwnH_of_wpt (c : CPU) (a : Int) (v : BitVec 8) :
    (a ↦w v : VProp GF) ⊢ wptOwnH (GF := GF) c a v := by
  refine entails_at.mpr fun V => ?_
  refine (wpt_at_view a _ v V).mp.trans (BIBase.Entails.trans ?_ (wptOwnH_at_view c a v V).mpr)
  unfold wlatPointsto
  iintro ⟨%t, ⟨He, Hc⟩, %ht⟩
  iexists t
  iframe He
  isplitl [Hc]
  · iapply wcleanOwnSt (GF := GF) c a
    iexact Hc
  · ipureintro; exact ht

/-- A CLEAN full-fraction byte IS an owned byte, at EVERY context — a clean byte names no author,
so there is nothing to be indexed by.  The converse is NOT available in general: that is the whole
point of the D state, and recovering it is what a release's flip does. -/
theorem wptOwn_of_wpt (ξ : CtxId) (a : Int) (v : BitVec 8) :
    (a ↦w v : VProp GF) ⊢ wptOwn (GF := GF) ξ a v := by
  refine entails_at.mpr fun V => ?_
  refine (wpt_at_view a _ v V).mp.trans (BIBase.Entails.trans ?_ (wptOwn_at_view ξ a v V).mpr)
  unfold wlatPointsto
  iintro ⟨%t, ⟨He, Hc⟩, %ht⟩
  iexists t
  iframe He
  isplitl [Hc]
  · iapply wownCtxOfClean (GF := GF) ξ a t
    iexact Hc
  · ipureintro; exact ht

theorem wptOwn_mono (ξ : CtxId) (a : Int) (v : BitVec 8) (ws ws' : Wstate) (h : wsLe ws ws') :
    vwpHold (wptOwn (GF := GF) ξ a v) ws ⊢ vwpHold (wptOwn (GF := GF) ξ a v) ws' :=
  vwpHold_mono _ h

/-! ### 3c'. THE φ PAYMENT OF AN OWNED BYTE (φ-upgrade §1.6)

Every leaf owes `nvHart` at its post-log, one `WeakGhost.nvByte` per byte of its own effect trace.
For an owned byte the obligation is paid HERE, and by the SAME lemma whether or not the thread has
migrated since it last wrote the byte: `WeakGhost.nvOkOfWownCtx` does the case analysis
internally. -/

theorem nvOk_of_wptOwn (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8) (V : View)
    (img : GMapF PAddr (BitVec 8)) (log logA : List Wmsg) :
    pubTransfer logA log c →
    wlogAuth (GF := GF) logA ∗ ctxMigr (GF := GF) ξ c ∗ wlatInterp (GF := GF) img log ∗
      (wptOwn (GF := GF) ξ a v).monPred_at V ⊢ ⌜nvOk log c a⌝ := by
  intro htr
  iintro ⟨Hlog, Hmg, Hi, Hpt⟩
  icases (wptOwn_at_view ξ a v V).mp $$ Hpt with ⟨%t, Hel, Hs, -⟩
  iapply nvOkOfWownCtx ξ c a t v img log logA htr
  iframe Hlog Hmg Hi Hel Hs

theorem nvOk_of_wptOwn_at (ξ : CtxId) (c : CPU) (a : Int) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (ws : Wstate) :
    wlogAuth (GF := GF) log ∗ ctxMigr (GF := GF) ξ c ∗ wlatInterp (GF := GF) img log ∗
      vwpHold (wptOwn (GF := GF) ξ a v) ws ⊢ ⌜nvOk log c a⌝ :=
  nvOk_of_wptOwn ξ c a v (wsView ws) img log log (pubTransferRefl log c)

/-! ## 4. THE LOAD RULE

Event altitude: one byte, inside the `wp_wexec_step` callback.  What is being collapsed is
`WeakExec.wp_wexec_step`'s ∀-over-oracles: a weak read of byte `a` may return ANY admissible
timestamp, and the rule says every one of them carries the value `v` the points-to names.  The
timestamp genuinely varies (a racy cell case-splits); the VALUE cannot.

The pure heart is `WeakMem.readableLatestPin` (the collapse lemma): `wlatLookup` says my element IS
the latest write, my index says the floor covers its timestamp, and `readable`'s coherence window
then has room for exactly that one timestamp. -/

/-- The pure half both load rules share: an element that is the latest write, whose timestamp the
hart's floor covers, pins every admissible non-fetch read (Lean-only factoring of the two Rocq
proofs' common `assert`s). -/
private theorem loadPin (σ : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (v : BitVec 8) (t' : Nat)
    (b : BitVec 8) :
    ak.akIfetch = false → wbyteOk σ ak a t' b → latestVal (imgZ σ.wmImg) σ.wmLog a t v →
    t ≤ flr (wsView σ.wmWs) a → t' = t ∧ b = v := by
  intro hcoh hok hlat ht
  obtain ⟨hv, hadm⟩ := hok
  rw [hcoh] at hadm
  simp only [Bool.false_eq_true, ↓reduceIte] at hadm
  obtain ⟨hrd, -⟩ := hadm
  have htt : t' = t := by
    refine readableLatestPin (wimg σ) σ.wmLog σ.wmWs (loadVpre σ.wmWs ak.akSync) a t t'
      (latestValLatest _ _ _ _ _ hlat) ?_ hrd
    have := loadVpreVrNew σ.wmWs ak.akSync
    rw [flr_wsView] at ht
    omega
  subst htt
  refine ⟨rfl, ?_⟩
  have h1 : some b = some v := hv.symm.trans hlat.1
  exact Option.some.inj h1

theorem wpt_load_rule (σ σ' : Wmstate) (ak : AkInfo) (a : Int) (dq : DFrac) (v : BitVec 8)
    (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog →
    flr (wsView σ.wmWs) a ≤ flr (wsView σ'.wmWs) a →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wpt (GF := GF) a dq v) σ.wmWs ⊢
      ⌜b = v⌝ ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ vwpHold (wpt (GF := GF) a dq v) σ'.wmWs := by
  intro hcoh hok himg hlog hfl
  rw [himg, hlog]
  refine (sep_mono_right (wpt_at a dq v σ.wmWs).mp).trans ?_
  iintro ⟨Hi, ⟨%t, He, %ht⟩⟩
  ihave ⟨%hlat, Hi, He⟩ := persistent_entails_right (wlatLookup σ.wmImg σ.wmLog a dq t v) $$ [Hi He]
  · iframe Hi He
  obtain ⟨rfl, rfl⟩ := loadPin σ ak a t v t' b hcoh hok hlat ht
  isplitr
  · ipureintro; rfl
  iframe Hi
  iapply (wpt_at a dq b σ'.wmWs).mpr
  iexists t'
  iframe He
  ipureintro; omega

/-- The framing side conditions, discharged once and for all at the interpreter's own read
post-state: a read moves neither the image nor the log, and only RAISES the views. -/
theorem wpt_load_wread (σ : Wmstate) (ak : AkInfo) (a : Int) (dq : DFrac) (v : BitVec 8)
    (pa : PAddr) (ts : List Nat) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wpt (GF := GF) a dq v) σ.wmWs ⊢
      ⌜b = v⌝ ∗
      wlatInterp (GF := GF) (wreadPost σ ak pa ts).wmImg (wreadPost σ ak pa ts).wmLog ∗
      vwpHold (wpt (GF := GF) a dq v) (wreadPost σ ak pa ts).wmWs := fun hcoh hok =>
  wpt_load_rule σ _ ak a dq v t' b hcoh hok (wreadPostImg σ ak pa ts) (wreadPostLog σ ak pa ts)
    ((View.le_spec _ _).1 (wsView_mono _ _ (wreadPostWsLe σ ak pa ts)) a)

/-! ### 4'. THE OWNED LOAD RULE — a hart reads its OWN (possibly DIRTY) byte

`wpt_load_rule` goes through `WeakGhost.wlatLookup`, which wants the CLEAN half of the points-to; a
hart that has just plain-stored to a byte holds `↦wo` instead.  The collapse itself never needed the
state element: `WeakGhost.wlatLookupElem` is stated over the bare VALUE element, which is what
`wptOwn` carries.  IT NEEDS NO MIGRATION MACHINERY AT ALL: a load moves no `Wcds` state, so a byte
dirtied on a hart the context has since left reads through this rule VERBATIM. -/

theorem wpt_load_rule_own (ξ : CtxId) (σ σ' : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8)
    (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog →
    flr (wsView σ.wmWs) a ≤ flr (wsView σ'.wmWs) a →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      ⌜b = v⌝ ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
        vwpHold (wptOwn (GF := GF) ξ a v) σ'.wmWs := by
  intro hcoh hok himg hlog hfl
  rw [himg, hlog]
  refine (sep_mono_right (wptOwn_at ξ a v σ.wmWs).mp).trans ?_
  iintro ⟨Hi, ⟨%t, He, Hs, %ht⟩⟩
  ihave ⟨%hlat, Hi, He⟩ :=
    persistent_entails_right (wlatLookupElem σ.wmImg σ.wmLog a (DFrac.own 1) t v) $$ [Hi He]
  · iframe Hi He
  obtain ⟨rfl, rfl⟩ := loadPin σ ak a t v t' b hcoh hok hlat ht
  isplitr
  · ipureintro; rfl
  iframe Hi
  iapply (wptOwn_at ξ a b σ'.wmWs).mpr
  iexists t'
  iframe He Hs
  ipureintro; omega

/-- The framing side conditions at the interpreter's own read post-state, exactly as
`wpt_load_wread` discharges them for the clean form. -/
theorem wpt_load_wread_own (ξ : CtxId) (σ : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8)
    (pa : PAddr) (ts : List Nat) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      ⌜b = v⌝ ∗
      wlatInterp (GF := GF) (wreadPost σ ak pa ts).wmImg (wreadPost σ ak pa ts).wmLog ∗
      vwpHold (wptOwn (GF := GF) ξ a v) (wreadPost σ ak pa ts).wmWs := fun hcoh hok =>
  wpt_load_rule_own ξ σ _ ak a v t' b hcoh hok (wreadPostImg σ ak pa ts) (wreadPostLog σ ak pa ts)
    ((View.le_spec _ _).1 (wsView_mono _ _ (wreadPostWsLe σ ak pa ts)) a)

/-! ## 5. THE STORE RULE

Event altitude: one byte.  The store appends its message at the log's fresh top
`t' = log.length + 1` (promise-free: there is no admissibility condition to check), the `γlat`
element for `a` is updated to `(t', v')`, and `WeakGhost.wlatAgreeStore` re-establishes the state
interpretation's tie.  The post-view premise is the honest one: the hart's floor at `a` must cover
the new timestamp; `flr_storePost` discharges it at the machine's own `storePost`.

THE C/D/S SPLIT (φ-upgrade §1) gives the rule TWO ENTRY FORMS: the OWNED form, for a store that may
be `WCplain` (it consumes and produces `wptOwn`, because a plain store DIRTIES its byte), and the
CLEAN form, for a store that is not an owned store at all (an AMO's write half, a release: it
consumes and produces `↦w`, which keeps a lock word held clean inside an invariant clean). -/

/-- The ghost half of the owned store (Lean-only helper, deviation 10): both ghost-map updates and
the re-established ties, at the store's fresh top. -/
theorem wlatStoreOwnStep (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (m : Wmsg)
    (a : Int) (t : Nat) (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    wlatInterp (GF := GF) img log ∗ wlatElem (GF := GF) a (DFrac.own 1) t v ∗
      wownSt (GF := GF) c a ⊢
      |==> (wlatInterp (GF := GF) img (log ++ [m]) ∗
        wlatElem (GF := GF) a (DFrac.own 1) (log.length + 1) v' ∗ wownSt (GF := GF) c a) := by
  intro hma hother htid
  unfold wlatInterp wlatElem wownSt wcdsEl
  iintro ⟨⟨%mm, %mc, Hauth, %hag, Hcauth, %hagc⟩, He, ⟨%s, Hsel, %hs⟩⟩
  icombine Hcauth Hsel gives %hlk
  imod ghost_map_update (log.length + 1, v') $$ Hauth He with ⟨Hauth, He⟩
  imod ghost_map_update (wcdsOwnStep c m.wmAk s) $$ Hcauth Hsel with ⟨Hcauth, Hsel⟩
  imodintro
  isplitl [Hauth Hcauth]
  · iexists insert mm a (log.length + 1, v'), insert mc a (wcdsOwnStep c m.wmAk s)
    iframe Hauth Hcauth
    isplit
    · ipureintro; exact wlatAgreeStore _ log m a v' mm hma hother hag
    · ipureintro
      intro a' s' ha'
      by_cases h : a' = a
      · subst h
        rw [lookupInsert] at ha'
        cases ha'
        exact wcdsOkStoreOwn log m a' c s htid hs (hagc a' s hlk)
      · rw [lookupInsertNe (Ne.symm h)] at ha'
        refine wcdsOkApp log [m] a' s' ?_ (hagc a' s' ha')
        intro m0 hm0
        rw [List.mem_singleton] at hm0
        subst hm0
        exact hother a' h
  · iframe He
    iexists wcdsOwnStep c m.wmAk s
    iframe Hsel
    ipureintro
    cases m.wmAk with
    | WCplain => exact .inr rfl
    | WCrel => exact .inl rfl
    | WCexcl => exact hs

/-- THE OWNED STORE, Stage 1.6 shape.  Beyond the Stage-1.5 statement it takes the LOG AUTHORITY at
the POST-log (which every store leaf already holds; the retarget reads the foreign author's
publication floor off it, and the mint reads the position bound) and `ctxMigr ξ c`, the scheduler's
migration invariant — and nothing else.  The case split "did this context dirty `a` on a hart it
has since left?" happens INSIDE, in `WeakGhost.wownCtxRetarget`, so the store site's script is the
same before and after a yield. -/
theorem wpt_store_rule_own (ξ : CtxId) (c : CPU) (σ σ' : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [m] →
    σ.wmLog.length + 1 ≤ flr (wsView σ'.wmWs) a →
    wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) ξ c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) ξ c ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v') σ'.wmWs) := by
  intro hma hother htid himg hlog hfl
  rw [himg, hlog]
  refine (sep_mono_right (sep_mono_right (sep_mono_right (wptOwn_at ξ a v σ.wmWs).mp))).trans ?_
  iintro ⟨Hlg, Hmg, Hi, ⟨%t, He, Hs, -⟩⟩
  -- THE RETARGET, and the log-authority offset it tolerates: the store's own message is `c`'s, so
  -- it publishes nothing for any other hart
  imod wownCtxRetarget ξ c a t v σ.wmImg σ.wmLog (σ.wmLog ++ [m])
      (pubTransferSnoc σ.wmLog m c htid) $$ [Hlg Hmg Hi He Hs] with ⟨Hlg, Hmg, Hi, He, Hs⟩
  · iframe Hlg Hmg Hi He Hs
  -- THE MINT, at the store's own fresh top
  imod ctxMigrMint ξ c (σ.wmLog ++ [m]) (σ.wmLog.length + 1)
      (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _) $$ [Hlg Hmg] with ⟨Hlg, Hmg, #Hbc⟩
  · iframe Hlg Hmg
  ihave #Hbca := ctxWroteByte (GF := GF) ξ c a (σ.wmLog.length + 1) $$ [Hbc]
  · iexact Hbc
  imod wlatStoreOwnStep c σ.wmImg σ.wmLog m a t v v' hma hother htid $$ [Hi He Hs]
      with ⟨Hi, He, Hs⟩
  · iframe Hi He Hs
  imodintro
  iframe Hlg Hmg Hi
  iapply (wptOwn_at ξ a v' σ'.wmWs).mpr
  iexists σ.wmLog.length + 1
  iframe He
  isplitl [Hs]
  · iapply wownCtxOfOwnSt (GF := GF) ξ c a (σ.wmLog.length + 1)
    iframe Hs Hbca
  · ipureintro; exact hfl

theorem wpt_store_rule (σ σ' : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmAk ≠ .WCplain →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [m] →
    σ.wmLog.length + 1 ≤ flr (wsView σ'.wmWs) a →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦w v : VProp GF) σ.wmWs ⊢
      |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ vwpHold (a ↦w v' : VProp GF) σ'.wmWs) := by
  intro hma hother hk himg hlog hfl
  rw [himg, hlog]
  refine (sep_mono_right (wpt_at a _ v σ.wmWs).mp).trans ?_
  refine BIBase.Entails.trans ?_ (bupd_mono (sep_mono_right (wpt_at a _ v' σ'.wmWs).mpr))
  unfold wlatInterp wlatPointsto wlatElem wclean wcdsEl
  iintro ⟨⟨%mm, %mc, Hauth, %hag, Hcauth, %hagc⟩, ⟨%t, ⟨He, Hc⟩, -⟩⟩
  imod ghost_map_update (σ.wmLog.length + 1, v') $$ Hauth He with ⟨Hauth, He⟩
  -- T2-0: `wcdsOkStoreNonplain` is false at a `WLock` byte, so the framing needs the ONE byte this
  -- message writes to be non-`WLock` — which the points-to's own `wclean` half says.
  icombine Hcauth Hc gives %hK
  imodintro
  isplitl [Hauth Hcauth]
  · iexists insert mm a (σ.wmLog.length + 1, v'), mc
    iframe Hauth Hcauth
    isplit
    · ipureintro; exact wlatAgreeStore _ _ m a v' mm hma hother hag
    · ipureintro; exact wcdsAgreeNonplain1 _ m mc a WClean hk rfl hother hK hagc
  · iexists σ.wmLog.length + 1
    iframe He Hc
    ipureintro; exact hfl

/-- At the machine's own store post-state, the post-view premise is automatic. -/
theorem wpt_store_post (σ : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8) (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmAk ≠ .WCplain →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦w v : VProp GF) σ.wmWs ⊢
      |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (a ↦w v' : VProp GF) (storePost σ.wmWs rl a (σ.wmLog.length + 1))) :=
  fun hma hother hk =>
    wpt_store_rule σ
      { σ with wmLog := σ.wmLog ++ [m], wmWs := storePost σ.wmWs rl a (σ.wmLog.length + 1) }
      m a v v' hma hother hk rfl rfl (flr_storePost _ _ _ _)

/-- The owned twin. -/
theorem wpt_store_post_own (ξ : CtxId) (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int)
    (v v' : BitVec 8) (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) ξ c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ a v) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) ξ c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (wptOwn (GF := GF) ξ a v') (storePost σ.wmWs rl a (σ.wmLog.length + 1))) :=
  fun hma hother htid =>
    wpt_store_rule_own ξ c σ
      { σ with wmLog := σ.wmLog ++ [m], wmWs := storePost σ.wmWs rl a (σ.wmLog.length + 1) }
      m a v v' hma hother htid rfl rfl (flr_storePost _ _ _ _)

end PointsToLaws

/-! ## 5b. THE AMBIENT API (φ-upgrade §1.7)

The rules above, with the context read out of the `CurCtx` instance instead of taken as an
argument.  They are THIN WRAPPERS and nothing else — each is its primitive applied at
`CurCtx.curCtx` — and the primitives stay exactly as they were, because a proof with two contexts
in scope must be able to use them at both (§3''). -/

section CurCtxApi
variable {GF : BundledGFunctors} [WeakGS GF] [XI : CurCtx]

/-- A clean full-fraction byte is owned by the ambient context — the receiving side of a transfer,
in one line. -/
theorem wptOwn_of_wpt_cur (a : Int) (v : BitVec 8) : (a ↦w v : VProp GF) ⊢ a ↦wo v :=
  wptOwn_of_wpt _ a v

/-- THE OWNED LOAD (§4'), ambient. -/
theorem wpt_load_rule_own_cur (σ σ' : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8) (t' : Nat)
    (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog →
    flr (wsView σ.wmWs) a ≤ flr (wsView σ'.wmWs) a →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ.wmWs ⊢
      ⌜b = v⌝ ∗ wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ'.wmWs :=
  wpt_load_rule_own _ σ σ' ak a v t' b

theorem wpt_load_wread_own_cur (σ : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8) (pa : PAddr)
    (ts : List Nat) (t' : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ.wmWs ⊢
      ⌜b = v⌝ ∗
      wlatInterp (GF := GF) (wreadPost σ ak pa ts).wmImg (wreadPost σ ak pa ts).wmLog ∗
      vwpHold (a ↦wo v : VProp GF) (wreadPost σ ak pa ts).wmWs :=
  wpt_load_wread_own _ σ ak a v pa ts t' b

/-- THE OWNED STORE (§5), ambient.  The hart `c` stays explicit: it is the hart the STEP runs on,
which the machine supplies and which genuinely varies — it is not the thing §1.7 makes ambient. -/
theorem wpt_store_rule_own_cur (c : CPU) (σ σ' : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [m] →
    σ.wmLog.length + 1 ≤ flr (wsView σ'.wmWs) a →
    wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) σ'.wmLog ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
        wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗ vwpHold (a ↦wo v' : VProp GF) σ'.wmWs) :=
  wpt_store_rule_own _ c σ σ' m a v v'

theorem wpt_store_post_own_cur (c : CPU) (σ : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8)
    (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmTid = some c.val →
    wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (a ↦wo v : VProp GF) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (σ.wmLog ++ [m]) ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
        wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m]) ∗
        vwpHold (a ↦wo v' : VProp GF) (storePost σ.wmWs rl a (σ.wmLog.length + 1))) :=
  wpt_store_post_own _ c σ m a v v' rl

/-- THE φ PAYMENT (§3c'), ambient — the lemma every access site applies, migrated or not. -/
theorem nvOk_of_wptOwn_cur (c : CPU) (a : Int) (v : BitVec 8) (V : View)
    (img : GMapF PAddr (BitVec 8)) (log logA : List Wmsg) :
    pubTransfer logA log c →
    wlogAuth (GF := GF) logA ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) img log ∗ (a ↦wo v : VProp GF).monPred_at V ⊢ ⌜nvOk log c a⌝ :=
  nvOk_of_wptOwn _ c a v V img log logA

theorem nvOk_of_wptOwn_at_cur (c : CPU) (a : Int) (v : BitVec 8) (img : GMapF PAddr (BitVec 8))
    (log : List Wmsg) (ws : Wstate) :
    wlogAuth (GF := GF) log ∗ ctxMigr (GF := GF) CurCtx.curCtx c ∗
      wlatInterp (GF := GF) img log ∗ vwpHold (a ↦wo v : VProp GF) ws ⊢ ⌜nvOk log c a⌝ :=
  nvOk_of_wptOwn_at _ c a v img log ws

end CurCtxApi

/-! ## 6. The monPred altitude

The DERIVED statements: the same two rules with the hart's index spelled as a `View` and the
points-to frozen at it.  These are what the M3 lock library will quote — and they are three lines
each, which is the point of the discipline. -/

section VPropAltitude
variable {GF : BundledGFunctors} [WeakGS GF]

theorem vwpHold_view_at_iff (P : VProp GF) (ws : Wstate) :
    vwpHold P ws ⊣⊢ vwpHold (P @@ wsView ws) ws :=
  vwpHold_freeze P ws

/-- THE LOAD RULE, `VProp` altitude: at the hart's index, an owned byte pins the value of every
admissible weak read of it. -/
theorem wpt_load_vprop (σ : Wmstate) (ak : AkInfo) (a : Int) (dq : DFrac) (v : BitVec 8) (t' : Nat)
    (b : BitVec 8) :
    ak.akIfetch = false →
    wbyteOk σ ak a t' b →
    (iprop(⎡wlatInterp (GF := GF) σ.wmImg σ.wmLog⎤ ∗ (a ↦w{dq} v) @@ wsView σ.wmWs) : VProp GF) ⊢
      ⌜b = v⌝ := fun hcoh hok =>
  entails_at.mpr fun _ =>
    (wpt_load_rule σ σ ak a dq v t' b hcoh hok rfl rfl (Nat.le_refl _)).trans sep_elim_left

/-- THE STORE RULE, `VProp` altitude. -/
theorem wpt_store_vprop (σ : Wmstate) (m : Wmsg) (a : Int) (v v' : BitVec 8) (rl : Bool) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    m.wmAk ≠ .WCplain →
    (iprop(⎡wlatInterp (GF := GF) σ.wmImg σ.wmLog⎤ ∗ (a ↦w v) @@ wsView σ.wmWs) : VProp GF) ⊢
      |==> (⎡wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [m])⎤ ∗
        (a ↦w v') @@ wsView (storePost σ.wmWs rl a (σ.wmLog.length + 1))) := fun hma hother hk =>
  entails_at.mpr fun _ => wpt_store_post σ m a v v' rl hma hother hk

end VPropAltitude

/-! ## 7. THE DEMO — a whole ACCESS, end to end through the interpreter

The event rules above are per-byte.  This section runs them through `WeakInterp`'s own read arm at
the width the machine actually uses, i.e. over the `wreadOk` obligation that `wrun`/`wexec` produce
for ONE `MemRead` — an `lb`/`lh`/`lw`/`ld`-class access, at any `n`.  Owning the `n` bytes at the
hart's index pins the whole assembled word.  This is the interface-composition check M2a is for:
the `VProp` points-to, the `vwpHold` discipline, `WeakGhost`'s latest-write tie and `WeakInterp`'s
admissibility predicate compose with no impedance mismatch, at the altitude of a real memory
access. -/

section Demo
variable {GF : BundledGFunctors} [WeakGS GF]

/-- One byte of an access. -/
theorem wpt_wread_byte (σ : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) (dq : DFrac) (b : BitVec 8) (j : Nat) :
    ak.akIfetch = false →
    j < n →
    wreadOk σ ak pa n ts w →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      vwpHold (WeakInterp.accAddr pa j ↦w{dq} b : VProp GF) σ.wmWs ⊢ ⌜nthByte w j = b⌝ := by
  rintro hcoh hj ⟨-, hbytes⟩
  exact (wpt_load_rule σ σ ak _ dq b _ _ hcoh (hbytes j hj) rfl rfl (Nat.le_refl _)).trans
    sep_elim_left

/-- The whole access: every byte of the returned word is the byte owned at that address.  `j` is a
Lean-level parameter, so the "for every byte" reading is the ∀ in front of the lemma — no induction
over the access width is needed, and the `wlatInterp` authority is consumed once. -/
theorem wpt_wread_bytes (σ : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) (dq : DFrac) (bs : List (BitVec 8)) (j : Nat) :
    ak.akIfetch = false →
    bs.length = n →
    j < n →
    wreadOk σ ak pa n ts w →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      ([∗list] j' ↦ b ∈ bs, vwpHold (WeakInterp.accAddr pa j' ↦w{dq} b : VProp GF) σ.wmWs) ⊢
      ⌜nthByte w j = bs[j]!⌝ := by
  intro hcoh hlen hj hok
  have hlk : bs[j]? = some bs[j]! := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [getElem!_pos, show j < bs.length by omega]
  exact (sep_mono_right (BigSepL.bigSepL_lookup
      (Φ := fun j' b => vwpHold (WeakInterp.accAddr pa j' ↦w{dq} b : VProp GF) σ.wmWs) hlk)).trans
    (wpt_wread_byte σ ak pa n ts w dq _ j hcoh hj hok)

/-- ... hence the READ VALUE IS DETERMINED: whatever timestamps the oracle chose, the word
`wrun`/`wexec` returns is the little-endian assembly of the bytes I own.  This is the statement a
real load leaf consumes. -/
theorem wpt_wread_word (σ : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) (dq : DFrac) (bs : List (BitVec 8)) :
    ak.akIfetch = false →
    bs.length = n →
    wreadOk σ ak pa n ts w →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      ([∗list] j' ↦ b ∈ bs, vwpHold (WeakInterp.accAddr pa j' ↦w{dq} b : VProp GF) σ.wmWs) ⊢
      ⌜w = assembleBytes n (fun j => bs[j]!)⌝ := by
  intro hcoh hlen hok
  by_cases hall : ∀ j, j < n → nthByte w j = bs[j]!
  · exact BI.pure_intro (bvEqOfBytes w _ fun j hj =>
      (hall j hj).trans (nthByteAssembleBytes n _ j hj).symm)
  · obtain ⟨j, hj⟩ := Classical.not_forall.mp hall
    have hj1 : j < n := Classical.byContradiction fun h => hj fun h' => absurd h' h
    have hj2 : ¬ nthByte w j = bs[j]! := fun h => hj fun _ => h
    exact (wpt_wread_bytes σ ak pa n ts w dq bs j hcoh hlen hj1 hok).trans
      (pure_mono fun h => absurd h hj2)

/-- The STORE side of the demo: the message `WeakInterp` appends for a ONE-BYTE store writes
exactly the byte it should, which is what discharges the store rule's two `msgByte` side conditions
at the real interpreter. -/
theorem wwriteMsg_byte1 (tid : Option Nat) (k : WmClass) (pa : PAddr) (v : BitVec (8 * 1)) :
    msgByte (wwriteMsg tid k pa 1 v) (paZ pa) = some (nthByte v 0) := by
  have := wwriteMsgByte tid k pa 1 v 0 (by omega)
  rwa [WeakInterp.accAddr0] at this

theorem wwriteMsg_byte1_none (tid : Option Nat) (k : WmClass) (pa : PAddr) (v : BitVec (8 * 1))
    (a : Int) : a ≠ paZ pa → msgByte (wwriteMsg tid k pa 1 v) a = none := by
  intro hne
  simp only [msgByte, wwriteMsg]
  split
  · apply List.getElem?_eq_none
    simp only [List.length_map, List.length_range']
    omega
  · rfl

/-- ... so the store rule fires at the interpreter's own write post-state, with no side condition
left for the caller beyond the value. -/
theorem wpt_wwrite_byte (ξ : CtxId) (c : CPU) (σ : Wmstate) (ak : AkInfo) (pa : PAddr)
    (v : BitVec (8 * 1)) (v0 : BitVec 8) :
    wlogAuth (GF := GF) (wwritePost (some c.val) σ ak pa 1 v).wmLog ∗ ctxMigr (GF := GF) ξ c ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗ vwpHold (wptOwn (GF := GF) ξ (paZ pa) v0) σ.wmWs ⊢
      |==> (wlogAuth (GF := GF) (wwritePost (some c.val) σ ak pa 1 v).wmLog ∗
        ctxMigr (GF := GF) ξ c ∗
        wlatInterp (GF := GF) (wwritePost (some c.val) σ ak pa 1 v).wmImg
          (wwritePost (some c.val) σ ak pa 1 v).wmLog ∗
        vwpHold (wptOwn (GF := GF) ξ (paZ pa) (nthByte v 0))
          (wwritePost (some c.val) σ ak pa 1 v).wmWs) := by
  refine wpt_store_rule_own ξ c σ (wwritePost (some c.val) σ ak pa 1 v)
    (wwriteMsg (some c.val) (wmClassOf ak σ.wmWs) pa 1 v) (paZ pa) v0 (nthByte v 0)
    (wwriteMsg_byte1 _ _ _ _) (fun a' h => wwriteMsg_byte1_none _ _ _ _ a' h) rfl rfl rfl ?_
  have e : paZ pa + ((0 : Nat) : Int) = paZ pa := by omega
  have h := flr_storePost σ.wmWs ak.akSync (paZ pa + ((0 : Nat) : Int)) (σ.wmLog.length + 1)
  rw [e] at h
  exact h

end Demo

end Weak
