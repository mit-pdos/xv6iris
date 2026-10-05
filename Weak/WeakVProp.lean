/-
Weak: THE WEAK BYTE POINTS-TO AND THE `vwpHold` DISCIPLINE (Rocq `iris/WeakVProp.v` @ xxvzwolszwmp
(1cc222280); M2a) — the MonPred spike's second file, PARTIAL: the monPred altitude only.

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

WHAT THIS FILE IS.  `WeakVProp.v` imports `WeakMem` (`wstate`, `ws_le`, `coh`), `WeakInterp`
(`wmstate`, `wbyte_ok`, `wread_post`, `store_post`) and `WeakGhost` (`weakGS`, `wlat_elem`,
`wclean`, `wlat_interp`, `wown_ctx`, `ctx_migr`, …) — 7.8k Rocq lines, not yet ported (`WeakMem` is
another lane's).  Everything in the Rocq file that is ABOUT `monPred` is here and fully proved; the
parts that are pure `WeakMem`/`WeakGhost` reasoning ("with no monPred in sight", per the header) are
listed under Not ported and land with those files.  To do so without porting the dependencies, two
SEAMS stand in for them, each a class the dependency's port instantiates:

* `WsIndex WS` — the hart weak state's index (Rocq §1: `ws_view`, `ws_le`, `ws_view_mono`).  The
  `WeakMem` port supplies `instance : WsIndex WState` with `wsView ws := ⟨ws.vrNew, ws.coh⟩` and
  `wsView_mono := ws_view_mono`; every lemma below is then literally the Rocq statement.
* `WLatG GF S` — the two ghost maps of `WeakGhost.weakGS` this file reads (`weak_lat_name`,
  `weak_cds_name`), with the C/D/S state type `S` and its `WClean` constructor abstract.  The
  base-altitude elements `wlatElem`, `wcdsEl`, `wclean`, `wlatPointsto` are DEFINED here over it,
  exactly as `WeakGhost.v` defines them, so §3a's ghost-map lemmas are genuinely proved; the
  `WeakGhost` port replaces the class by `weakGS` (with `S := wcds`, `clean := WClean`) and moves
  the four definitions home.

Deviations from Rocq.
1. §1 is replaced by the `WsIndex` seam (above); `vwp_hold P ws` is `vwpHold P ws` for any
   `[WsIndex WS]`.  `flr_ws_view`, `ws_view_mono`, `ws_view_init`, `flr_store_post`,
   `flr_load_post_at` are WeakMem facts and are not ported here.
2. `wlat_elem`/`wcds_el`/`wclean`/`wlat_pointsto` are local copies of `WeakGhost.v`'s, over the
   `WLatG` seam (above).
3. `Section rules`' `riscvGS Σ` context is dropped: nothing ported here uses it.
4. Rocq's dfrac notation `a ↦w{dq} v` / `a ↦w□ v` / `a ↦w{# q} v` / `a ↦w v` becomes the Lean
   notations `a ↦w{dq} v` / `a ↦w□ v` / `a ↦w{DFrac.own q} v` / `a ↦w v` (no custom dfrac
   entry); the address is an `Int` (Rocq `Z`), the byte a `BitVec 8` (Rocq `bv 8`).
5. `vwp_hold_ne` / `vwp_hold_proper` / `vwp_hold_mono'` (setoid instances) are the theorems
   `vwpHold_ne` / `vwpHold_proper` / `vwpHold_mono'`; iris-lean's OFE equality is Leibniz, so
   `proper` is stated over `⊣⊢`.
6. PRECEDENCE PITFALL (measured): iris-lean's `|==> P ∗ Q` parses as `(|==> P) ∗ Q` (`|==>`
   takes `term:40`, `∗` is 35); Rocq's is `|==> (P ∗ Q)`.  Every such conclusion is parenthesised.

Name map (Rocq → Lean): `vwp_hold`→`vwpHold`, `vwp_hold_*`→`vwpHold_*` (`ne`, `proper`, `mono'`,
`mono`, `ent`, `intro`, `sep`, `exist`, `pure`, `embed`, `bupd`, `seen`, `seen_self`, `view_at`,
`freeze`, `thaw`), `wpt`→`wpt`, `wpt_at_view`→`wpt_at_view`, `wpt_at`→`wpt_at`, `wpt_at_intro`→
`wpt_at_intro`, `wlat_elem_agree`→`wlatElem_agree`, `wlat_pointsto_agree/valid_2/persist/split/
persistent/timeless`→`wlatPointsto_agree/valid_2/persist/split/persistent/timeless`,
`wpt_persistent/timeless/agree/valid_2/split/persist`→ same, `wpt_img`→`wptImg`,
`wpt_img_objective/persistent/wpt/at`→`wptImg_objective/persistent/wpt/at`; seams `WsIndex`,
`WLatG` are new.

Not ported (all blocked on WeakMem/WeakInterp/WeakGhost/WeakCtx, which this lane does not own; none
is a monPred question): §1 `ws_view` and its five lemmas (deviation 1); §3' `wpt_own`, §3''
`CurCtx`/`cur_ctx`/`↦wo`, §3c `wpt_own_at_view`/`wpt_own_at`/`wpt_own_at_intro`/`wpt_own_of_wpt`/
`wpt_own_mono`, §3c'' `wpt_own_h` and its four lemmas (need `CtxId`, `CPU`, `wown_ctx`, `wown_st`);
§3c' `nv_ok_of_wpt_own(_at)`; §4 `wpt_load_rule`, `wpt_load_wread`, §4' `wpt_load_rule_own`,
`wpt_load_wread_own`; §5 `wpt_store_rule_own`, `wpt_store_rule`, `wpt_store_post`,
`wpt_store_post_own`; §5b the eight `_cur` wrappers; §6 `vwp_hold_view_at_iff`,
`wpt_load_vprop`, `wpt_store_vprop`; §7 `wpt_wread_byte/bytes/word`, `wwrite_msg_byte1(_none)`,
`wpt_wwrite_byte`.  `wpt_own*` decode exactly as `wpt_at_view` does (same proof shape).

Statements checked: every lemma above, against `WeakVProp.v`, modulo deviations 1–4.
-/
import Weak.WeakView
import MachCSL.MonPredExtra
import Iris.Instances.Lib.GhostMap

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std MachCSL

/-! ## 1. The hart index — THE SEAM (deviation 1)

A hart's LOGICAL INDEX at a program point is its semantic read floor: the scalar pre-view `w_vrNew`
joined with the per-byte coherence map `w_coh` (design doc, Decision 5).  That is exactly a `View`,
and the machine's own per-field `ws_le` IS the index order. -/

/-- The weak state's view and its order (Rocq `ws_view`, `ws_le`, `ws_view_mono`). -/
class WsIndex (WS : Type _) where
  wsView : WS → View
  wsLe : WS → WS → Prop
  wsView_mono : ∀ {ws ws' : WS}, wsLe ws ws' → wsView ws ≤ wsView ws'

export WsIndex (wsView wsLe wsView_mono)

/-! ## 2. `vwpHold` — the discipline

"`P` holds at the hart whose weak state is `ws`".  Everything below is stated through it. -/

section Rules
variable {GF : BundledGFunctors} {WS : Type _} [WsIndex WS]

/-- Rocq `vwp_hold`. -/
def vwpHold (P : VProp GF) (ws : WS) : IProp GF := P.monPred_at (wsView ws)

theorem vwpHold_ne (ws : WS) : OFE.NonExpansive (fun P : VProp GF => vwpHold P ws) :=
  ⟨fun _ _ _ h => dist_at.mp h _⟩

theorem vwpHold_proper (ws : WS) {P Q : VProp GF} (h : P ⊣⊢ Q) : vwpHold P ws ⊣⊢ vwpHold Q ws :=
  ⟨entails_at.mp h.mp _, entails_at.mp h.mpr _⟩

theorem vwpHold_mono' (ws : WS) {P Q : VProp GF} (h : P ⊢ Q) : vwpHold P ws ⊢ vwpHold Q ws :=
  entails_at.mp h _

/-- THE WORKHORSE.  A step only ever raises the hart's views, so every premise the step did not
touch survives it with no work at all. -/
theorem vwpHold_mono (P : VProp GF) {ws ws' : WS} (h : wsLe ws ws') : vwpHold P ws ⊢ vwpHold P ws' :=
  P.monPred_mono (wsView_mono h)

/-- A `VProp` entailment used INSIDE the discipline (the `apply`-shaped twin of `vwpHold_mono'`). -/
theorem vwpHold_ent {P Q : VProp GF} (ws : WS) (h : P ⊢ Q) : vwpHold P ws ⊢ vwpHold Q ws :=
  vwpHold_mono' ws h

/-- ... and its index-level twin: an obligation stated at an index BELOW the hart's is an obligation
at the hart.  This is the seam a future `VProp`-level WP would be defined over. -/
theorem vwpHold_intro (V : View) (P : VProp GF) (ws : WS) (h : V ≤ wsView ws) :
    P.monPred_at V ⊢ vwpHold P ws :=
  P.monPred_mono h

/-- The structural laws — all definitional unfoldings of `monPred_at`. -/
theorem vwpHold_sep (P Q : VProp GF) (ws : WS) :
    vwpHold iprop(P ∗ Q) ws ⊣⊢ vwpHold P ws ∗ vwpHold Q ws := .rfl
theorem vwpHold_exist {A : Type _} (Φ : A → VProp GF) (ws : WS) :
    vwpHold iprop(∃ x, Φ x) ws ⊣⊢ ∃ x, vwpHold (Φ x) ws := monPred_at_exist _ Φ
theorem vwpHold_pure (φ : Prop) (ws : WS) : vwpHold (iprop(⌜φ⌝) : VProp GF) ws ⊣⊢ ⌜φ⌝ := .rfl
theorem vwpHold_embed (R : IProp GF) (ws : WS) : vwpHold (iprop(⎡R⎤) : VProp GF) ws ⊣⊢ R := .rfl
theorem vwpHold_bupd (P : VProp GF) (ws : WS) :
    vwpHold iprop(|==> P) ws ⊣⊢ |==> vwpHold P ws := .rfl

/-- The seen assertion at the hart IS the index inequality. -/
theorem vwpHold_seen (V : View) (ws : WS) :
    vwpHold (⊒V : VProp GF) ws ⊣⊢ ⌜V ≤ wsView ws⌝ := .rfl

theorem vwpHold_seen_self (ws : WS) : ⊢ vwpHold (⊒(wsView ws) : VProp GF) ws :=
  seen_at_self (wsView ws)

/-- THE SPLIT AXIOM, transported to the discipline.  `P @@ V` is index-free (objective), so its
value at the hart is just `P`'s value at `V`. -/
theorem vwpHold_view_at (P : VProp GF) (V : View) (ws : WS) :
    vwpHold (P @@ V) ws ⊣⊢ P.monPred_at V := .rfl

theorem vwpHold_freeze (P : VProp GF) (ws : WS) : vwpHold P ws ⊣⊢ vwpHold (P @@ wsView ws) ws :=
  .rfl

theorem vwpHold_thaw (V : View) (P : VProp GF) (ws : WS) (h : V ≤ wsView ws) :
    vwpHold (P @@ V) ws ⊢ vwpHold P ws :=
  vwpHold_intro V P ws h

end Rules

/-! ## 3. The byte points-to

`a ↦w{dq} v` — "the LATEST write to byte `a` is `(t, v)` for some timestamp `t`, AND I have
observed `t`".  The first conjunct is the base-layer element (`wlatPointsto`, objective — it is an
embedded `IProp`); the second is the receipt that makes the assertion SUBJECTIVE, and is the entire
difference between this and the SC points-to.  Mutable RAM bytes are the only subjective footprint
in the whole design (design doc, Decision 5). -/

/-- THE GHOST SEAM (deviation 2): the latest-write map `γlat : Int ⇀ (Nat × BitVec 8)` and the
C/D/S state map `γcds : Int ⇀ S` of `WeakGhost.weakGS`, with the clean state `clean`. -/
class WLatG (GF : BundledGFunctors) (S : outParam (Type _)) where
  [latG : GhostMapG GF Int (Nat × BitVec 8) (GMapF Int)]
  [cdsG : GhostMapG GF Int S (GMapF Int)]
  latName : GName
  cdsName : GName
  clean : S

attribute [reducible, instance] WLatG.latG WLatG.cdsG

section PointsTo
variable {GF : BundledGFunctors} {S : Type _} [WLatG GF S]

/-- The VALUE element (Rocq `WeakGhost.wlat_elem`). -/
def wlatElem (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) : IProp GF :=
  ghost_map_elem (WLatG.latName (GF := GF)) dq a (t, v)

/-- The STATE element (Rocq `WeakGhost.wcds_el`). -/
def wcdsEl (a : Int) (dq : DFrac) (s : S) : IProp GF :=
  ghost_map_elem (WLatG.cdsName (GF := GF)) dq a s

/-- Rocq `WeakGhost.wclean`. -/
def wclean (a : Int) (dq : DFrac) : IProp GF := wcdsEl (GF := GF) a dq (WLatG.clean (GF := GF))

/-- The base-altitude points-to: value element plus clean state (Rocq `WeakGhost.wlat_pointsto`). -/
def wlatPointsto (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) : IProp GF :=
  iprop(wlatElem (GF := GF) a dq t v ∗ wclean (GF := GF) a dq)

/-- Rocq `wpt`. -/
def wpt (a : Int) (dq : DFrac) (v : BitVec 8) : VProp GF :=
  iprop(∃ t : Nat, ⎡wlatPointsto (GF := GF) a dq t v⎤ ∗ ⊒(viewByte a t))

end PointsTo

notation:50 a:50 " ↦w{" dq "} " v:50 => wpt a dq v
notation:50 a:50 " ↦w□ " v:50 => wpt a DFrac.discard v
notation:50 a:50 " ↦w " v:50 => wpt a (DFrac.own 1) v

section PointsToLaws
variable {GF : BundledGFunctors} {S : Type _} [WLatG GF S] {WS : Type _} [WsIndex WS]

/-- THE DECODE LEMMA, and the seam between the two altitudes: at an index, the points-to is exactly
"an element of the latest-write map, whose timestamp the index's floor for `a` covers".  Every rule
is proved through this and never mentions `MonPred` again.  Stated at an ARBITRARY index, because
the framing pattern needs the decode at a FROZEN index. -/
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

theorem wpt_at (a : Int) (dq : DFrac) (v : BitVec 8) (ws : WS) :
    vwpHold (wpt (GF := GF) a dq v) ws ⊣⊢
      ∃ t : Nat, wlatPointsto (GF := GF) a dq t v ∗ ⌜t ≤ flr (wsView ws) a⌝ :=
  wpt_at_view a dq v (wsView ws)

/-- The introduction form: owning the element and covering its timestamp is the points-to. -/
theorem wpt_at_intro (a : Int) (dq : DFrac) (v : BitVec 8) (t : Nat) (ws : WS)
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
  have hE := (ghost_map_elem_fractional (GF := GF) (WLatG.latName (GF := GF)) a (t, v)).fractional q1 q2
  have hC := (ghost_map_elem_fractional (GF := GF) (WLatG.cdsName (GF := GF)) a (WLatG.clean (GF := GF))).fractional
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
    (a ↦w{DFrac.own (q1 + q2)} v : VProp GF) ⊣⊢ iprop(a ↦w{DFrac.own q1} v ∗ a ↦w{DFrac.own q2} v) := by
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

A byte whose latest write is the ERA-INITIAL IMAGE — timestamp 0 — carries a points-to with NO
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
theorem wptImg_at (a : Int) (dq : DFrac) (v : BitVec 8) (ws : WS) :
    vwpHold (wptImg (GF := GF) a dq v) ws ⊣⊢ wlatPointsto (GF := GF) a dq 0 v := .rfl

end PointsToLaws

end Weak
