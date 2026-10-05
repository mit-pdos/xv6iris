/-
Weak: THE VIEW INDEX AND THE `VProp` CORE (Rocq `iris/WeakView.v` @ xxvzwolszwmp (1cc222280); M2a).
The MonPred spike (`notes/weak-port-iris-gaps.md` G8): the first tree file over iris-lean's
`Iris.BI.MonPred` / `Iris.ProofMode.MonPred`.

Rocq header (verbatim, Rocq vocabulary):

    The surface layer of the design doc's Decision 5: the [biIndex] of views,
    [vProp := monPred view (iProp)], the seen-assertion [⊒V], the view-at
    modality [P @@ V], and THE SPLIT AXIOM

        [P ⊢ ∃ V, ⊒V ∗ P @@ V]        (VA-intro)
        [⊒V ∗ P @@ V ⊢ P]             (VA-elim)

    which is the soundness linchpin the whole weak-memory architecture turns
    on: an invariant may hold only OBJECTIVE assertions, and subjective
    content crosses a synchronisation edge by being frozen at a view
    ([P @@ V], objective) and thawed by the acquirer's [⊒V].

    DEPENDENCY DISCIPLINE.  This file is Sail-free and tree-free: stdpp plus
    [iris.bi.monpred] plus the proofmode.  [Z] appears only as the key type of
    the per-byte component (design doc, Decision 2: the weak-memory maps are
    keyed by [Z] = [uint] of the physical address, converted once at the
    [WeakInterp] seam), so nothing here can trip the [gmap Arch.pa _]
    Countable trap recorded in the durable notes.

    WHAT IS INHERITED FROM [iris/bi/monpred.v] AND WHAT IS ADDED.  Almost
    everything is inherited; this file adds only what the INDEX is about.

      inherited: the whole BI structure of [vProp] (incl. [BiAffine], [BiBUpd],
        [BiFUpd], [BiEmbed iProp], later-contractivity) via [monPredI]; [⊒V]'s
        persistence/absorbingness/anti-monotonicity ([monPred_in_persistent],
        [monPred_in_mono]); the [Objective] class and its instances for the
        embedding, pure, emp, ∧/∨/→/∗, -∗/∀/∃, □/<pers>/<affine>/<absorb>,
        [<obj>]/[<subj>], [|==>] and [|={E1,E2}=>]; and the proofmode support
        ([iris.proofmode.monpred]).
      added here: the [view] record, its floor/order/join lattice, the
        [biIndex] and [BiIndexBottom] instances, the [P @@ V] modality with
        its objectivity and monotonicity, and the split axiom.

    WHY [P @@ V] IS AN EMBEDDING OF [monPred_at] AND NOT [<obj>].  [<obj> P]
    is "P at EVERY index", which is far too strong to freeze a resource at one
    view.  The right object is the CONSTANT monPred at [P]'s value at [V] —
    [MonPred (λ _, P V) _] — which is literally [⎡ P V ⎤], i.e. the embedding
    [monPred_embed] applied to the projection [monPred_at].  So it is
    [Objective] by [embed_objective], with no new proof obligation, and every
    embedding lemma applies to it.  Iris does NOT provide this composition
    under a name; [view_at] below is it.

How the Rocq monPred vocabulary maps to iris-lean (the spike's finding, for the 41 MonPred files):

| Rocq | Lean |
|---|---|
| `biIndex`, `BiIndex car inh sqsubseteq preorder` | `Iris.BI.BiIndex` (`car`, `rel : LE car`, `[Std.IsPreorder car]`) |
| `BiIndexBottom bot` | `Iris.BI.BiIndexBottom I bot` (field `bot_le`) |
| `monPred I PROP`, `monPredI`, `monPredO` | `MonPred I PROP` (one type carries the OFE and the BI) |
| `monPred_at P i`, `P i` (coercion) | `P.monPred_at i` (no coercion) |
| `monPred_mono` | the structure field `P.monPred_mono : i ≤ j → P.monPred_at i ⊢ P.monPred_at j` |
| `monPred_in V` | `MonPred.monPred_in V` |
| `⎡P⎤` (`embed`) | `⎡P⎤` (`BiEmbed PROP (MonPred I PROP)`) |
| `Objective`, `objective_at` | `Objective`, `Objective.objective_at` |
| `<obj>` / `<subj>` | `<obj>` / `<subj>` (`MonPred.objectively` / `subjectively`) |
| `monPred_at_*` (sep/exist/embed/in/pure/bupd/…) | `MonPred.monPred_at_*`; all but `∀`/`∃` are `.rfl` (definitional) |
| `constructor => V` (unfold an entailment pointwise) | `MonPred.entails_at.mpr fun V => _`, or `istart (IProp GF)` then `iintro %V` |

Deviations from Rocq.
1. `view` is a `structure View` with fields `scl`, `map` (Rocq `v_scl`, `v_map`); the map is
   `GMapF Int Nat` (Rocq `gmap Z nat`), read through iris-lean `get?` with `Option.getD 0` for stdpp
   `default 0 (m !! a)`.
2. The order is an `LE View` instance written `≤` (Rocq `⊑`, `SqSubsetEq`), as iris-lean's
   `BiIndex.rel` is an `LE`; the join is `View.join`, written `⊔` (scoped notation in `Weak`), over
   iris-lean `merge` (Rocq `union_with (λ n1 n2, Some (max n1 n2))`).
3. `vPropO`/`vPropI` collapse into `VProp`: iris-lean's `MonPred I PROP` carries both the `OFE` and
   the `BI` instance (no canonical-structure split).
4. `⊒V` is a NOTATION for `MonPred.monPred_in V` (as in Rocq), so every iris-lean `monPred_in`
   instance and proofmode instance applies verbatim; `P @@ V` is notation for the definition
   `viewAt V P`, with an `iprop(…)` macro rule so it nests under the BI connectives.
5. `view_at_proper` / `view_at_mono'` / `view_at_flip_mono'` (setoid `Proper` instances) become the
   theorems `viewAt_proper` / `viewAt_mono'`; the flip form is the same statement and is not
   repeated (Lean has no setoid rewriting to feed).
6. ADDED (not in Rocq): `makeMonPredAt_viewAt`, a proofmode instance so that `istart` evaluates
   `(P @@ V).monPred_at i` to `P.monPred_at V` (Rocq gets the same effect from `monPred_at_embed`
   being a `MakeMonPredAt` instance on the unfolded `⎡·⎤`; in Lean `viewAt` is a `def`, which the
   instance search does not unfold).
7. Lemma statements `⊢ P V` (Rocq's `monPred_at` coercion) are `⊢ P.monPred_at V`.
8. `seen_persistent` / `seen_absorbing` and the ADDED `seen_timeless` re-state iris-lean's
   `monPred_in_*` instances at type `View` (not `viewBiIndex.car`).  They are NEEDED, not cosmetic
   (measured): under a binder, `Timeless (∃ t, ⊒(viewByte a t))` fails with only the upstream
   instance, because unifying `monPred_in (viewByte a t)` with `monPred_in (?i t)` (`?i : Nat →
   viewBiIndex.car`) fails at instance transparency; at `?i : Nat → View` it succeeds.

Name map (Rocq → Lean): `view`→`View`, `View`→`View.mk`, `v_scl`→`View.scl`, `v_map`→`View.map`,
`view_eq_dec`→derived `DecidableEq`, `flr`→`flr` (and `flr_scl`, `flr_lookup`, `flr_bot`,
`flr_scl_eq`, `flr_byte_eq`, `flr_byte_ne`, `flr_join` unchanged), `view_bot`→`viewBot`,
`view_scl`→`viewScl`, `view_byte`→`viewByte`, `view_sqsubseteq`→`instLEView`,
`view_sqsubseteq_spec`→`View.le_spec`, `view_preorder`→`instIsPreorderView`,
`view_inhabited`→`instInhabitedView`, `view_join_inst`→`View.join`, `view_join_l/r/lub/le/mono`→
`View.join_l/r/lub/le/mono`, `view_bot_le`→`viewBot_le`, `view_byte_le`→`viewByte_le`,
`view_byte_0`→`viewByte_0`, `view_scl_le`→`viewScl_le`, `view_bi_index`→`viewBiIndex`,
`view_bi_index_bot`→`viewBiIndexBot`, `vProp`/`vPropO`/`vPropI`→`VProp`, `view_at`→`viewAt`,
`seen_*`→`seen_*` (`seen_persistent`, `seen_absorbing`, new `seen_timeless`, `seen_at`, `seen_mono`, `seen_bot`,
`seen_bot_True`, `seen_join`, `seen_byte_0`, `seen_join_l/r`, `seen_at_self`), `view_at_*`→
`viewAt_*` (`unfold`, `at`, `ne`, `proper`, `mono'`, `objective`, `persistent`, `absorbing`, `affine`,
`timeless`, `view_mono`, `sep`, `and`, `or`, `exist`, `forall`, `pure`, `embed`, `bupd`,
`objective_id`, `intro`, `elim`, `split`, `intro_at`, `elim_at`), `objective_no_receipt`,
`objective_view_at_elim`→`objective_viewAt_elim`, `smoke_seen/split/roundtrip` unchanged.

Not ported: none (`view_at_flip_mono'`: deviation 5).

Statements checked: every lemma above, against `WeakView.v`.
-/
import MachCSL.StdppMap
import Iris.BI.MonPred
import Iris.ProofMode
import Iris.ProofMode.MonPred
import Iris.Instances.IProp

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL

/-! ## 1. The view index

DECIDED at M1 (design doc, Decision 5): a view is a SCALAR floor joined with a SPARSE per-byte map.
Why the pair: a hart's semantic read floor for byte `a` is `w_vrNew ⊔ coh(a)` — a scalar joined with
a finite map, which a bare map cannot represent (its support would be infinite) and a bare scalar
cannot either (a points-to needs a per-byte floor).  A points-to carries a singleton-map view; a
release deposits a pure SCALAR view, because a timestamp below the log's length bounds every
component of the releaser's floor.

The order is POINTWISE ON THE FLOOR, hence a PREORDER and not a partial order — `View.mk 1 ∅` and
`View.mk 1 {[a := 0]}` are equivalent but not equal.  We deliberately do NOT quotient: `MonPred`
only ever needs a preorder (`BiIndex` asks for exactly that). -/

/-- A view: a scalar floor and a sparse per-byte floor map (Rocq `view`). -/
structure View where
  scl : Nat
  map : GMapF Int Nat
  deriving DecidableEq

/-- The FLOOR of view `V` at byte `a`: the scalar, joined with whatever the sparse map says about
`a` (nothing = 0). -/
def flr (V : View) (a : Int) : Nat := max V.scl ((get? V.map a).getD 0)

theorem flr_scl (V : View) (a : Int) : V.scl ≤ flr V a := by unfold flr; omega

theorem flr_lookup (V : View) (a : Int) (n : Nat) (h : get? V.map a = some n) : n ≤ flr V a := by
  unfold flr; rw [h]; simp only [Option.getD_some]; omega

/-- The three views this development actually builds. -/
def viewBot : View := ⟨0, ∅⟩
def viewScl (n : Nat) : View := ⟨n, ∅⟩
def viewByte (a : Int) (t : Nat) : View := ⟨0, {[a := t]}⟩

theorem flr_bot (a : Int) : flr viewBot a = 0 := by
  simp [flr, viewBot, lookupEmpty]

theorem flr_scl_eq (n : Nat) (a : Int) : flr (viewScl n) a = n := by
  simp [flr, viewScl, lookupEmpty]

theorem flr_byte_eq (a : Int) (t : Nat) : flr (viewByte a t) a = t := by
  simp [flr, viewByte, lookupSingleton]

theorem flr_byte_ne (a : Int) (t : Nat) (a' : Int) (h : a' ≠ a) : flr (viewByte a t) a' = 0 := by
  simp [flr, viewByte, lookupSingletonNe (Ne.symm h)]

/-! ### The lattice -/

instance instLEView : LE View := ⟨fun V1 V2 => ∀ a, flr V1 a ≤ flr V2 a⟩

theorem View.le_spec (V1 V2 : View) : V1 ≤ V2 ↔ ∀ a, flr V1 a ≤ flr V2 a := Iff.rfl

instance instIsPreorderView : Std.IsPreorder View where
  le_refl _ _ := Nat.le_refl _
  le_trans _ _ _ h12 h23 a := Nat.le_trans (h12 a) (h23 a)

instance instInhabitedView : Inhabited View := ⟨viewBot⟩

/-- The join (Rocq `view_join_inst`): max of the scalars, pointwise max of the maps. -/
def View.join (V1 V2 : View) : View :=
  ⟨max V1.scl V2.scl, merge (fun _ n1 n2 => max n1 n2) V1.map V2.map⟩

@[inherit_doc] scoped infixl:65 " ⊔ " => View.join

/-- THE JOIN LEMMA: the floor of a join is the max of the floors, pointwise.  Everything else about
the lattice follows from it. -/
theorem flr_join (V1 V2 : View) (a : Int) : flr (V1 ⊔ V2) a = max (flr V1 a) (flr V2 a) := by
  simp only [flr, View.join, lookupUnionWith]
  cases get? V1.map a <;> cases get? V2.map a <;> simp [Option.merge] <;> omega

theorem View.join_l (V1 V2 : View) : V1 ≤ V1 ⊔ V2 := fun a => by rw [flr_join]; omega
theorem View.join_r (V1 V2 : View) : V2 ≤ V1 ⊔ V2 := fun a => by rw [flr_join]; omega

theorem View.join_lub (V1 V2 V : View) (h1 : V1 ≤ V) (h2 : V2 ≤ V) : V1 ⊔ V2 ≤ V := fun a => by
  rw [flr_join]; have := h1 a; have := h2 a; omega

/-- ... hence the join IS the least upper bound, in one iff — the form the
`⊒V1 ∗ ⊒V2 ⊣⊢ ⊒(V1 ⊔ V2)` law consumes. -/
theorem View.join_le (V1 V2 V : View) : V1 ⊔ V2 ≤ V ↔ V1 ≤ V ∧ V2 ≤ V :=
  ⟨fun h => ⟨fun a => Nat.le_trans (View.join_l V1 V2 a) (h a),
             fun a => Nat.le_trans (View.join_r V1 V2 a) (h a)⟩,
   fun ⟨h1, h2⟩ => View.join_lub V1 V2 V h1 h2⟩

theorem View.join_mono {V1 V1' V2 V2' : View} (h1 : V1 ≤ V1') (h2 : V2 ≤ V2') :
    V1 ⊔ V2 ≤ V1' ⊔ V2' := fun a => by
  rw [flr_join, flr_join]; have := h1 a; have := h2 a; omega

theorem viewBot_le (V : View) : viewBot ≤ V := fun a => by rw [flr_bot]; omega

/-- A singleton-byte view is below `V` exactly when `V`'s floor covers the timestamp — the form
every points-to law is stated in. -/
theorem viewByte_le (a : Int) (t : Nat) (V : View) : viewByte a t ≤ V ↔ t ≤ flr V a := by
  constructor
  · intro h; have := h a; rwa [flr_byte_eq] at this
  · intro ht a'
    by_cases hne : a' = a
    · subst hne; rw [flr_byte_eq]; exact ht
    · rw [flr_byte_ne a t a' hne]; omega

/-- A byte view AT TIMESTAMP 0 is the bottom view: the era-initial image is visible to every agent,
whatever it has observed.  This is what makes an era-image points-to receipt-free, hence OBJECTIVE
(see `WeakVProp`'s `wptImg`). -/
theorem viewByte_0 (a : Int) : viewByte a 0 ≤ viewBot := fun a' => by
  rw [flr_bot]
  by_cases hne : a' = a
  · subst hne; rw [flr_byte_eq]; exact Nat.le_refl 0
  · rw [flr_byte_ne a 0 a' hne]; exact Nat.le_refl 0

/-- A scalar view is below `V` exactly when `V`'s SCALAR covers it: the scalar floor must be
dominated at every byte, including the ones `V`'s map says nothing about. -/
theorem viewScl_le (n : Nat) (V : View) : viewScl n ≤ V ↔ ∀ a, n ≤ flr V a := by
  constructor
  · intro h a; have := h a; rwa [flr_scl_eq] at this
  · intro h a; rw [flr_scl_eq]; exact h a

/-! ### The `BiIndex` -/

/-- The view index (Rocq `view_bi_index`, a canonical structure there). -/
abbrev viewBiIndex : BiIndex where
  car := View
  rel := instLEView

instance viewBiIndexBot : BiIndexBottom viewBiIndex viewBot where
  bot_le V := viewBot_le V

/-! ## 2. `VProp` -/

/-- Monotone predicates over views (Rocq `vProp`, `vPropO`, `vPropI`; deviation 3). -/
abbrev VProp (GF : BundledGFunctors) : Type _ := MonPred viewBiIndex (IProp GF)

/-- `⊒V` — "I have observed `V`".  This is iris-lean's own `monPred_in`, reused rather than
hand-rolled: persistence, absorbingness and anti-monotonicity all come for free, and so does the
proofmode's handling of it. -/
notation:max "⊒" V:max => MonPred.monPred_in (I := viewBiIndex) V

/-- `P @@ V` — "P holds at view `V`", frozen: an OBJECTIVE assertion (see the header for why this,
and not `<obj>`). -/
def viewAt {GF : BundledGFunctors} (V : View) (P : VProp GF) : VProp GF :=
  iprop(⎡P.monPred_at V⎤)

@[inherit_doc viewAt] notation:40 P:41 " @@ " V:41 => viewAt V P
macro_rules | `(iprop($P @@ $V)) => ``(viewAt $V iprop($P))

section ViewLaws
variable {GF : BundledGFunctors}

/-! ### 2a. the seen assertion -/

instance seen_persistent (V : View) : Persistent (⊒V : VProp GF) :=
  monPred_in_persistent (I := viewBiIndex) V
instance seen_absorbing (V : View) : Absorbing (⊒V : VProp GF) :=
  monPred_in_absorbing (I := viewBiIndex) V
/-- ADDED (deviation 8): iris-lean's `monPred_in_timeless`, re-stated at `View`. -/
instance seen_timeless (V : View) : Timeless (⊒V : VProp GF) :=
  monPred_in_timeless (I := viewBiIndex) V

theorem seen_at (V V' : View) : (⊒V : VProp GF).monPred_at V' ⊣⊢ ⌜V ≤ V'⌝ :=
  monPred_at_in (I := viewBiIndex) V' V

/-- ANTI-MONOTONE: seeing more implies seeing less. -/
theorem seen_mono {V1 V2 : View} (h : V1 ≤ V2) : (⊒V2 : VProp GF) ⊢ ⊒V1 := monPred_in_mono h

/-- The bottom view is free. -/
theorem seen_bot : ⊢ (⊒viewBot : VProp GF) :=
  entails_at.mpr fun V => pure_intro (viewBot_le V)

theorem seen_bot_True : (⊒viewBot : VProp GF) ⊣⊢ True := by
  constructor
  · iintro _; ipureintro; trivial
  · iintro _; iapply seen_bot

/-- JOIN: two observations are one observation of the join.  This is exactly `View.join_le`,
transported. -/
theorem seen_join (V1 V2 : View) : (iprop(⊒V1 ∗ ⊒V2) : VProp GF) ⊣⊢ ⊒(V1 ⊔ V2) := by
  istart (IProp GF)
  iintro %V
  isplit
  · iintro ⟨%h1, %h2⟩; ipureintro; exact View.join_lub V1 V2 V h1 h2
  · iintro %h
    have ⟨h1, h2⟩ := (View.join_le V1 V2 V).mp h
    isplit <;> ipureintro <;> assumption

/-- The era-image receipt is free. -/
theorem seen_byte_0 (a : Int) : ⊢ (⊒(viewByte a 0) : VProp GF) :=
  seen_bot.trans (seen_mono (viewByte_0 a))

theorem seen_join_l (V1 V2 : View) : (⊒(V1 ⊔ V2) : VProp GF) ⊢ ⊒V1 := seen_mono (View.join_l V1 V2)
theorem seen_join_r (V1 V2 : View) : (⊒(V1 ⊔ V2) : VProp GF) ⊢ ⊒V2 := seen_mono (View.join_r V1 V2)

/-- The index is REFLEXIVE, so at index `V` the assertion `⊒V` is free.  This is what lets a leaf
rule at the hart's index produce its own seen-assertion out of nothing. -/
theorem seen_at_self (V : View) : ⊢ (⊒V : VProp GF).monPred_at V :=
  pure_intro (Std.IsPreorder.le_refl V)

/-! ### 2b. the view-at modality -/

theorem viewAt_unfold (V : View) (P : VProp GF) : iprop(P @@ V) = iprop(⎡P.monPred_at V⎤) := rfl

theorem viewAt_at (V V' : View) (P : VProp GF) : (P @@ V).monPred_at V' ⊣⊢ P.monPred_at V := .rfl

set_option synthInstance.checkSynthOrder false in
/-- ADDED (deviation 6): the proofmode evaluates `(P @@ V)` at any index to `P` at `V`. -/
instance makeMonPredAt_viewAt (d : MakeMonPredAt.Kind) (i V : View) (P : VProp GF) :
    MakeMonPredAt d i (P @@ V) (P.monPred_at V) where
  make_monPred_at := .rfl

instance viewAt_ne (V : View) : OFE.NonExpansive (viewAt (GF := GF) V) :=
  ⟨fun _ _ _ h => dist_at.mpr fun _ => dist_at.mp h V⟩

theorem viewAt_proper (V : View) {P Q : VProp GF} (h : P ⊣⊢ Q) : P @@ V ⊣⊢ Q @@ V :=
  ⟨entails_at.mpr fun _ => entails_at.mp h.mp V, entails_at.mpr fun _ => entails_at.mp h.mpr V⟩

theorem viewAt_mono' (V : View) {P Q : VProp GF} (h : P ⊢ Q) : P @@ V ⊢ Q @@ V :=
  entails_at.mpr fun _ => entails_at.mp h V

/-- OBJECTIVE BY CONSTRUCTION — the whole point of the modality. -/
instance viewAt_objective (V : View) (P : VProp GF) : Objective (P @@ V) :=
  embed_objective _

instance viewAt_persistent (V : View) (P : VProp GF) [Persistent P] : Persistent (P @@ V) :=
  embed_persistent _
instance viewAt_absorbing (V : View) (P : VProp GF) [Absorbing P] : Absorbing (P @@ V) :=
  embed_absorbing _
instance viewAt_affine (V : View) (P : VProp GF) [Affine P] : Affine (P @@ V) :=
  embed_affine _
instance viewAt_timeless (V : View) (P : VProp GF) [Timeless P] : Timeless (P @@ V) :=
  embed_timeless _

/-- MONOTONE in the view — every `VProp` is monotone, by construction. -/
theorem viewAt_view_mono {V1 V2 : View} (P : VProp GF) (h : V1 ≤ V2) : P @@ V1 ⊢ P @@ V2 :=
  entails_at.mpr fun _ => P.monPred_mono h

/-- The structural laws.  `∗` and `∃` commute with `@@` because `monPred_at` and `⎡·⎤` both do. -/
theorem viewAt_sep (V : View) (P Q : VProp GF) : iprop((P ∗ Q) @@ V) ⊣⊢ (P @@ V) ∗ (Q @@ V) := .rfl
theorem viewAt_and (V : View) (P Q : VProp GF) : iprop((P ∧ Q) @@ V) ⊣⊢ (P @@ V) ∧ (Q @@ V) := .rfl
theorem viewAt_or (V : View) (P Q : VProp GF) : iprop((P ∨ Q) @@ V) ⊣⊢ (P @@ V) ∨ (Q @@ V) := .rfl
theorem viewAt_exist {A : Type _} (V : View) (Φ : A → VProp GF) :
    iprop((∃ x, Φ x) @@ V) ⊣⊢ ∃ x, (Φ x) @@ V :=
  (embed_congr (monPred_at_exist V Φ)).trans (embed_exist _)
theorem viewAt_forall {A : Type _} (V : View) (Φ : A → VProp GF) :
    iprop((∀ x, Φ x) @@ V) ⊣⊢ ∀ x, (Φ x) @@ V :=
  (embed_congr (monPred_at_forall V Φ)).trans (embed_forall _)
theorem viewAt_pure (V : View) (φ : Prop) : iprop((⌜φ⌝ : VProp GF) @@ V) ⊣⊢ ⌜φ⌝ := embed_pure φ
theorem viewAt_embed (V : View) (P : IProp GF) : iprop((⎡P⎤ : VProp GF) @@ V) ⊣⊢ ⎡P⎤ := .rfl
theorem viewAt_bupd (V : View) (P : VProp GF) : iprop((|==> P) @@ V) ⊣⊢ |==> (P @@ V) := .rfl

/-- An OBJECTIVE assertion is its own view-at, at every view: freezing it is the identity.  This is
what makes the whole "registers / devices / ghost state / pure facts / `↦□` ride along unchanged"
claim of the design doc a one-line corollary at every such assertion. -/
theorem viewAt_objective_id (V : View) (P : VProp GF) [Objective P] : P @@ V ⊣⊢ P :=
  ⟨entails_at.mpr fun V' => Objective.objective_at V V',
   entails_at.mpr fun V' => Objective.objective_at V' V⟩

/-! ### 2c. THE SPLIT AXIOM

The soundness linchpin.  Read together: any assertion is an objective payload plus a receipt for the
view it was taken at, and the receipt is what a synchronisation edge transports.

Both directions are iris-lean's `monPred_in_intro` / `monPred_in_elim` with the ∧ turned into a ∗ —
legitimate because `⊒V` is persistent and `VProp` is affine (both inherited). -/

theorem viewAt_intro (P : VProp GF) : P ⊢ ∃ V, ⊒V ∗ P @@ V := by
  istart (IProp GF)
  iintro %V HP
  iexists V
  isplitr
  · ipureintro; exact Std.IsPreorder.le_refl V
  · iexact HP

/-- VA-ELIM is where the MONOTONICITY of every `VProp` is spent: the receipt `⊒V` says the ambient
index is above `V`, and `P`'s own `monPred_mono` carries `P`'s value at `V` up to it. -/
theorem viewAt_elim (V : View) (P : VProp GF) : iprop(⊒V ∗ P @@ V) ⊢ P := by
  istart (IProp GF)
  iintro %V' ⟨%hV, HP⟩
  iapply (P.monPred_mono hV)
  iexact HP

theorem viewAt_split (P : VProp GF) : P ⊣⊢ ∃ V, ⊒V ∗ P @@ V :=
  ⟨viewAt_intro P, exists_elim fun V => viewAt_elim V P⟩

/-- The two forms a leaf rule uses directly. -/
theorem viewAt_intro_at (V : View) (P : VProp GF) :
    P.monPred_at V ⊢ (iprop(⊒V ∗ P @@ V) : VProp GF).monPred_at V := by
  iintro H
  isplitr
  · ipureintro; exact Std.IsPreorder.le_refl V
  · iexact H

theorem viewAt_elim_at {V V' : View} (P : VProp GF) (h : V ≤ V') :
    P.monPred_at V ⊢ P.monPred_at V' := P.monPred_mono h

end ViewLaws

/-! ## 3. Objectivity: what is inherited, what this file adds

INHERITED from `Iris.BI.MonPred` and covering, wholesale, everything the design doc lists as
"objective by construction": `embed_objective` (⎡P⎤ for ANY `IProp` P — every register/CSR
assertion, every device-fabric assertion, all ghost state and every base-layer resource),
`pure_objective`, `emp_objective`, `and_/or_/impl_/sep_/wand_/forall_/exists_objective`,
`persistently_/affinely_/absorbingly_/intuitionistically_objective`,
`objectively_/subjectively_objective`, `later_objective`, `bupd_objective`, `fupd_objective`, and
the big-op instances `big_sepL_objective` / `big_sepM_objective` / `big_sepS_objective`.

ADDED here: `viewAt_objective` (§2b) — and nothing else is needed. -/

section ObjectiveDerived
variable {GF : BundledGFunctors}

/-- An objective assertion needs no receipt: the split axiom degenerates. -/
theorem objective_no_receipt (P : VProp GF) [Objective P] (V : View) : P ⊣⊢ P @@ V :=
  (viewAt_objective_id V P).symm

/-- ... hence VA-elim needs no `⊒V` at an objective assertion. -/
theorem objective_viewAt_elim (P : VProp GF) [Objective P] (V : View) : P @@ V ⊢ P :=
  (viewAt_objective_id V P).mp

end ObjectiveDerived

/-! ## 4. Proofmode smoke test

Kept in the file deliberately: it is the check that the `MonPred` proofmode instances FIRE through
`⊒`, `@@` and `⎡·⎤` — `iintro`, `isplit`, `imodintro`, `icases`-of-an-existential, `iframe`, and a
`Persistent` hypothesis all at once.  If a future change to the index or to the modality breaks the
instance resolution, this fails here rather than deep inside a leaf proof.  These run at the
`VProp` altitude, WITHOUT `istart`. -/

section Smoke
variable {GF : BundledGFunctors}

example (V1 V2 : View) (R : IProp GF) (P : VProp GF) :
    iprop(⊒V1 ∗ ⊒V2 ∗ ⎡R⎤ ∗ P @@ V1) ⊢
      |==> (⊒(V1 ⊔ V2) ∗ ⎡R⎤ ∗ <obj> (P @@ V1) ∗ ⊒V1) := by
  iintro ⟨#H1, #H2, HR, HP⟩
  imodintro
  isplitr
  · iapply (seen_join V1 V2).mp
    isplitl []
    · iexact H1
    · iexact H2
  iframe HR H1
  iapply objective_objectively
  iexact HP

example (P : VProp GF) : P ⊢ ∃ V, ⊒V ∗ (P @@ V ∗ ⌜True⌝) := by
  iintro HP
  icases viewAt_intro P $$ HP with ⟨%V, #HV, HPV⟩
  iexists V
  iframe HV HPV

example (P : VProp GF) : (∃ V, ⊒V ∗ P @@ V) ⊢ P := by
  iintro ⟨%V, #HV, HP⟩
  iapply viewAt_elim V
  iframe HV HP

example (P : VProp GF) : P ⊢ |==> P := by
  iintro H
  imodintro
  iexact H

end Smoke

end Weak
