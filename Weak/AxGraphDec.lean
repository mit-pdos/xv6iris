/-
Weak: **a COMPUTABLE checker for the cat model on concrete graphs** (AxSL tier).

Rocq: `iris/AxGraphDec.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
gate G0.5, witness graphs "with proved verdicts").  PURE (no Iris).

THE POINT.  Every axiom of `AxGraphCat.rvwmoCatConsistent` quantifies over
events, bytes and values, but on a `Gdexec` all of them are BOUNDED: the events
are the positions of the rows (`gevents`), an event's bytes are read off its
label (`WeakRvwmoDec.gwrBytes` / `grdBytes`), and `gmoLt`, `gwix`, `gwriteAt`
are list functions.  So the whole model is one boolean `catConsistentB`, proved
SOUND (`catConsistentBSound`) — a witness's verdict is then a closed `decide`
(`decide +kernel` for the big ones), and the failing verdicts for RVWMO⁻ are one
`gpoloc` edge plus one gmo comparison (`notMinusOfPoloc`).

Why not `WeakRvwmoDec`'s `Decidable` instances: in Rocq they are `Qed`-opaque.
(In Lean they are transparent, but this file keeps Rocq's transparent-`Bool`
route so that the verdicts and the `↔` specs downstream files cite exist under
their Rocq names.)  Only the BYTE ENUMERATIONS and the three `Alt`
reformulations of `WeakRvwmoDec` are reused.

Relations get `↔` specs (needed to ENUMERATE `gobCat`'s edges for the deferral
witness); the whole-model checks get soundness only.

FETCHES (owner decision D1): this tier keeps the Rocq treatment — a fetch is a
graph `LLoad` read like any other; nothing in this file distinguishes it.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (`_b` ↦ `B`,
   `_spec` ↦ `Spec`, `_sound` ↦ `Sound`).  None of this file's names is in
   `notes/weak-port-dupnames.json`; the dependencies' duplicates are referred
   to qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `AxGraphCat` deviation 2 (`forallb`/`existsb` ↦
   `List.all`/`List.any`, `bool_decide` ↦ `decide`, `implb a b` ↦ `!a || b`,
   `is_Some o` ↦ `o.isSome = true`, `seq` ↦ `List.range'`, `imap` ↦
   `List.mapIdx`, `mjoin` ↦ `List.flatten`), plus `Nat.ltb`/`Nat.leb`/`Nat.eqb`
   ↦ `decide (· < ·)`/`decide (· ≤ ·)`/`decide (· = ·)` and `bv_unsigned` ↦
   `BitVec.toNat`.  The read-byte triple keeps Rocq's LEFT-nested product
   `(Int × Nat) × BitVec 8` (`WeakRvwmoDec` deviation 2).
3. `forallb_forall_true` / `existsb_exists_true` are stated over `List.all` /
   `List.any` (they coincide with `AxGraphCat.forallbAll` / `existsbSome`;
   kept under their own names for faithfulness).
4. A closing `example` (`lbgd`, the LB witness, passes `catConsistentB` by
   `decide +kernel`) checks that the checker COMPUTES; it is not a declaration
   and has no Rocq twin.

**Name map** (Rocq → Lean): `forallb_forall_true` ↦ `forallbForallTrue`;
`existsb_exists_true` ↦ `existsbExistsTrue`; `is_some_b` ↦ `isSomeB`;
`is_some_b_spec` ↦ `isSomeBSpec`; `bv_eqb` ↦ `bvEqb`; `bv_eqb_spec` ↦
`bvEqbSpec`; `gevents`; `gevents_spec` ↦ `geventsSpec`; `gevents_of_lbl` ↦
`geventsOfLbl`; `glbl_b` ↦ `glblB`; `glbl_b_spec` ↦ `glblBSpec`; `gpo_b` ↦
`gpoB`; `gpo_b_spec` ↦ `gpoBSpec`; `gmo_lt_b` ↦ `gmoLtB`; `gmo_lt_b_spec` ↦
`gmoLtBSpec`; `gvis_b` ↦ `gvisB`; `gvis_b_spec` ↦ `gvisBSpec`; `gwb_b` ↦
`gwbB`; `gwb_b_spec` ↦ `gwbBSpec`; `gwa_b` ↦ `gwaB`; `gwa_b_spec` ↦
`gwaBSpec`; `grb_b` ↦ `grbB`; `grb_b_spec` ↦ `grbBSpec`; `grf_at_b` ↦
`grfAtB`; `grf_at_b_spec` ↦ `grfAtBSpec`; `gacc_b` ↦ `gaccB`; `gacc_b_spec` ↦
`gaccBSpec`; `gwrites_byte_gevents` ↦ `gwritesByteGevents`;
`greads_byte_gevents` ↦ `greadsByteGevents`; `gpo_gevents` ↦ `gpoGevents`;
`gppo1_b` ↦ `gppo1B`; `gppo1_b_spec` ↦ `gppo1BSpec`; `gnoint_b` ↦ `gnointB`;
`gnoint_b_spec` ↦ `gnointBSpec`; `gppo2_b` ↦ `gppo2B`; `gppo2_b_spec` ↦
`gppo2BSpec`; `gppo3_b` ↦ `gppo3B`; `gppo3_b_spec` ↦ `gppo3BSpec`; `gfcov_b` ↦
`gfcovB`; `gfcov_b_spec` ↦ `gfcovBSpec`; `gfence_b` ↦ `gfenceB`;
`gfence_b_spec` ↦ `gfenceBSpec`; `gacq_b` ↦ `gacqB`; `gacq_b_spec` ↦
`gacqBSpec`; `grcsc_b` ↦ `grcscB`; `grcsc_b_spec` ↦ `grcscBSpec`;
`gppo_cat6_b` ↦ `gppoCat6B`; `gppo_cat6_b_spec` ↦ `gppoCat6BSpec`;
`gpoloc_b` ↦ `gpolocB`; `gpoloc_b_spec` ↦ `gpolocBSpec`; `not_minus_of_poloc`
↦ `notMinusOfPoloc`; `grf_b` ↦ `grfB`; `grf_b_spec` ↦ `grfBSpec`; `gppo12_b`
↦ `gppo12B`; `gppo12_b_spec` ↦ `gppo12BSpec`; `gppo_cat_b` ↦ `gppoCatB`;
`gppo_cat_b_spec` ↦ `gppoCatBSpec`; `not_cat_of_rule12` ↦ `notCatOfRule12`;
`grfe_b` ↦ `grfeB`; `grfe_b_spec` ↦ `grfeBSpec`; `gco_b` ↦ `gcoB`;
`gco_b_spec` ↦ `gcoBSpec`; `gfr_b` ↦ `gfrB`; `gfr_b_spec` ↦ `gfrBSpec`;
`gobr_cat_b` ↦ `gobrCatB`; `gobr_cat_b_spec` ↦ `gobrCatBSpec`;
`gobr_cat_gevents` ↦ `gobrCatGevents`; `gshape_b` ↦ `gshapeB`;
`gshape_b_spec` ↦ `gshapeBSpec`; `gwf_b` ↦ `gwfB`; `gwf_b_sound` ↦
`gwfBSound`; `ppo_gmo_b` ↦ `ppoGmoB`; `ppo_gmo_b_sound` ↦ `ppoGmoBSound`;
`gppo_cat6_gmo_b_sound` ↦ `gppoCat6GmoBSound`; `gppo_cat_gmo_b_sound` ↦
`gppoCatGmoBSound`; `gimg_b` ↦ `gimgB`; `gimg_b_spec` ↦ `gimgBSpec`;
`glv_src_b` ↦ `glvSrcB`; `glv_max_b` ↦ `glvMaxB`; `gload_value_b` ↦
`gloadValueB`; `gload_value_b_sound` ↦ `gloadValueBSound`; `gatom_b` ↦
`gatomB`; `gatom_b_sound` ↦ `gatomBSound`; `gdeps_wf_b` ↦ `gdepsWfB`;
`gdeps_wf_b_sound` ↦ `gdepsWfBSound`; `gdeps_gmo_b` ↦ `gdepsGmoB`;
`gdeps_gmo_b_sound` ↦ `gdepsGmoBSound`; `axioms_b` ↦ `axiomsB`;
`cat_consistent_b` ↦ `catConsistentB`; `cat6_consistent_b` ↦
`cat6ConsistentB`; `axioms_b_sound` ↦ `axiomsBSound`;
`cat_consistent_b_sound` ↦ `catConsistentBSound`; `cat6_consistent_b_sound` ↦
`cat6ConsistentBSound`.

**Not ported:** nothing (the §7 `Print Assumptions` block has no Lean twin; the
lint's axiom check covers it).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `gshapeB`'s / `gshapeBSpec`'s `LIo` arms are `true`/`True` (`gwf`'s flip).
-/
import Weak.WeakRvwmoDec
import Weak.AxGraph
import Weak.AxGraphCat

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The boolean kit -/

theorem forallbForallTrue {A : Type _} (f : A → Bool) (l : List A) :
    l.all f = true ↔ ∀ x, x ∈ l → f x = true := by
  simp

theorem existsbExistsTrue {A : Type _} (f : A → Bool) (l : List A) :
    l.any f = true ↔ ∃ x, x ∈ l ∧ f x = true := by
  simp

def isSomeB {A : Type _} (o : Option A) : Bool :=
  match o with
  | some _ => true
  | none => false

theorem isSomeBSpec {A : Type _} (o : Option A) : isSomeB o = true ↔ o.isSome = true := by
  cases o <;> simp [isSomeB]

/-- Byte values compared through `BitVec.toNat`. -/
def bvEqb (x y : BitVec 8) : Bool := decide (x.toNat = y.toNat)

theorem bvEqbSpec (x y : BitVec 8) : bvEqb x y = true ↔ x = y := by
  unfold bvEqb
  rw [decide_eq_true_iff]
  exact BitVec.toNat_inj

/-! # 2. The events of a graph -/

def gevents (G : Gexec) : List Geid :=
  (G.gxProg.mapIdx (fun i p => (List.range' 0 p.length).map (fun k => (i, k)))).flatten

theorem geventsSpec (G : Gexec) (e : Geid) : e ∈ gevents G ↔ (gxLbl G e).isSome = true := by
  obtain ⟨i, k⟩ := e
  unfold gevents gxLbl
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hel⟩
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hl
    rw [List.getElem?_mapIdx] at hn
    cases hp : G.gxProg[n]? with
    | none => rw [hp] at hn; cases hn
    | some p =>
      rw [hp, Option.map_some, Option.some.injEq] at hn
      subst hn
      obtain ⟨k', hk', hx⟩ := List.mem_map.1 hel
      rw [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hk := (elem_of_seq.1 hk').2
      show ((G.gxProg[n]?).bind (fun p => p[k']?)).isSome = true
      rw [hp]
      show (p[k']?).isSome = true
      exact lookup_lt_is_Some.2 (by omega)
  · intro h
    cases hp : G.gxProg[i]? with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      have h' : (p[k]?).isSome = true := h
      refine ⟨(List.range' 0 p.length).map (fun k => (i, k)), ?_, ?_⟩
      · exact List.mem_iff_getElem?.2 ⟨i, by rw [List.getElem?_mapIdx, hp]; rfl⟩
      · exact List.mem_map.2 ⟨k, elem_of_seq.2 ⟨Nat.zero_le _, by
          have := lookup_lt_is_Some.1 h'; omega⟩, rfl⟩

theorem geventsOfLbl (G : Gexec) (e : Geid) (l : Lbl) : gxLbl G e = some l → e ∈ gevents G := by
  intro hl
  rw [geventsSpec, hl]
  rfl

/-! # 3. The elementary relations -/

def glblB (G : Gexec) (e : Geid) (P : Lbl → Bool) : Bool :=
  match gxLbl G e with
  | some l => P l
  | none => false

theorem glblBSpec (G : Gexec) (e : Geid) (P : Lbl → Bool) : glblB G e P = true ↔ glblIs G e P := by
  unfold glblB glblIs
  cases gxLbl G e with
  | some l => simp
  | none => simp

def gpoB (G : Gexec) (e1 e2 : Geid) : Bool :=
  decide (e1.1 = e2.1) && decide (e1.2 < e2.2) &&
  isSomeB (gxLbl G e1) && isSomeB (gxLbl G e2)

theorem gpoBSpec (G : Gexec) (e1 e2 : Geid) : gpoB G e1 e2 = true ↔ WeakRvwmoGraph.gpo G e1 e2 := by
  simp only [gpoB, WeakRvwmoGraph.gpo, Bool.and_eq_true, decide_eq_true_iff, isSomeBSpec,
    and_assoc]

def gmoLtB (G : Gexec) (e1 e2 : Geid) : Bool :=
  decide (e1 ∈ G.gxGmo) && decide (e2 ∈ G.gxGmo) && decide (gpos G e1 < gpos G e2)

theorem gmoLtBSpec (G : Gexec) (e1 e2 : Geid) : gmoLtB G e1 e2 = true ↔ gmoLt G e1 e2 := by
  simp only [gmoLtB, gmoLt, Bool.and_eq_true, decide_eq_true_iff, and_assoc]

def gvisB (G : Gexec) (w r : Geid) : Bool := gmoLtB G w r || gpoB G w r

theorem gvisBSpec (G : Gexec) (w r : Geid) : gvisB G w r = true ↔ gvisible G w r := by
  rw [gvisB, Bool.or_eq_true, gmoLtBSpec, gpoBSpec]
  rfl

/-- `gwritesByte` at a byte AND value; at a byte (some value). -/
def gwbB (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) : Bool :=
  (gwrBytes G w).any (fun x : Int × BitVec 8 => decide (x.1 = a) && bvEqb x.2 v)

theorem gwbBSpec (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) :
    gwbB G w a v = true ↔ gwritesByte G w a v := by
  rw [gwritesByteBytes, gwbB, existsbExistsTrue]
  constructor
  · rintro ⟨⟨a', v'⟩, hx, h⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, bvEqbSpec] at h
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    subst h1 h2
    exact hx
  · intro h
    refine ⟨(a, v), h, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, bvEqbSpec]
    exact ⟨rfl, rfl⟩

def gwaB (G : Gexec) (w : Geid) (a : Int) : Bool :=
  (gwrBytes G w).any (fun x : Int × BitVec 8 => decide (x.1 = a))

theorem gwaBSpec (G : Gexec) (w : Geid) (a : Int) : gwaB G w a = true ↔ ∃ v, gwritesByte G w a v := by
  rw [gwaB, existsbExistsTrue]
  constructor
  · rintro ⟨⟨a', v⟩, hx, h⟩
    rw [decide_eq_true_iff] at h
    dsimp only at h
    subst h
    exact ⟨v, (gwritesByteBytes G w a' v).2 hx⟩
  · rintro ⟨v, h⟩
    exact ⟨(a, v), (gwritesByteBytes G w a v).1 h, decide_eq_true rfl⟩

/-- `greadsByte` at a byte, timestamp and value. -/
def grbB (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) : Bool :=
  (grdBytes G r).any (fun x : (Int × Nat) × BitVec 8 =>
    decide (x.1.1 = a) && decide (x.1.2 = t) && bvEqb x.2 v)

theorem grbBSpec (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    grbB G r a t v = true ↔ greadsByte G r a t v := by
  rw [greadsByteBytes, grbB, existsbExistsTrue]
  constructor
  · rintro ⟨⟨⟨a', t'⟩, v'⟩, hx, h⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      bvEqbSpec] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    exact hx
  · intro h
    refine ⟨((a, t), v), h, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, bvEqbSpec]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- `grfAt`: the rf-source at a byte. -/
def grfAtB (G : Gexec) (a : Int) (w r : Geid) : Bool :=
  (grdBytes G r).any (fun x : (Int × Nat) × BitVec 8 =>
    decide (x.1.1 = a) && decide (gwriteAt G x.1.2 = some w))

theorem grfAtBSpec (G : Gexec) (a : Int) (w r : Geid) : grfAtB G a w r = true ↔ grfAt G a w r := by
  rw [grfAtB, existsbExistsTrue]
  unfold grfAt
  constructor
  · rintro ⟨⟨⟨a', t⟩, v⟩, hx, h⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    subst h1
    exact ⟨t, v, (greadsByteBytes G r a' t v).2 hx, h2⟩
  · rintro ⟨t, v, hrd, hat⟩
    refine ⟨((a, t), v), (greadsByteBytes G r a t v).1 hrd, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨rfl, hat⟩

def gaccB (G : Gexec) (e : Geid) (a : Int) : Bool := decide (a ∈ gaccAddrs G e)

theorem gaccBSpec (G : Gexec) (e : Geid) (a : Int) : gaccB G e a = true ↔ gaccesses G e a := by
  rw [gaccB, decide_eq_true_iff, gaccessesAddrs]

/-- The events an edge's endpoints must be. -/
theorem gwritesByteGevents (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → w ∈ gevents G := by
  rintro ⟨l, _, _, _, hl, _⟩
  exact geventsOfLbl G w l hl

theorem greadsByteGevents (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G r a t v → r ∈ gevents G := by
  rintro ⟨l, _, _, _, _, hl, _⟩
  exact geventsOfLbl G r l hl

theorem gpoGevents (G : Gexec) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → e1 ∈ gevents G ∧ e2 ∈ gevents G := by
  rintro ⟨_, _, h1, h2⟩
  exact ⟨(geventsSpec G e1).2 h1, (geventsSpec G e2).2 h2⟩

/-! # 4. The ppo_cat arms -/

def gppo1B (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && (gaccAddrs G e1).any (fun a => gwaB G e2 a)

theorem gppo1BSpec (G : Gexec) (e1 e2 : Geid) : gppo1B G e1 e2 = true ↔ gppo1 G e1 e2 := by
  rw [gppo1B, Bool.and_eq_true, gpoBSpec, existsbExistsTrue]
  unfold gppo1
  constructor
  · rintro ⟨hpo, a, ha, hw⟩
    exact ⟨hpo, a, (gaccessesAddrs G e1 a).2 ha, (gwaBSpec G e2 a).1 hw⟩
  · rintro ⟨hpo, a, ha, hw⟩
    exact ⟨hpo, a, (gaccessesAddrs G e1 a).1 ha, (gwaBSpec G e2 a).2 hw⟩

/-- "No same-hart write to `a` po-between `e1` and `e2`". -/
def gnointB (G : Gexec) (e1 e2 : Geid) (a : Int) : Bool :=
  (gevents G).all (fun w => !(gwaB G w a && gpoB G e1 w && gpoB G w e2))

theorem gnointBSpec (G : Gexec) (e1 e2 : Geid) (a : Int) :
    gnointB G e1 e2 a = true ↔
    (∀ w v, gwritesByte G w a v → WeakRvwmoGraph.gpo G e1 w → WeakRvwmoGraph.gpo G w e2 → False) := by
  rw [gnointB, forallbForallTrue]
  constructor
  · intro H w v hw h1 h2
    have h := H w (gwritesByteGevents G w a v hw)
    rw [(gwaBSpec G w a).2 ⟨v, hw⟩, (gpoBSpec G e1 w).2 h1, (gpoBSpec G w e2).2 h2] at h
    cases h
  · intro H w _
    cases hc : (gwaB G w a && gpoB G e1 w && gpoB G w e2) with
    | false => rfl
    | true =>
      rw [Bool.and_eq_true, Bool.and_eq_true] at hc
      obtain ⟨⟨hw, h1⟩, h2⟩ := hc
      obtain ⟨v, hw⟩ := (gwaBSpec G w a).1 hw
      exact (H w v hw ((gpoBSpec G e1 w).1 h1) ((gpoBSpec G w e2).1 h2)).elim

def gppo2B (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 &&
  (grdBytes G e1).any (fun x : (Int × Nat) × BitVec 8 =>
    (grdBytes G e2).any (fun y : (Int × Nat) × BitVec 8 =>
      decide (y.1.1 = x.1.1) && !(decide (x.1.2 = y.1.2)) &&
      gnointB G e1 e2 x.1.1))

theorem gppo2BSpec (G : Gexec) (e1 e2 : Geid) : gppo2B G e1 e2 = true ↔ gppo2 G e1 e2 := by
  rw [gppo2B, Bool.and_eq_true, gpoBSpec, existsbExistsTrue]
  unfold gppo2
  constructor
  · rintro ⟨hpo, ⟨⟨a, t1⟩, v1⟩, hx, h⟩
    refine ⟨hpo, ?_⟩
    obtain ⟨⟨⟨a2, t2⟩, v2⟩, hy, h⟩ := (existsbExistsTrue _ _).1 h
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true',
      decide_eq_false_iff_not, gnointBSpec] at h
    obtain ⟨⟨heq, hne⟩, hno⟩ := h
    dsimp only at heq hne hno
    subst heq
    exact ⟨a2, t1, v1, t2, v2, (greadsByteBytes G e1 a2 t1 v1).2 hx,
      (greadsByteBytes G e2 a2 t2 v2).2 hy, hne, hno⟩
  · rintro ⟨hpo, a, t1, v1, t2, v2, h1, h2, hne, hno⟩
    refine ⟨hpo, ((a, t1), v1), (greadsByteBytes G e1 a t1 v1).1 h1, ?_⟩
    refine (existsbExistsTrue _ _).2 ⟨((a, t2), v2), (greadsByteBytes G e2 a t2 v2).1 h2, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true',
      decide_eq_false_iff_not, gnointBSpec]
    exact ⟨⟨rfl, hne⟩, hno⟩

def gppo3B (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && glblB G e1 lbIsRmw &&
  (grdBytes G e2).any (fun x : (Int × Nat) × BitVec 8 => decide (gwriteAt G x.1.2 = some e1))

theorem gppo3BSpec (G : Gexec) (e1 e2 : Geid) : gppo3B G e1 e2 = true ↔ gppo3 G e1 e2 := by
  rw [gppo3B, Bool.and_eq_true, Bool.and_eq_true, gpoBSpec, glblBSpec, existsbExistsTrue]
  unfold gppo3 grfAt
  constructor
  · rintro ⟨⟨hpo, hrmw⟩, ⟨⟨a, t⟩, v⟩, hx, h⟩
    rw [decide_eq_true_iff] at h
    exact ⟨hpo, hrmw, a, t, v, (greadsByteBytes G e2 a t v).2 hx, h⟩
  · rintro ⟨hpo, hrmw, a, t, v, hrd, hat⟩
    exact ⟨⟨hpo, hrmw⟩, ((a, t), v), (greadsByteBytes G e2 a t v).1 hrd, decide_eq_true hat⟩

def gfcovB (G : Gexec) (e1 e2 : Geid) (kf : Nat) : Bool :=
  match gxLbl G (e1.1, kf) with
  | some (LFence pr pw sr sw) =>
      ((glblB G e1 lbIsR && pr) || (glblB G e1 lbIsW && pw)) &&
      ((glblB G e2 lbIsR && sr) || (glblB G e2 lbIsW && sw))
  | _ => false

theorem gfcovBSpec (G : Gexec) (e1 e2 : Geid) (kf : Nat) :
    gfcovB G e1 e2 kf = true ↔ gfcovAt G e1 e2 kf := by
  unfold gfcovB gfcovAt
  cases gxLbl G (e1.1, kf) with
  | none => simp
  | some l =>
    cases l with
    | LFence pr pw sr sw =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, glblBSpec]
    | _ => simp

def gfenceB (G : Gexec) (e1 e2 : Geid) : Bool :=
  decide (e1.1 = e2.1) && decide (e1.2 < e2.2) &&
  (List.range' (e1.2 + 1) (e2.2 - (e1.2 + 1))).any (fun kf => gfcovB G e1 e2 kf)

theorem gfenceBSpec (G : Gexec) (e1 e2 : Geid) : gfenceB G e1 e2 = true ↔ gfenceCovers G e1 e2 := by
  rw [gfenceCoversAlt, gfenceB, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, existsbExistsTrue]
  constructor
  · rintro ⟨⟨h1, h2⟩, kf, hkf, hc⟩
    exact ⟨h1, h2, kf, hkf, (gfcovBSpec G e1 e2 kf).1 hc⟩
  · rintro ⟨h1, h2, kf, hkf, hc⟩
    exact ⟨⟨h1, h2⟩, kf, hkf, (gfcovBSpec G e1 e2 kf).2 hc⟩

def gacqB (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && glblB G e1 lbIsR && glblB G e1 lbAq && glblB G e2 lbIsMem

theorem gacqBSpec (G : Gexec) (e1 e2 : Geid) : gacqB G e1 e2 = true ↔ gacqPo G e1 e2 := by
  rw [gacqB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, gpoBSpec, glblBSpec,
    glblBSpec, glblBSpec]
  unfold gacqPo gmem
  exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩

def grcscB (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && glblB G e1 lbRcsc && glblB G e2 lbRcsc

theorem grcscBSpec (G : Gexec) (e1 e2 : Geid) : grcscB G e1 e2 = true ↔ grcsc G e1 e2 := by
  rw [grcscB, Bool.and_eq_true, Bool.and_eq_true, gpoBSpec, glblBSpec, glblBSpec]
  unfold grcsc
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

def gppoCat6B (G : Gexec) (e1 e2 : Geid) : Bool :=
  gppo1B G e1 e2 || gppo2B G e1 e2 || gppo3B G e1 e2 ||
  gfenceB G e1 e2 || gacqB G e1 e2 || grcscB G e1 e2

theorem gppoCat6BSpec (G : Gexec) (e1 e2 : Geid) : gppoCat6B G e1 e2 = true ↔ gppoCat6 G e1 e2 := by
  simp only [gppoCat6B, Bool.or_eq_true, gppo1BSpec, gppo2BSpec, gppo3BSpec, gfenceBSpec,
    gacqBSpec, grcscBSpec, or_assoc]
  rfl

/-- ppo⁻'s `gpoloc`, for the FAILING verdicts. -/
def gpolocB (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && (gaccAddrs G e1).any (fun a => gaccB G e2 a)

theorem gpolocBSpec (G : Gexec) (e1 e2 : Geid) : gpolocB G e1 e2 = true ↔ gpoloc G e1 e2 := by
  rw [gpolocAlt, gpolocB, Bool.and_eq_true, gpoBSpec, existsbExistsTrue]
  constructor
  · rintro ⟨hpo, a, ha, hb⟩
    exact ⟨hpo, a, ha, (gaccBSpec G e2 a).1 hb⟩
  · rintro ⟨hpo, a, ha, hb⟩
    exact ⟨hpo, a, ha, (gaccBSpec G e2 a).2 hb⟩

/-- The one-line refutation of RVWMO⁻: a `gpoloc` edge that is not gmo-forward. -/
theorem notMinusOfPoloc (G : Gexec) (e1 e2 : Geid) :
    gpolocB G e1 e2 = true → gmoLtB G e1 e2 = false → ¬ rvwmoMinusConsistent G := by
  rintro hpl hmo ⟨_, hppo, _, _⟩
  have h := (gmoLtBSpec G e1 e2).2 (hppo e1 e2 (Or.inl ((gpolocBSpec G e1 e2).1 hpl)))
  rw [hmo] at h
  cases h

/-! # 5. rf / co / fr and the ob step -/

def grfB (G : Gexec) (w r : Geid) : Bool :=
  (grdBytes G r).any (fun x : (Int × Nat) × BitVec 8 => decide (gwriteAt G x.1.2 = some w))

theorem grfBSpec (G : Gexec) (w r : Geid) : grfB G w r = true ↔ WeakRvwmoAcyc.grf G w r := by
  rw [grfAlt, grfB, existsbExistsTrue]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, of_decide_eq_true h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, decide_eq_true h⟩

/-- RULE 12 over an edge list. -/
def gppo12B (G : Gexec) (dd : List (Geid × Geid)) (a b : Geid) : Bool :=
  decide (a.1 = b.1) &&
  dd.any (fun rw : Geid × Geid => decide (rw.1 = a) && grfB G rw.2 b)

theorem gppo12BSpec (G : Gexec) (dd : List (Geid × Geid)) (a b : Geid) :
    gppo12B G dd a b = true ↔ gppo12 G dd a b := by
  rw [gppo12B, Bool.and_eq_true, decide_eq_true_iff, existsbExistsTrue]
  unfold gppo12
  constructor
  · rintro ⟨hag, ⟨a', m⟩, hin, h⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, grfBSpec] at h
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    subst h1
    exact ⟨hag, m, hin, h2⟩
  · rintro ⟨hag, m, hin, hrf⟩
    refine ⟨hag, (a, m), hin, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, grfBSpec]
    exact ⟨rfl, hrf⟩

def gppoCatB (GD : Gdexec) (e1 e2 : Geid) : Bool :=
  gppoCat6B GD.gdG e1 e2 || gppo12B GD.gdG GD.gdDeps e1 e2

theorem gppoCatBSpec (GD : Gdexec) (e1 e2 : Geid) : gppoCatB GD e1 e2 = true ↔ gppoCat GD e1 e2 := by
  rw [gppoCatB, Bool.or_eq_true, gppoCat6BSpec, gppo12BSpec]
  rfl

/-- The one-line refutation of the cat model: a rule-12 edge that is not
gmo-forward. -/
theorem notCatOfRule12 (GD : Gdexec) (a b : Geid) :
    gppo12B GD.gdG GD.gdDeps a b = true → gmoLtB GD.gdG a b = false →
    ¬ rvwmoCatConsistent GD := by
  rintro h12 hmo ⟨_, hppo, _⟩
  have h := (gmoLtBSpec _ a b).2 (hppo a b (Or.inr ((gppo12BSpec _ _ a b).1 h12)))
  rw [hmo] at h
  cases h

def grfeB (G : Gexec) (w r : Geid) : Bool :=
  grfB G w r && !(decide (w.1 = r.1))

theorem grfeBSpec (G : Gexec) (w r : Geid) : grfeB G w r = true ↔ grfe G w r := by
  rw [grfeB, Bool.and_eq_true, grfBSpec, Bool.not_eq_true', decide_eq_false_iff_not]
  rfl

def gcoB (G : Gexec) (w w' : Geid) : Bool :=
  decide (gwix G w < gwix G w') &&
  (gwrBytes G w).any (fun x : Int × BitVec 8 => gwaB G w' x.1)

theorem gcoBSpec (G : Gexec) (w w' : Geid) : gcoB G w w' = true ↔ gco G w w' := by
  rw [gcoB, Bool.and_eq_true, decide_eq_true_iff, existsbExistsTrue]
  unfold gco
  constructor
  · rintro ⟨hlt, ⟨a, v⟩, hx, h⟩
    obtain ⟨v', h'⟩ := (gwaBSpec G w' a).1 h
    exact ⟨a, v, v', (gwritesByteBytes G w a v).2 hx, h', hlt⟩
  · rintro ⟨a, v, v', h1, h2, hlt⟩
    exact ⟨hlt, (a, v), (gwritesByteBytes G w a v).1 h1, (gwaBSpec G w' a).2 ⟨v', h2⟩⟩

def gfrB (G : Gexec) (r w' : Geid) : Bool :=
  !(decide (r = w')) &&
  (grdBytes G r).any (fun x : (Int × Nat) × BitVec 8 =>
    decide (x.1.2 < gwix G w') && gwaB G w' x.1.1)

theorem gfrBSpec (G : Gexec) (r w' : Geid) : gfrB G r w' = true ↔ gfr G r w' := by
  rw [gfrB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, existsbExistsTrue]
  unfold gfr
  constructor
  · rintro ⟨hne, ⟨⟨a, t⟩, v⟩, hx, h⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hlt, hw⟩ := h
    obtain ⟨v', hw⟩ := (gwaBSpec G w' a).1 hw
    exact ⟨hne, a, t, v, v', (greadsByteBytes G r a t v).2 hx, hw, hlt⟩
  · rintro ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
    refine ⟨hne, ((a, t), v), (greadsByteBytes G r a t v).1 hrd, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨hlt, (gwaBSpec G w' a).2 ⟨v', hwb⟩⟩

def gobrCatB (GD : Gdexec) (x y : Geid) : Bool :=
  gppoCatB GD x y || decide ((x, y) ∈ GD.gdDeps) ||
  grfeB GD.gdG x y || gcoB GD.gdG x y || gfrB GD.gdG x y

theorem gobrCatBSpec (GD : Gdexec) (x y : Geid) : gobrCatB GD x y = true ↔ gobrCat GD x y := by
  simp only [gobrCatB, Bool.or_eq_true, gppoCatBSpec, decide_eq_true_iff, grfeBSpec, gcoBSpec,
    gfrBSpec, or_assoc]
  rfl

/-- An ob step's endpoints are events (so enumerating `gevents` sees every
edge). -/
theorem gobrCatGevents (GD : Gdexec) (x y : Geid) :
    rvwmoCatConsistent GD → gobrCat GD x y →
    x ∈ gevents GD.gdG ∧ y ∈ gevents GD.gdG := by
  rintro ⟨_, _, _, _, hdw, _⟩ (h | h | h | h | h)
  · obtain ⟨_, h1, h2⟩ := gppoCatEvents GD x y hdw h
    exact ⟨(geventsSpec _ x).2 h1, (geventsSpec _ y).2 h2⟩
  · obtain ⟨_, _, ⟨l1, h1, _⟩, ⟨l2, h2, _⟩⟩ := hdw (x, y) h
    exact ⟨geventsOfLbl _ x l1 h1, geventsOfLbl _ y l2 h2⟩
  · obtain ⟨⟨a, t, v, hrd, hat⟩, _⟩ := h
    refine ⟨?_, greadsByteGevents _ y a t v hrd⟩
    have hw := ((gwritesElemOf _ x).1 (gwriteAtGwrites _ t x hat)).2
    unfold gisW at hw
    cases hl : gxLbl GD.gdG x with
    | none => rw [hl] at hw; cases hw
    | some l => exact geventsOfLbl _ x l hl
  · obtain ⟨a, v, v', h1, h2, _⟩ := h
    exact ⟨gwritesByteGevents _ x a v h1, gwritesByteGevents _ y a v' h2⟩
  · obtain ⟨_, a, t, v, v', h1, h2, _⟩ := h
    exact ⟨greadsByteGevents _ x a t v h1, gwritesByteGevents _ y a v' h2⟩

/-! # 6. The model, as one boolean -/

def gshapeB (l : Lbl) : Bool :=
  match l with
  | LLoad _ _ ts vs => decide (vs.length = ts.length)
  | LStore _ _ vs _ => match vs with | [] => false | _ :: _ => true
  | LFence _ _ _ _ => true
  | LRmw _ _ _ ts rvs wvs _ =>
      (match wvs with | [] => false | _ :: _ => true) &&
      decide (wvs.length = ts.length) && decide (rvs.length = ts.length)
  | LIo .. => true

theorem gshapeBSpec (l : Lbl) :
    gshapeB l = true →
    match l with
    | LLoad _ _ ts vs => vs.length = ts.length
    | LStore _ _ vs _ => vs ≠ []
    | LFence _ _ _ _ => True
    | LRmw _ _ _ ts rvs wvs _ =>
        wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
    | LIo .. => True := by
  cases l with
  | LLoad _ _ ts vs => exact of_decide_eq_true
  | LStore _ _ vs _ => cases vs <;> simp [gshapeB]
  | LFence _ _ _ _ => intro _; trivial
  | LRmw _ _ _ ts rvs wvs _ =>
    cases wvs <;> simp [gshapeB]
  | LIo => intro _; trivial

def gwfB (G : Gexec) : Bool :=
  decide G.gxGmo.Nodup &&
  G.gxGmo.all (fun e => glblB G e lbIsMem) &&
  (gevents G).all (fun e => !(glblB G e lbIsMem) || decide (e ∈ G.gxGmo)) &&
  (gevents G).all (fun e => match gxLbl G e with | some l => gshapeB l | none => true)

theorem gwfBSound (G : Gexec) : gwfB G = true → gwf G := by
  rw [gwfB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rintro ⟨⟨⟨hnd, hmem1⟩, hmem2⟩, hsh⟩
  refine ⟨of_decide_eq_true hnd, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      exact (glblBSpec G e lbIsMem).1 ((forallbForallTrue _ _).1 hmem1 e he)
    · intro he
      have hin : e ∈ gevents G := by
        obtain ⟨l, hl, _⟩ := he
        exact geventsOfLbl G e l hl
      have h := (forallbForallTrue _ _).1 hmem2 e hin
      rw [(glblBSpec G e lbIsMem).2 he, Bool.not_true, Bool.false_or] at h
      exact of_decide_eq_true h
  · intro i p k l hp hk
    have hl : gxLbl G (i, k) = some l := by
      unfold gxLbl
      rw [hp]
      exact hk
    have h := (forallbForallTrue _ _).1 hsh (i, k) (geventsOfLbl G (i, k) l hl)
    rw [hl] at h
    exact gshapeBSpec l h

/-- "ppo ⊆ gmo", GENERIC in the ppo boolean: instantiated with and without
rule 12. -/
def ppoGmoB (P : Geid → Geid → Bool) (G : Gexec) : Bool :=
  (gevents G).all (fun e1 => (gevents G).all (fun e2 => !(P e1 e2) || gmoLtB G e1 e2))

theorem ppoGmoBSound (P : Geid → Geid → Bool) (Pp : Geid → Geid → Prop) (G : Gexec) :
    (∀ x y, P x y = true ↔ Pp x y) →
    (∀ x y, Pp x y → x ∈ gevents G ∧ y ∈ gevents G) →
    ppoGmoB P G = true → ∀ x y, Pp x y → gmoLt G x y := by
  intro hspec hev H x y hp
  obtain ⟨h1, h2⟩ := hev x y hp
  have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 H x h1) y h2
  rw [(hspec x y).2 hp, Bool.not_true, Bool.false_or] at h
  exact (gmoLtBSpec G x y).1 h

theorem gppoCat6GmoBSound (G : Gexec) : ppoGmoB (gppoCat6B G) G = true → gppoCat6Gmo G := by
  intro H e1 e2 hp
  exact ppoGmoBSound _ (gppoCat6 G) G (gppoCat6BSpec G)
    (fun x y h' => gpoGevents G x y (gppoCat6Gpo G x y h')) H e1 e2 hp

theorem gppoCatGmoBSound (GD : Gdexec) :
    gdepsWf GD.gdG GD.gdDeps →
    ppoGmoB (gppoCatB GD) GD.gdG = true → gppoCatGmo GD := by
  intro hdw H e1 e2 hp
  refine ppoGmoBSound _ (gppoCat GD) GD.gdG (gppoCatBSpec GD) ?_ H e1 e2 hp
  intro x y h'
  obtain ⟨_, h1, h2⟩ := gppoCatEvents GD x y hdw h'
  exact ⟨(geventsSpec _ x).2 h1, (geventsSpec _ y).2 h2⟩

def gimgB (G : Gexec) (a : Int) (v : BitVec 8) : Bool :=
  match G.gxImg a with
  | some v' => bvEqb v' v
  | none => false

theorem gimgBSpec (G : Gexec) (a : Int) (v : BitVec 8) : gimgB G a v = true ↔ G.gxImg a = some v := by
  unfold gimgB
  cases G.gxImg a with
  | none => simp
  | some v' => rw [bvEqbSpec, Option.some.injEq]

def glvSrcB (G : Gexec) (e : Geid) (x : (Int × Nat) × BitVec 8) : Bool :=
  match x.1.2 with
  | 0 => gimgB G x.1.1 x.2
  | _ + 1 =>
    match gwriteAt G x.1.2 with
    | some w => gwbB G w x.1.1 x.2 && gvisB G w e
    | none => false

def glvMaxB (G : Gexec) (e : Geid) (x : (Int × Nat) × BitVec 8) : Bool :=
  (gevents G).all (fun w' =>
    !(gwaB G w' x.1.1 && gvisB G w' e) || decide (gwix G w' ≤ x.1.2))

def gloadValueB (G : Gexec) : Bool :=
  (gevents G).all (fun e =>
    (grdBytes G e).all (fun x => glvSrcB G e x && glvMaxB G e x))

theorem gloadValueBSound (G : Gexec) : gloadValueB G = true → gloadValue G := by
  intro H e a t v hrd
  have h := (forallbForallTrue _ _).1
    ((forallbForallTrue _ _).1 H e (greadsByteGevents G e a t v hrd))
    ((a, t), v) ((greadsByteBytes G e a t v).1 hrd)
  rw [Bool.and_eq_true] at h
  obtain ⟨hsrc, hmax⟩ := h
  refine ⟨?_, ?_⟩
  · unfold glvSrcB at hsrc
    dsimp only at hsrc
    cases t with
    | zero => exact (gimgBSpec G a v).1 hsrc
    | succ t =>
      dsimp only at hsrc ⊢
      cases hw : gwriteAt G (t + 1) with
      | none => rw [hw] at hsrc; cases hsrc
      | some w =>
        rw [hw, Bool.and_eq_true] at hsrc
        obtain ⟨hwb, hvis⟩ := hsrc
        exact ⟨w, rfl, (gwbBSpec G w a v).1 hwb, (gvisBSpec G w e).1 hvis⟩
  · intro w' v' hw' hvis
    have h := (forallbForallTrue _ _).1 hmax w' (gwritesByteGevents G w' a v' hw')
    dsimp only at h
    rw [(gwaBSpec G w' a).2 ⟨v', hw'⟩, (gvisBSpec G w' e).2 hvis, Bool.and_true, Bool.not_true,
      Bool.false_or] at h
    exact of_decide_eq_true h

def gatomB (G : Gexec) : Bool :=
  (gevents G).all (fun e => !(glblB G e lbIsW) ||
    (grdBytes G e).all (fun x : (Int × Nat) × BitVec 8 =>
      (gevents G).all (fun w' => !(gwaB G w' x.1.1) ||
        !(decide (x.1.2 < gwix G w') && decide (gwix G w' < gwix G e)))))

theorem gatomBSound (G : Gexec) : gatomB G = true → gatomicity G := by
  intro H e a t v hrd hw w' v' hw' hlt
  have h := (forallbForallTrue _ _).1 H e (greadsByteGevents G e a t v hrd)
  rw [(glblBSpec G e lbIsW).2 hw, Bool.not_true, Bool.false_or] at h
  have h2 := (forallbForallTrue _ _).1
    ((forallbForallTrue _ _).1 h ((a, t), v) ((greadsByteBytes G e a t v).1 hrd))
    w' (gwritesByteGevents G w' a v' hw')
  dsimp only at h2
  rw [(gwaBSpec G w' a).2 ⟨v', hw'⟩, decide_eq_true hlt.1, decide_eq_true hlt.2] at h2
  cases h2

def gdepsWfB (G : Gexec) (deps : List (Geid × Geid)) : Bool :=
  deps.all (fun rw : Geid × Geid =>
    decide (rw.1.1 = rw.2.1) && decide (rw.1.2 < rw.2.2) &&
    glblB G rw.1 lbIsR && glblB G rw.2 lbIsW)

theorem gdepsWfBSound (G : Gexec) (deps : List (Geid × Geid)) :
    gdepsWfB G deps = true → gdepsWf G deps := by
  intro H rw hrw
  have h := (forallbForallTrue _ _).1 H rw hrw
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, glblBSpec, glblBSpec] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

def gdepsGmoB (G : Gexec) (deps : List (Geid × Geid)) : Bool :=
  deps.all (fun rw : Geid × Geid => gmoLtB G rw.1 rw.2)

theorem gdepsGmoBSound (G : Gexec) (deps : List (Geid × Geid)) :
    gdepsGmoB G deps = true → gdepsGmo G deps := by
  intro H rw hrw
  exact (gmoLtBSpec G rw.1 rw.2).1 ((forallbForallTrue _ _).1 H rw hrw)

/-- The model, with and without rule 12. -/
def axiomsB (GD : Gdexec) : Bool :=
  gwfB GD.gdG && gloadValueB GD.gdG && gatomB GD.gdG &&
  gdepsWfB GD.gdG GD.gdDeps && gdepsGmoB GD.gdG GD.gdDeps

def catConsistentB (GD : Gdexec) : Bool :=
  axiomsB GD && ppoGmoB (gppoCatB GD) GD.gdG

def cat6ConsistentB (GD : Gdexec) : Bool :=
  axiomsB GD && ppoGmoB (gppoCat6B GD.gdG) GD.gdG

theorem axiomsBSound (GD : Gdexec) :
    axiomsB GD = true →
    gwf GD.gdG ∧ gloadValue GD.gdG ∧ gatomicity GD.gdG ∧
    gdepsWf GD.gdG GD.gdDeps ∧ gdepsGmo GD.gdG GD.gdDeps := by
  rw [axiomsB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rintro ⟨⟨⟨⟨hwf, hlv⟩, hat⟩, hdw⟩, hdg⟩
  exact ⟨gwfBSound _ hwf, gloadValueBSound _ hlv, gatomBSound _ hat, gdepsWfBSound _ _ hdw,
    gdepsGmoBSound _ _ hdg⟩

theorem catConsistentBSound (GD : Gdexec) : catConsistentB GD = true → rvwmoCatConsistent GD := by
  rw [catConsistentB, Bool.and_eq_true]
  rintro ⟨hax, hppo⟩
  obtain ⟨hwf, hlv, hat, hdw, hdg⟩ := axiomsBSound GD hax
  exact ⟨hwf, gppoCatGmoBSound GD hdw hppo, hlv, hat, hdw, hdg⟩

theorem cat6ConsistentBSound (GD : Gdexec) :
    cat6ConsistentB GD = true → rvwmoCat6Consistent GD := by
  rw [cat6ConsistentB, Bool.and_eq_true]
  rintro ⟨hax, hppo⟩
  obtain ⟨hwf, hlv, hat, hdw, hdg⟩ := axiomsBSound GD hax
  exact ⟨hwf, gppoCat6GmoBSound _ hppo, hlv, hat, hdw, hdg⟩

/-! # 7. The checker computes (no Rocq twin; header deviation 4) -/

example : catConsistentB lbgd = true := by decide +kernel

end Weak
