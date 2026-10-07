/-
Weak: **THE TWO-MOVE (W,W) NORMALIZATION, AND WHAT IT COSTS** (a leaf).

Rocq: `iris/WeakRvwmoPreNorm2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoPreNorm` normalizes the same-hart write order by DESCENDING the po-minimal write
witness and pays with three residual kills, each reducible to the missing edge `wwGapLink`.
This file runs the analysis to its conclusion: the exchange kit is not the right instrument.

  §1  `normalizeWw2` — `racyD`-acyclicity ALONE gives a normalized `gdEquiv` member (no kill,
      no `wwGapLink`, no orbit quantification): `racyD` contains rule 14's own edge `gpow`, so
      `normalizeOfAcyclic'` retimes to a rule-14 graph and `gwrowGmoOfRule14` reads off the
      conclusion.  PreNorm §7's counterexample is `racyD`-acyclic, hence covered.
  §2  `gwrowGmo` enters the walk at exactly one place (`wlkStep'OfSupply` step 3); `gwrowSeg`
      states that use site and `gwrowSegIff` proves it EQUIVALENT to `gwrowGmo` (the range
      restriction is vacuous — a negative result).
  §3  THE REAL REDUCTION.  `WeakRvwmoTopo`'s linearization uses the `gpow` arm only in
      `linGrule14`; so a linear extension of `rwwD` (= `racyD` with `gpow` narrowed to `gpoww`,
      po between two writes of one hart) re-times to a consistent graph with `gwrowGmo`
      (`topoLinearizesW`, `normalizeWw3`).  LB cycles run through `gpow` edges OUT OF A READ,
      which `rwwD` lacks.
  §4  SHARPNESS AND TRANSPORT.  `rwwt` (`rwwD` minus `gco`/`gfr`) transports along `gdEquiv`
      and its acyclicity is NECESSARY; the gap is exactly `gco` ∪ `gfr`.  The `racyD` cycle
      transport with its exact side condition, and the monotone instance.
  §5  The remaining obligation: the orbit pull-back forces `gwrowGmo` (not a route);
      `killAtMember` / `orbitCycleTransport` / `cycleKillOfMember`; the residue `wwResidue`.

The `Print Assumptions` are Rocq commands.  A LEAF: nothing imports this file.

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoPreNorm` deviation 1 and `WeakRvwmoTopo` deviations 1–2
   (`Racy`/`RacyD` ↦ `racy`/`racyD`; `Rww`/`RwwD`/`Rwwt` ↦ `rww`/`rwwD`/`rwwt`; `agent` ↦
   `Nat`, `dev_state` ↦ `Efab`, `image` ↦ `Image`; `GDExec g d` ↦ `⟨g, d⟩`; `tc_mono` ↦
   `tcMono`).
2. SECTION `topo_linw`: as `WeakRvwmoTopo` deviation 3 — the Rocq `Local Lemma`s are top-level
   theorems over `GD L hcons hlin` (all four `include`d).  Their proofs are `WeakRvwmoTopo`'s
   `topo_lin` proofs with the first `racy` arm replaced (as in Rocq).
3. `gwrowGmoOfGwrowSeg`: the Rocq `Decision (Bad p)` (built through `list_exists_dec`) is
   replaced by `classical` (it only feeds a `filter` inside a proof).
4. The `Global Instance`s `gpoww_dec`/`rww_dec`/`rwwD_dec` are global `instance`s built by
   `unfold; infer_instance` over `WeakRvwmoDec`'s global instances.
5. O2 / STAGE C: nothing to do.  This file has no capstone (no WP/adequacy statement), so no
   `efetchItvOk` premise arises; `wsupply` is the Lean (Stage C) one.

**Rocq → Lean name map.**  `normalize_ww2` `normalizeWw2`, `normalize_ww_no_gap_link`
`normalizeWwNoGapLink`, `gwrow_seg` `gwrowSeg`, `gwrow_seg_of_gwrow_gmo` `gwrowSegOfGwrowGmo`,
`gwrow_gmo_of_gwrow_seg` `gwrowGmoOfGwrowSeg`, `gwrow_seg_iff` `gwrowSegIff`, `gpoww` `gpoww`,
`gpoww_gpow` `gpowwGpow`, `Rww` `rww`, `RwwD` `rwwD`, `Rww_Racy` `rwwRacy`, `RwwD_RacyD`
`rwwDRacyD`, `RwwD_acyclic_of_RacyD` `rwwDAcyclicOfRacyD`, `gpoww_dec` `gpowwDec`, `rww_dec`
`rwwDec`, `rwwD_dec` `rwwDDec`, `RwwD_mem` `rwwDMem`, `linw_extD` `linwExtD`, `linw_wf`/`_lv`/
`_at`/`_perm`/`_rows`/`_nodup`/`_wfilter`/`_wlen`/`_welem`/`_wat`/`_wperm`/`_before` ↦
`linwWf`/`linwLv`/`linwAt`/`linwPerm`/`linwRows`/`linwNodup`/`linwWfilter`/`linwWlen`/
`linwWelem`/`linwWat`/`linwWperm`/`linwBefore`, `step_rww` `stepRww`, `step_dep`
`WeakRvwmoPreNorm2.stepDep`, `linw_co_fwd`/`_inv` `linwCoFwd`/`linwCoInv`, `linw_gwf`/
`_gppo`/`_gwrow`/`_gload_value`/`_gatomicity`/`_gdeps_wf`/`_gdeps_gmo` ↦ `linwGwf`/`linwGppo`/
`linwGwrow`/`linwGloadValue`/`linwGatomicity`/`linwGdepsWf`/`linwGdepsGmo`,
`topo_linearizes_w` `topoLinearizesW`, `topo_exists_w` `topoExistsW`, `normalize_ww3`
`normalizeWw3`, `normalize_ww2_of_ww3` `normalizeWw2OfWw3`, `Rwwt` `rwwt`, `Rwwt_RwwD`
`rwwtRwwD`, `Rwwt_gd_equiv` `rwwtGdEquiv`, `Rwwt_cycle_transport` `rwwtCycleTransport`,
`Rwwt_gmo` `rwwtGmo`, `Rwwt_acyclic_of_gwrow` `rwwtAcyclicOfGwrow`, `Rwwt_acyclic_necessary`
`rwwtAcyclicNecessary`, `RacyD_transport` `racyDTransport`, `cycle_transport`
`cycleTransport`, `cycle_transport_mono` `cycleTransportMono`,
`wsupply_orbit_pull_forces_gwrow` `wsupplyOrbitPullForcesGwrow`, `kill_at_member`
`killAtMember`, `orbit_cycle_transport` `orbitCycleTransport`, `cycle_kill_of_member`
`cycleKillOfMember`, `orbit_cycle_transport_Rwwt` `orbitCycleTransportRwwt`, `ww_residue`
`wwResidue`, `ww_residue_gives_gwrow` `wwResidueGivesGwrow`, `ww_residue_of_acyclic`
`wwResidueOfAcyclic`.

**File-qualified names:** `step_dep` (in `notes/weak-port-dupnames.json`) ↦
`WeakRvwmoPreNorm2.stepDep`; no Lean-only helpers.

**Dropped:** none (Rocq 63 declarations; Lean 63).
-/
import Weak.WeakRvwmoPreNorm
import Weak.WeakRvwmoDec
import Weak.WeakRvwmoLinInd
import Weak.WeakRvwmoHull

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. THE THEOREM: acyclicity alone, both moves at once -/

/-- `racyD` carries `gpow` — rule 14's own edge — so any topological order of an acyclic
`racyD` puts a violating pair in program order: the retiming performs the ascent. -/
theorem normalizeWw2 (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG := by
  intro hcons hacy
  obtain ⟨GD', pi, hcons', h14, hrows, hdeps, hwp⟩ := normalizeOfAcyclic' GD hcons hacy
  exact ⟨GD', ⟨pi, hrows, hwp, hdeps, hcons'⟩, gwrowGmoOfRule14 _ hcons'.1.1 h14⟩

/-- THE §7 COUNTEREXAMPLE, RE-EXAMINED: `normalizeWwOfAcyclic`'s conclusion without its
`wwGapLink` premise and without orbit quantification. -/
theorem normalizeWwNoGapLink (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG :=
  normalizeWw2 GD

/-! # 2. THE WALK'S USE SITE, AND WHY RESTRICTING IT BUYS NOTHING -/

/-- `wlkStep'OfSupply` step 3, verbatim: no row position in `[k0, kz)` is a write. -/
def gwrowSeg (G : Gexec) : Prop :=
  ∀ (n : Nat) (x : Nat) (kz k0 j : Nat) (lb : Lbl),
    gwriteAt G (n + 1) = some (x, kz) →
    wposHi G n x k0 →
    k0 ≤ j → j < kz →
    gxLbl G (x, j) = some lb → lbIsW lb = false

theorem gwrowSegOfGwrowGmo (G : Gexec) : gwf G → gwrowGmo G → gwrowSeg G := by
  intro hwf hrow n x kz k0 j lb hat hhi hk0 hjkz hlj
  have hnd : G.gxGmo.Nodup := hwf.1
  cases hb : lbIsW lb with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨hmem, hwix⟩ := gwriteAtInv G (n + 1) (x, kz) hnd hat
    have hisw : gisW G (x, kz) = true := ((gwritesElemOf G _).1 hmem).2
    cases hlbz : gxLbl G (x, kz) with
    | none => simp [gisW, hlbz] at hisw
    | some lbz =>
      have hlbzw : lbIsW lbz = true := by simpa [gisW, hlbz] using hisw
      have hlt := hrow x j kz hjkz ⟨lb, hlj, hb⟩ ⟨lbz, hlbz, hlbzw⟩
      have hgt := hhi j lb hk0 hlj hb
      omega

/-- THE NEGATIVE RESULT: the converse, by the inversion whose later-in-po member has the
smallest write index. -/
theorem gwrowGmoOfGwrowSeg (G : Gexec) : gwf G → gwrowSeg G → gwrowGmo G := by
  classical
  intro hwf hseg x j k hjk hj hk
  have hnd : G.gxGmo.Nodup := hwf.1
  obtain ⟨lj, hlj, hbj⟩ := hj
  obtain ⟨lk, hlk, hbk⟩ := hk
  have hinj : (x, j) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlj]; rfl) (by simp only [gisW, hlj]; exact hbj)
  have hink : (x, k) ∈ gwrites G :=
    gisWGwrites G _ hwf (by rw [hlk]; rfl) (by simp only [gisW, hlk]; exact hbk)
  by_cases hlt : gwix G (x, j) < gwix G (x, k)
  · exact hlt
  exfalso
  -- the inverted pairs, indexed by their LATER-IN-PO member
  let Bad : Geid → Prop := fun p =>
    ∃ i : Nat, i < p.2 ∧ glblIs G (p.1, i) lbIsW ∧ gwix G p < gwix G (p.1, i)
  have hbadk : Bad (x, k) := by
    refine ⟨j, hjk, ⟨lj, hlj, hbj⟩, ?_⟩
    have hne : gwix G (x, j) ≠ gwix G (x, k) := by
      intro heq
      have := gwixInj G (x, j) (x, k) hnd hinj hink heq
      simp only [Prod.mk.injEq, true_and] at this
      omega
    show gwix G (x, k) < gwix G (x, j)
    omega
  have hne : (gwrites G).filter (fun p => decide (Bad p)) ≠ [] := by
    intro hnil
    have hin : (x, k) ∈ (gwrites G).filter (fun p => decide (Bad p)) :=
      List.mem_filter.2 ⟨hink, decide_eq_true hbadk⟩
    rw [hnil] at hin
    simp at hin
  obtain ⟨p, hpin, hpmin⟩ := listMinBy (gwix G) _ hne
  obtain ⟨hpw, hpbad⟩ := List.mem_filter.1 hpin
  have hpbad : Bad p := of_decide_eq_true hpbad
  obtain ⟨y, kz⟩ := p
  obtain ⟨j0, hj0lt, hj0w, hj0ix⟩ := hpbad
  simp only at hj0lt hj0w hj0ix
  -- the covering step: the walk emits `(y, kz)` at gmo index `gwix`
  have hpos : 0 < gwix G (y, kz) := WeakRvwmoGraph.gwixPos G (y, kz) hpw
  have hgw : gwix G (y, kz) = (gwix G (y, kz) - 1) + 1 := by omega
  have hat : gwriteAt G ((gwix G (y, kz) - 1) + 1) = some (y, kz) :=
    gwixPin G (y, kz) _ hnd hpw hgw
  -- the hart may be taken to stand exactly at `j0`
  have hhi : wposHi G (gwix G (y, kz) - 1) y j0 := by
    intro i lb hi hli hbi
    rcases Nat.lt_or_ge (gwix G (y, kz) - 1) (gwix G (y, i)) with h | hle
    · exact h
    exfalso
    have hini : (y, i) ∈ gwrites G :=
      gisWGwrites G _ hwf (by rw [hli]; rfl) (by simp only [gisW, hli]; exact hbi)
    have hlti : gwix G (y, i) < gwix G (y, kz) := by omega
    by_cases hij0 : i = j0
    · subst hij0
      omega
    have hij : j0 < i := by omega
    have hbadi : Bad (y, i) := ⟨j0, hij, hj0w, by show gwix G (y, i) < gwix G (y, j0); omega⟩
    have hini' : (y, i) ∈ (gwrites G).filter (fun p => decide (Bad p)) :=
      List.mem_filter.2 ⟨hini, decide_eq_true hbadi⟩
    have hm := hpmin (y, i) hini'
    omega
  obtain ⟨lb0, hlb0, hbw0⟩ := hj0w
  have := hseg _ y kz j0 j0 lb0 hat hhi (Nat.le_refl _) hj0lt hlb0
  rw [hbw0] at this
  cases this

theorem gwrowSegIff (G : Gexec) : gwf G → (gwrowSeg G ↔ gwrowGmo G) :=
  fun hwf => ⟨gwrowGmoOfGwrowSeg G hwf, gwrowSegOfGwrowGmo G hwf⟩

/-! # 3. THE REAL REDUCTION: A SMALLER RELATION SUFFICES -/

def gpoww (G : Gexec) (e w : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e w ∧ glblIs G e lbIsW ∧ glblIs G w lbIsW

theorem gpowwGpow (G : Gexec) (e w : Geid) : gpoww G e w → gpow G e w :=
  fun ⟨hpo, he, hw⟩ => ⟨hpo, WeakRvwmoGraph.glblIsWGmem G e he, glblIsWGisW G w hw⟩

/-- The same five arms as `racy`, with the first narrowed. -/
def rww (G : Gexec) (x y : Geid) : Prop :=
  gpoww G x y ∨ WeakRvwmoAcyc.grf G x y ∨ gco G x y ∨ gfr G x y ∨ gppo G x y

def rwwD (GD : Gdexec) (x y : Geid) : Prop :=
  rww GD.gdG x y ∨ (x, y) ∈ GD.gdDeps

theorem rwwRacy (G : Gexec) (x y : Geid) : rww G x y → racy G x y := by
  rintro (h | h)
  · exact Or.inl (gpowwGpow G x y h)
  · exact Or.inr h

theorem rwwDRacyD (GD : Gdexec) (x y : Geid) : rwwD GD x y → racyD GD x y := by
  rintro (h | h)
  · exact Or.inl (rwwRacy _ x y h)
  · exact Or.inr h

/-- … so `racyD`-acyclicity is STRICTLY stronger. -/
theorem rwwDAcyclicOfRacyD (GD : Gdexec) :
    (∀ x, ¬ tc (racyD GD) x x) → ∀ x, ¬ tc (rwwD GD) x x :=
  fun hacy x htc => hacy x (tcMono _ _ x x (fun a b => rwwDRacyD GD a b) htc)

instance gpowwDec (G : Gexec) (e w : Geid) : Decidable (gpoww G e w) := by
  unfold gpoww; infer_instance

instance rwwDec (G : Gexec) (x y : Geid) : Decidable (rww G x y) := by
  unfold rww; infer_instance

instance rwwDDec (GD : Gdexec) (x y : Geid) : Decidable (rwwD GD x y) := by
  unfold rwwD; infer_instance

/-- Every `rwwD` edge runs between members of the order. -/
theorem rwwDMem (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → rwwD GD x y →
    x ∈ GD.gdG.gxGmo ∧ y ∈ GD.gdG.gxGmo :=
  fun hcons hR => racyDMem GD x y hcons (rwwDRacyD GD x y hR)

/-- THE INPUT THE RE-TIMING CONSUMES, weakened. -/
def linwExtD (GD : Gdexec) (L : List Geid) : Prop :=
  L.Perm GD.gdG.gxGmo ∧ ∀ x y, rwwD GD x y → before L x y

section TopoLinw

variable (GD : Gdexec) (L : List Geid)
variable (hcons : rvwmoMinusDepsConsistent GD) (hlin : linwExtD GD L)
include hcons hlin

theorem linwWf : gwf GD.gdG := hcons.1.1
theorem linwLv : gloadValue GD.gdG := hcons.1.2.2.1
theorem linwAt : gatomicity GD.gdG := hcons.1.2.2.2
theorem linwPerm : L.Perm GD.gdG.gxGmo := hlin.1

theorem linwRows : rowsRel (tren GD.gdG L) GD.gdG (retime GD.gdG L) := retimeRowsRel GD.gdG L

/-! ## 3.1 `L` is a well-formed order, and `tren` is a write permutation -/

theorem linwNodup : L.Nodup := (linwPerm GD L hcons hlin).nodup_iff.2 (linwWf GD L hcons hlin).1

theorem linwWfilter : (L.filter (gisW GD.gdG)).Perm (gwrites GD.gdG) :=
  (linwPerm GD L hcons hlin).filter _

theorem linwWlen : (gwrites (retime GD.gdG L)).length = (gwrites GD.gdG).length := by
  rw [retimeGwrites]
  exact (linwWfilter GD L hcons hlin).length_eq

theorem linwWelem (w : Geid) : w ∈ gwrites (retime GD.gdG L) ↔ w ∈ gwrites GD.gdG := by
  rw [retimeGwrites]
  exact (linwWfilter GD L hcons hlin).mem_iff

theorem linwWat (t : Nat) : gwriteAt (retime GD.gdG L) (tren GD.gdG L t) = gwriteAt GD.gdG t := by
  cases ht : gwriteAt GD.gdG t with
  | some w =>
    rw [trenAt GD.gdG L t w ht, ← retimeGwix]
    exact gwriteAtGwix _ w ((linwWelem GD L hcons hlin w).2 (gwriteAtGwrites GD.gdG t w ht))
  | none =>
    rw [trenNone GD.gdG L t ht]
    cases t with
    | zero => rfl
    | succ i =>
      simp only [gwriteAt] at ht ⊢
      apply lookup_ge_None_2
      rw [linwWlen GD L hcons hlin]
      exact lookup_ge_None_1 ht

theorem linwWperm : wperm (tren GD.gdG L) GD.gdG (retime GD.gdG L) := by
  refine ⟨?_, linwWat GD L hcons hlin, linwWlen GD L hcons hlin⟩
  intro t1 t2 heq
  have h1 := linwWat GD L hcons hlin t1
  have h2 := linwWat GD L hcons hlin t2
  rw [heq, h2] at h1
  cases e1 : gwriteAt GD.gdG t1 with
  | some w =>
    rw [e1] at h1
    have a := (gwriteAtInv GD.gdG t1 w (linwWf GD L hcons hlin).1 e1).2
    have b := (gwriteAtInv GD.gdG t2 w (linwWf GD L hcons hlin).1 h1).2
    omega
  | none =>
    rw [e1] at h1
    have a := trenNone GD.gdG L t1 e1
    have b := trenNone GD.gdG L t2 h1
    omega

/-! ## 3.2 The bridge: `before L` IS `gmoLt` of the re-timed graph -/

theorem linwBefore (x y : Geid) : before L x y ↔ gmoLt (retime GD.gdG L) x y := by
  have hnd : (retime GD.gdG L).gxGmo.Nodup := linwNodup GD L hcons hlin
  constructor
  · rintro ⟨i, j, hi, hj, hlt⟩
    refine ⟨elem_of_list_lookup_2 hi, elem_of_list_lookup_2 hj, ?_⟩
    rw [gposOfLookup (retime GD.gdG L) i x hnd hi, gposOfLookup (retime GD.gdG L) j y hnd hj]
    exact hlt
  · rintro ⟨hx, hy, hlt⟩
    exact ⟨gpos (retime GD.gdG L) x, gpos (retime GD.gdG L) y,
      gposElemLookup (retime GD.gdG L) x hx, gposElemLookup (retime GD.gdG L) y hy, hlt⟩

theorem stepRww (x y : Geid) : rww GD.gdG x y → gmoLt (retime GD.gdG L) x y :=
  fun hR => (linwBefore GD L hcons hlin x y).1 (hlin.2 x y (Or.inl hR))

theorem WeakRvwmoPreNorm2.stepDep (x y : Geid) : (x, y) ∈ GD.gdDeps → gmoLt (retime GD.gdG L) x y :=
  fun hd => (linwBefore GD L hcons hlin x y).1 (hlin.2 x y (Or.inr hd))

/-! ## 3.3 `tren` is MONOTONE ON SAME-BYTE WRITES, both ways -/

theorem linwCoFwd (w1 w2 : Geid) (a : Int) (u1 u2 : BitVec 8) :
    gwritesByte GD.gdG w1 a u1 → gwritesByte GD.gdG w2 a u2 →
    gwix GD.gdG w1 < gwix GD.gdG w2 → gwix (retime GD.gdG L) w1 < gwix (retime GD.gdG L) w2 := by
  intro h1 h2 hlt
  have hmo : gmoLt (retime GD.gdG L) w1 w2 :=
    stepRww GD L hcons hlin w1 w2 (Or.inr (Or.inr (Or.inl ⟨a, u1, u2, h1, h2, hlt⟩)))
  exact (gwixGposLt (retime GD.gdG L) w1 w2 (linwNodup GD L hcons hlin)
    ((linwWelem GD L hcons hlin w1).2
      (gwritesByteInGwrites GD.gdG w1 a u1 (linwWf GD L hcons hlin) h1))
    ((linwWelem GD L hcons hlin w2).2
      (gwritesByteInGwrites GD.gdG w2 a u2 (linwWf GD L hcons hlin) h2))).2 hmo.2.2

theorem linwCoInv (w1 w2 : Geid) (a : Int) (u1 u2 : BitVec 8) :
    gwritesByte GD.gdG w1 a u1 → gwritesByte GD.gdG w2 a u2 →
    gwix (retime GD.gdG L) w1 < gwix (retime GD.gdG L) w2 → gwix GD.gdG w1 < gwix GD.gdG w2 := by
  intro h1 h2 hlt
  have hin1 := gwritesByteInGwrites GD.gdG w1 a u1 (linwWf GD L hcons hlin) h1
  have hin2 := gwritesByteInGwrites GD.gdG w2 a u2 (linwWf GD L hcons hlin) h2
  rcases Nat.lt_trichotomy (gwix GD.gdG w1) (gwix GD.gdG w2) with h | h | h
  · exact h
  · exfalso
    have := gwixInj GD.gdG w1 w2 (linwWf GD L hcons hlin).1 hin1 hin2 h
    subst this
    omega
  · exfalso
    have := linwCoFwd GD L hcons hlin w2 w1 a u2 u1 h2 h1 h
    omega

/-! ## 3.4 The axioms of the re-timed graph -/

theorem linwGwf : gwf (retime GD.gdG L) := by
  obtain ⟨_, hmem, hsh⟩ := linwWf GD L hcons hlin
  have hperm := linwPerm GD L hcons hlin
  have hrows := linwRows GD L hcons hlin
  refine ⟨linwNodup GD L hcons hlin, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      exact (rowsRelGmem _ GD.gdG _ e hrows).2
        ((hmem e).1 ((permElemOf L GD.gdG.gxGmo e hperm).1 he))
    · intro he
      exact (permElemOf L GD.gdG.gxGmo e hperm).2
        ((hmem e).2 ((rowsRelGmem _ GD.gdG _ e hrows).1 he))
  · intro i p k l hp hk
    rw [show (retime GD.gdG L).gxProg
        = GD.gdG.gxProg.map (fun row : List Lbl => row.map (lblRen (tren GD.gdG L))) from rfl,
      List.getElem?_map] at hp
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hp
    rw [List.getElem?_map] at hk
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hk
    exact WeakRvwmoTopo.lblRenShape _ l0 (hsh i r k l0 hr hl0)

theorem linwGppo : gppoGmo (retime GD.gdG L) := by
  intro e1 e2 hppo'
  exact stepRww GD L hcons hlin e1 e2 (Or.inr (Or.inr (Or.inr (Or.inr
    ((rowsRelGppo _ GD.gdG _ e1 e2 (linwRows GD L hcons hlin)).1 hppo')))))

/-- THE REPLACEMENT FOR `linGrule14`: the `gpow` arm is narrowed to `gpoww`, and what it
delivers is `gwrowGmo` instead of rule 14. -/
theorem linwGwrow : gwrowGmo (retime GD.gdG L) := by
  intro x j k hjk hj' hk'
  have hrows := linwRows GD L hcons hlin
  have hj := (rowsRelGlblIs _ GD.gdG _ (x, j) lbIsW hrows (lblRenIsW _)).1 hj'
  have hk := (rowsRelGlblIs _ GD.gdG _ (x, k) lbIsW hrows (lblRenIsW _)).1 hk'
  obtain ⟨lj, hlj, _⟩ := id hj
  obtain ⟨lk, hlk, _⟩ := id hk
  have hmo : gmoLt (retime GD.gdG L) (x, j) (x, k) :=
    stepRww GD L hcons hlin (x, j) (x, k)
      (Or.inl ⟨⟨rfl, hjk, by rw [hlj]; rfl, by rw [hlk]; rfl⟩, hj, hk⟩)
  have hgwf := linwGwf GD L hcons hlin
  have hinj' : (x, j) ∈ gwrites (retime GD.gdG L) := by
    obtain ⟨l, hl, hb⟩ := hj'
    exact gisWGwrites _ _ hgwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hb)
  have hink' : (x, k) ∈ gwrites (retime GD.gdG L) := by
    obtain ⟨l, hl, hb⟩ := hk'
    exact gisWGwrites _ _ hgwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hb)
  exact (gwixGposLt (retime GD.gdG L) (x, j) (x, k) (linwNodup GD L hcons hlin)
    hinj' hink').2 hmo.2.2

theorem linwGloadValue : gloadValue (retime GD.gdG L) := by
  intro e a t' v hrd'
  have hrows := linwRows GD L hcons hlin
  obtain ⟨t, rfl, hrd⟩ := rowsRelRdbInv _ GD.gdG _ e a t' v hrows hrd'
  have hwf := linwWf GD L hcons hlin
  obtain ⟨hsrc, hmax⟩ := linwLv GD L hcons hlin e a t v hrd
  have hinj := (linwWperm GD L hcons hlin).1
  refine ⟨?_, ?_⟩
  · cases hpt : tren GD.gdG L t with
    | zero =>
      have ht0 : t = 0 := hinj _ _ (by rw [hpt]; rfl)
      subst ht0
      exact hsrc
    | succ k =>
      cases t with
      | zero => rw [trenZero] at hpt; omega
      | succ t0 =>
        obtain ⟨w, hwat, hwb, _⟩ := hsrc
        refine ⟨w, ?_, (rowsRelWrb _ GD.gdG _ w a v hrows).2 hwb,
          Or.inl (stepRww GD L hcons hlin w e (Or.inr (Or.inl ⟨a, t0 + 1, v, hrd, hwat⟩)))⟩
        rw [← hpt, linwWat GD L hcons hlin]
        exact hwat
  · intro w' v' hwb' hvis'
    have hwb := (rowsRelWrb _ GD.gdG _ w' a v' hrows).1 hwb'
    have hw'in := gwritesByteInGwrites GD.gdG w' a v' hwf hwb
    have hne : w' ≠ e := by
      rintro rfl
      rcases hvis' with hm | hp
      · exact gmoLtIrrefl _ _ hm
      · exact gpoIrrefl _ _ hp
    -- the read is never gmo-before a visible write
    have hnv : ¬ gmoLt (retime GD.gdG L) e w' := by
      intro hew
      rcases hvis' with hm | hp
      · exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hew hm)
      · have hpo := (rowsRelGpo _ GD.gdG _ w' e hrows).1 hp
        have hwe : gmoLt (retime GD.gdG L) w' e :=
          stepRww GD L hcons hlin w' e (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hpo, a, Or.inl ⟨v', hwb⟩, Or.inr ⟨t, v, hrd⟩⟩)))))
        exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hew hwe)
    rcases Nat.lt_or_ge t (gwix GD.gdG w') with hgt | hle
    · exact absurd (stepRww GD L hcons hlin e w' (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fun h => hne h.symm, a, t, v, v', hrd, hwb, hgt⟩))))) hnv
    · by_cases heq : gwix GD.gdG w' = t
      · have hat' : gwriteAt GD.gdG t = some w' := by
          rw [← heq]; exact gwriteAtGwix GD.gdG w' hw'in
        have hgw : gwix (retime GD.gdG L) w' = tren GD.gdG L t := by
          rw [retimeGwix, trenAt GD.gdG L t w' hat']
        omega
      · have hlt : gwix GD.gdG w' < t := by omega
        cases t with
        | zero =>
          have := WeakRvwmoGraph.gwixPos GD.gdG w' hw'in
          omega
        | succ t0 =>
          obtain ⟨w, hwat, hwbw, _⟩ := hsrc
          have hwix : gwix GD.gdG w = t0 + 1 := (gwriteAtInv GD.gdG (t0 + 1) w hwf.1 hwat).2
          have hgw : gwix (retime GD.gdG L) w = tren GD.gdG L (t0 + 1) := by
            rw [retimeGwix, trenAt GD.gdG L (t0 + 1) w hwat]
          rw [← hgw]
          exact Nat.le_of_lt (linwCoFwd GD L hcons hlin w' w a v' v hwb hwbw (by omega))

theorem linwGatomicity : gatomicity (retime GD.gdG L) := by
  rintro e a t' v hrd' hw' w' v' hwb' ⟨_, hlt2⟩
  have hrows := linwRows GD L hcons hlin
  obtain ⟨t, hpt, hrd⟩ := rowsRelRdbInv _ GD.gdG _ e a t' v hrows hrd'
  have hwf := linwWf GD L hcons hlin
  have hw := (rowsRelGlblIs _ GD.gdG _ e lbIsW hrows (lblRenIsW _)).1 hw'
  have hwb := (rowsRelWrb _ GD.gdG _ w' a v' hrows).1 hwb'
  have hw'in := gwritesByteInGwrites GD.gdG w' a v' hwf hwb
  obtain ⟨ve, hwbe⟩ := greadByteWriteByte GD.gdG e a t v hwf (glblIsWGisW GD.gdG e hw) hrd
  -- the upper bound
  have hup : gwix GD.gdG w' < gwix GD.gdG e :=
    linwCoInv GD L hcons hlin w' e a v' ve hwb hwbe hlt2
  -- the lower bound
  have hlow : t < gwix GD.gdG w' := by
    cases t with
    | zero =>
      have := WeakRvwmoGraph.gwixPos GD.gdG w' hw'in
      omega
    | succ t0 =>
      obtain ⟨w, hwat, hwbw, _⟩ := (linwLv GD L hcons hlin e a (t0 + 1) v hrd).1
      have hwix : gwix GD.gdG w = t0 + 1 := (gwriteAtInv GD.gdG (t0 + 1) w hwf.1 hwat).2
      have hgw : gwix (retime GD.gdG L) w = t' := by
        rw [retimeGwix, hpt, trenAt GD.gdG L (t0 + 1) w hwat]
      rw [← hwix]
      exact linwCoInv GD L hcons hlin w w' a v v' hwbw hwb (by omega)
  exact linwAt GD L hcons hlin e a t v hrd hw w' v' hwb ⟨hlow, hup⟩

theorem linwGdepsWf : gdepsWf (retime GD.gdG L) GD.gdDeps := by
  intro rw hrw
  have hrows := linwRows GD L hcons hlin
  obtain ⟨h1, h2, h3, h4⟩ := hcons.2.1 rw hrw
  exact ⟨h1, h2, (rowsRelGlblIs _ GD.gdG _ rw.1 lbIsR hrows (lblRenIsR _)).2 h3,
    (rowsRelGlblIs _ GD.gdG _ rw.2 lbIsW hrows (lblRenIsW _)).2 h4⟩

theorem linwGdepsGmo : gdepsGmo (retime GD.gdG L) GD.gdDeps := by
  rintro ⟨r, w⟩ hrw
  exact WeakRvwmoPreNorm2.stepDep GD L hcons hlin r w hrw

/-- THE DELIVERABLE. -/
theorem topoLinearizesW :
    rvwmoMinusDepsConsistent ⟨retime GD.gdG L, GD.gdDeps⟩ ∧
    gwrowGmo (retime GD.gdG L) ∧
    rowsRel (tren GD.gdG L) GD.gdG (retime GD.gdG L) ∧
    wperm (tren GD.gdG L) GD.gdG (retime GD.gdG L) :=
  ⟨⟨⟨linwGwf GD L hcons hlin, linwGppo GD L hcons hlin, linwGloadValue GD L hcons hlin,
      linwGatomicity GD L hcons hlin⟩,
    linwGdepsWf GD L hcons hlin, linwGdepsGmo GD L hcons hlin⟩,
   linwGwrow GD L hcons hlin, linwRows GD L hcons hlin, linwWperm GD L hcons hlin⟩

end TopoLinw

/-! ## 3.1 EXISTENCE, and the deliverable -/

theorem topoExistsW (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (rwwD GD) x x) →
    ∃ L, linwExtD GD L := by
  intro hcons hacy
  have hnd : GD.gdG.gxGmo.Nodup := hcons.1.1.1
  obtain ⟨L, hL, hord⟩ := topoSortExists (rwwD GD) (fun x y => rwwDDec GD x y) hacy _ hnd
  refine ⟨L, hL, ?_⟩
  intro x y hR
  obtain ⟨hx, hy⟩ := rwwDMem GD x y hcons hR
  exact hord x y hx hy hR

/-- THE THEOREM THIS FILE IS FOR: `gwrowGmo` at a `gdEquiv` member from acyclicity of `rwwD`. -/
theorem normalizeWw3 (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (rwwD GD) x x) →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG := by
  intro hcons hacy
  obtain ⟨L, hlin⟩ := topoExistsW GD hcons hacy
  obtain ⟨hc', hrow, hr, hw⟩ := topoLinearizesW GD L hcons hlin
  exact ⟨⟨retime GD.gdG L, GD.gdDeps⟩, ⟨tren GD.gdG L, hr, hw, rfl, hc'⟩, hrow⟩

/-- … and `normalizeWw2` is now a corollary. -/
theorem normalizeWw2OfWw3 (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG :=
  fun hcons hacy => normalizeWw3 GD hcons (rwwDAcyclicOfRacyD GD hacy)

/-! # 4. SHARPNESS AND TRANSPORT -/

def rwwt (GD : Gdexec) (x y : Geid) : Prop :=
  (gpoww GD.gdG x y ∨ WeakRvwmoAcyc.grf GD.gdG x y ∨ gppo GD.gdG x y) ∨
  (x, y) ∈ GD.gdDeps

theorem rwwtRwwD (GD : Gdexec) (x y : Geid) : rwwt GD x y → rwwD GD x y := by
  rintro ((h | h | h) | h)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr h

theorem rwwtGdEquiv (GD GD' : Gdexec) (x y : Geid) :
    gdEquiv GD GD' → rwwt GD x y → rwwt GD' x y := by
  rintro ⟨π, hr, hw, hd, _⟩ ((⟨hpo, he, hf⟩ | h | h) | h)
  · exact Or.inl (Or.inl ⟨(rowsRelGpo π _ _ x y hr).2 hpo,
      (rowsRelGlblIs π _ _ x lbIsW hr (lblRenIsW π)).2 he,
      (rowsRelGlblIs π _ _ y lbIsW hr (lblRenIsW π)).2 hf⟩)
  · exact Or.inl (Or.inr (Or.inl ((grfRowsRel π _ _ x y hr hw).1 h)))
  · exact Or.inl (Or.inr (Or.inr ((rowsRelGppo π _ _ x y hr).2 h)))
  · exact Or.inr (by rw [hd]; exact h)

theorem rwwtCycleTransport (GD GD' : Gdexec) (x : Geid) :
    gdEquiv GD GD' → tc (rwwt GD) x x → tc (rwwt GD') x x :=
  fun heq htc => tcMono _ _ x x (fun a b => rwwtGdEquiv GD GD' a b heq) htc

/-! ## 4.1 `rwwt`-acyclicity is NECESSARY -/

theorem rwwtGmo (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gwrowGmo GD.gdG →
    rwwt GD x y → gmoLt GD.gdG x y := by
  intro hcons hrow hR
  obtain ⟨hc, _, hdmo⟩ := hcons
  have hwf := hc.1
  have hppo := hc.2.1
  have hnd : GD.gdG.gxGmo.Nodup := hwf.1
  rcases hR with ((⟨hpo, he, hf⟩ | h | h) | h)
  · obtain ⟨a, j⟩ := x
    obtain ⟨b, k⟩ := y
    obtain ⟨hag, hlt, _, _⟩ := hpo
    simp only at hag hlt
    subst hag
    have hinj : (a, j) ∈ gwrites GD.gdG := by
      obtain ⟨l, hl, hb⟩ := he
      exact gisWGwrites _ _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hb)
    have hink : (a, k) ∈ gwrites GD.gdG := by
      obtain ⟨l, hl, hb⟩ := hf
      exact gisWGwrites _ _ hwf (by rw [hl]; rfl) (by simp only [gisW, hl]; exact hb)
    exact ⟨gwfMemGmo _ _ hwf (WeakRvwmoGraph.glblIsWGmem _ _ he),
      gwfMemGmo _ _ hwf (WeakRvwmoGraph.glblIsWGmem _ _ hf),
      (gwixGposLt GD.gdG (a, j) (a, k) hnd hinj hink).1 (hrow a j k hlt he hf)⟩
  · exact WeakRvwmoAcyc.grfGmo _ x y hc h
  · exact hppo x y h
  · exact hdmo (x, y) h

theorem rwwtAcyclicOfGwrow (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → gwrowGmo GD.gdG →
    ∀ x, ¬ tc (rwwt GD) x x := by
  intro hcons hrow x htc
  have hstep : ∀ a b, tc (rwwt GD) a b → gmoLt GD.gdG a b := by
    intro a b h
    induction h with
    | single h => exact rwwtGmo GD _ _ hcons hrow h
    | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (rwwtGmo GD _ _ hcons hrow h)
  exact gmoLtIrrefl _ _ (hstep x x htc)

/-- THE NECESSITY, in orbit form: if ANY `gdEquiv` member has `gwrowGmo`, `GD`'s own
transporting fragment is acyclic. -/
theorem rwwtAcyclicNecessary (GD GD' : Gdexec) :
    gdEquiv GD GD' → gwrowGmo GD'.gdG → ∀ x, ¬ tc (rwwt GD) x x := by
  intro heq hrow x htc
  obtain ⟨_, _, _, _, hcons'⟩ := id heq
  exact rwwtAcyclicOfGwrow GD' hcons' hrow x (rwwtCycleTransport GD GD' x heq htc)

/-! ## 4.2 THE FULL CYCLE TRANSPORT, with its exact side condition -/

theorem racyDTransport (GD GD' : Gdexec) (π : Nat → Nat) :
    rowsRel π GD.gdG GD'.gdG → wperm π GD.gdG GD'.gdG →
    GD'.gdDeps = GD.gdDeps →
    (∀ w w', gco GD.gdG w w' → gco GD'.gdG w w') →
    (∀ r w', gfr GD.gdG r w' → gfr GD'.gdG r w') →
    ∀ x y, racyD GD x y → racyD GD' x y := by
  intro hr hw hd hco hfr x y h
  rcases h with (h | h | h | h | h) | h
  · exact Or.inl (Or.inl ((gpowRowsRel π _ _ x y hr).1 h))
  · exact Or.inl (Or.inr (Or.inl ((grfRowsRel π _ _ x y hr hw).1 h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (hco x y h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (hfr x y h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ((rowsRelGppo π _ _ x y hr).2 h)))))
  · exact Or.inr (by rw [hd]; exact h)

theorem cycleTransport (GD GD' : Gdexec) (π : Nat → Nat) (x : Geid) :
    rowsRel π GD.gdG GD'.gdG → wperm π GD.gdG GD'.gdG →
    GD'.gdDeps = GD.gdDeps →
    (∀ w w', gco GD.gdG w w' → gco GD'.gdG w w') →
    (∀ r w', gfr GD.gdG r w' → gfr GD'.gdG r w') →
    tc (racyD GD) x x → tc (racyD GD') x x :=
  fun hr hw hd hco hfr htc =>
    tcMono _ _ x x (fun a b => racyDTransport GD GD' π hr hw hd hco hfr a b) htc

/-- THE SUFFICIENT INSTANCE: a MONOTONE write-index renaming discharges both side conditions. -/
theorem cycleTransportMono (GD GD' : Gdexec) (π : Nat → Nat) (x : Geid) :
    gwf GD.gdG → gdEquiv GD GD' →
    rowsRel π GD.gdG GD'.gdG → wperm π GD.gdG GD'.gdG →
    (∀ t1 t2, t1 < t2 → π t1 < π t2) →
    tc (racyD GD) x x → tc (racyD GD') x x := by
  intro hwf heq hr hw hmono htc
  obtain ⟨_, _, _, hd, hcons'⟩ := heq
  have hnd' : GD'.gdG.gxGmo.Nodup := hcons'.1.1.1
  exact cycleTransport GD GD' π x hr hw hd
    (fun w w' => gcoRowsRelMono π _ _ w w' hwf hnd' hr hw hmono)
    (fun r w' => gfrRowsRelMono π _ _ r w' hwf hnd' hr hw hmono) htc

/-! # 5. WHERE `gwrowGmo` IS NEEDED, AND THE OBLIGATION THAT REMAINS -/

/-- THE ORBIT PULL-BACK IS NOT A ROUTE: it forces `gwrowGmo` at `GD` itself. -/
theorem wsupplyOrbitPullForcesGwrow (boot : Nat → Pexv6) (d0 : Efab) (N : Nat)
    (GD GD' : Gdexec) :
    wsupplyOrbitPull boot d0 N →
    gdEquiv GD GD' → (∃ W tm, wsupply boot d0 GD'.gdG W tm N) →
    gwrowGmo GD.gdG := by
  intro hpull heq hw
  obtain ⟨_, _, h, _⟩ := hpull GD GD' heq hw
  exact h

/-- THE ROUTE THAT IS LEFT: run the walk AT THE NORMALIZED MEMBER and transport the CYCLE. -/
def killAtMember (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) : Prop :=
  ∀ GD GD' : Gdexec,
    rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
    gdEquiv GD GD' → gwrowGmo GD'.gdG →
    (∀ cs, properCut GD.gdG cs → ∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    ∀ x, tc (racyD GD') x x → False

def orbitCycleTransport : Prop :=
  ∀ (GD GD' : Gdexec) (x : Geid),
    gdEquiv GD GD' → tc (racyD GD) x x → tc (racyD GD') x x

theorem cycleKillOfMember (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    killAtMember boot d0 im nh →
    orbitCycleTransport →
    (∀ GD : Gdexec,
       rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
       ∀ x, ¬ tc (rwwD GD) x x) →
    cycleKill boot d0 im nh := by
  intro hkill htr hacy GD hcons hq hhulls x hx
  obtain ⟨GD', heq, hrow⟩ := normalizeWw3 GD hcons (hacy GD hcons hq)
  exact hkill GD GD' hcons hq heq hrow hhulls x (htr GD GD' x heq hx)

/-- The `rwwt` fragment of the orbit transport IS free. -/
theorem orbitCycleTransportRwwt (GD GD' : Gdexec) (x : Geid) :
    gdEquiv GD GD' → tc (rwwt GD) x x → tc (racyD GD') x x :=
  fun heq htc =>
    tcMono _ _ x x (fun a b hR => rwwDRacyD GD' a b (rwwtRwwD GD' a b hR))
      (rwwtCycleTransport GD GD' x heq htc)

/-! ## 5.1 THE RESIDUE, NAMED -/

def wwResidue (GD : Gdexec) : Prop := ∀ x, ¬ tc (rwwD GD) x x

theorem wwResidueGivesGwrow (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → wwResidue GD →
    ∃ GD', gdEquiv GD GD' ∧ gwrowGmo GD'.gdG ∧
      GD'.gdDeps = GD.gdDeps ∧
      ∀ boot d0 im nh, gdexecQconf boot d0 im nh GD → gdexecQconf boot d0 im nh GD' := by
  intro hcons hres
  obtain ⟨GD', heq, hrow⟩ := normalizeWw3 GD hcons hres
  obtain ⟨π, hr, _, hd, _⟩ := id heq
  exact ⟨GD', heq, hrow, hd,
    fun boot d0 im nh hq => gdexecQconfRen π boot d0 im nh GD GD' hr hd hq⟩

/-- … and it is implied by `racyD`-acyclicity. -/
theorem wwResidueOfAcyclic (GD : Gdexec) :
    (∀ x, ¬ tc (racyD GD) x x) → wwResidue GD :=
  rwwDAcyclicOfRacyD GD

end Weak
