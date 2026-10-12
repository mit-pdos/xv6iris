/-
Weak: **THE CAUSAL HULL SLICE (route B, stage B1a')**.

Rocq: `iris/WeakRvwmoHull.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4d.1 F3 and §4d.4, "B1a' — CAUSAL HULLS"; generalizes B1a, `WeakRvwmoRestr`).

WHY B1a IS NOT ENOUGH.  `restrOk` ties the per-hart cut to a gmo PREFIX, and
`WeakRvwmoProbeRestr.erg` shows no cut vector can satisfy that at the frontier:
another hart's EARLY READ (a load gmo-below the violating write whose own
po-predecessor is gmo-above it) is consistent, is not a violation, and breaks the
tie.  The realizable region is not the prefix — it is the CAUSAL HULL.

THE OBJECT.  A hull is a per-hart cut vector `cs` (hart `i` keeps its first
`cs[i]?` row events, so po-closure is BY CONSTRUCTION — B1a's `gcut`) that is
RF-CLOSED: every kept read's named source is kept (`hullOk`).  There is NO gmo
cut: the hull's gmo is `G.gxGmo.filter (gcut cs)`, a SUBSEQUENCE.  Hence the
hull's writes are a subsequence of `gwrites G` and write indices RENUMBER, and
the file factors as

    G  ---- gxCut ---->  gxCut G cs  ---- lblRen ---->  gxHull G cs

the CUT (B1a's row-cutting shape, with the filtered gmo) followed by the
RENAMING `hren G cs` of every read's `ts` entries.  The cut's label layer is
B1a's `gxr*` family at `n := 0` (BY CONVERSION: those lemmas read `gxProg`
only); the renaming layer is `WeakRvwmoNorm`'s `rowsRel` with `WeakRvwmoAcyc`'s
transport lemmas.  What is new is the RENUMBERING ARITHMETIC: `filter` preserves
relative order (`sortedPosIff`), so gmo positions and write indices restrict
order-isomorphically, and `hren` is "the index of `gwriteAt G t` among the
hull's writes".

WHAT IS PROVED: the `gxc*`/`gxh*` bookkeeping, `hullConsistent`, `hullRule14`,
`hullDepsConsistent`, the composition `hullLinearizes`, the pure row
correspondence `hullRowsRel`, the full-cut identity (`hullOkFull`,
`gxHullFull`), and NON-VACUITY at `erg`: the hull `[1, 0]` IS rf-closed and
violation-free (`ergHullLinearizes`, `ergHullBeatsRestr`).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  Duplicated Rocq
   names (protocol rule) are FILE-QUALIFIED: `WeakRvwmoHull.filterAll`,
   `WeakRvwmoHull.lblRenShape`.  Uses of duplicated names refer to the imported
   files' qualified names (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`,
   `WeakRvwmoGraph.gwritesByteGisW`, `WeakRvwmoLin.gmsg`, `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `WeakRvwmoRestr` deviation 2 (`StronglySorted` ↦
   `List.Pairwise`, `is_Some o` ↦ `o.isSome = true`, `Decision` filters ↦ `Bool`
   filters).  `filterComm` is stated for Boolean predicates, the shim's `filter`
   convention.
3. `hullRule14`: `gviolGrule14` (Lean) takes `gwf G`, so the hull's consistency
   is projected to its `gwf` component — same statement (as `restrictRule14`).

**Name map** (Rocq → Lean): `filter_comm` ↦ `filterComm`; `filter_all` ↦
`WeakRvwmoHull.filterAll`; `sorted_pos_iff` ↦ `sortedPosIff`;
`gmo_gpos_sorted` ↦ `gmoGposSorted`; `gwrites_gwix_sorted` ↦
`gwritesGwixSorted`; `lbl_ren_shape` ↦ `WeakRvwmoHull.lblRenShape`;
`gload_src_elim` ↦ `gloadSrcElim`; `gload_src_intro` ↦ `gloadSrcIntro`;
`gx_cut` ↦ `gxCut`; `gxc_gmo` ↦ `gxcGmo`; `gxc_img` ↦ `gxcImg`;
`gxc_prog_lookup` ↦ `gxcProgLookup`; `gxc_row` ↦ `gxcRow`; `gxc_lbl` ↦
`gxcLbl`; `gxc_lbl_in` ↦ `gxcLblIn`; `gxc_glbl_is` ↦ `gxcGlblIs`; `gxc_gmem`
↦ `gxcGmem`; `gxc_gis_w` ↦ `gxcGisW`; `gxc_gpo` ↦ `gxcGpo`; `gxc_wrb` ↦
`gxcWrb`; `gxc_rdb` ↦ `gxcRdb`; `gxc_gmsg` ↦ `gxcGmsg`; `gxc_gppo` ↦
`gxcGppo`; `gxc_gppo_cut` ↦ `gxcGppoCut`; `gxc_gmo_elem` ↦ `gxcGmoElem`;
`gxc_nodup` ↦ `gxcNodup`; `gxc_gmo_sorted` ↦ `gxcGmoSorted`; `gxc_gmo_lt` ↦
`gxcGmoLt`; `gxc_gwrites` ↦ `gxcGwrites`; `gxc_gwrites_elem` ↦
`gxcGwritesElem`; `gxc_gwrites_sorted` ↦ `gxcGwritesSorted`; `gxc_gwix_lt` ↦
`gxcGwixLt`; `gxc_gwix_le` ↦ `gxcGwixLe`; `hren`; `hren_zero` ↦ `hrenZero`;
`gx_hull` ↦ `gxHull`; `hull_rows_rel` ↦ `hullRowsRel`; `gxh_gmo` ↦ `gxhGmo`;
`gxh_gpos` ↦ `gxhGpos`; `gxh_img` ↦ `gxhImg`; `gxh_prog_lookup` ↦
`gxhProgLookup`; `gxh_row` ↦ `gxhRow`; `gxh_lbl` ↦ `gxhLbl`; `gxh_glbl_is` ↦
`gxhGlblIs`; `gxh_gmem` ↦ `gxhGmem`; `gxh_gis_w` ↦ `gxhGisW`; `gxh_gpo` ↦
`gxhGpo`; `gxh_wrb` ↦ `gxhWrb`; `gxh_rdb_in` ↦ `gxhRdbIn`; `gxh_rdb_inv` ↦
`gxhRdbInv`; `gxh_gppo` ↦ `gxhGppo`; `gxh_gppo_cut` ↦ `gxhGppoCut`;
`gxh_gmsg` ↦ `gxhGmsg`; `gxh_gmo_lt` ↦ `gxhGmoLt`; `gxh_gwrites` ↦
`gxhGwrites`; `gxh_gwrites_G` ↦ `gxhGwritesG`; `gxh_gwrites_elem` ↦
`gxhGwritesElem`; `gxh_gwix` ↦ `gxhGwix`; `gxh_gwrite_at` ↦ `gxhGwriteAt`;
`gxh_gwix_lt` ↦ `gxhGwixLt`; `gxh_gwix_le` ↦ `gxhGwixLe`; `hren_wix` ↦
`hrenWix`; `hren_gwix` ↦ `hrenGwix`; `hren_wat` ↦ `hrenWat`; `hren_pos` ↦
`hrenPos`; `hren_zero_inv` ↦ `hrenZeroInv`; `hull_ok` ↦ `hullOk`;
`hull_ok_len` ↦ `hullOkLen`; `hull_ok_rf` ↦ `hullOkRf`; `hull_ok_grf` ↦
`hullOkGrf`; `hull_consistent` ↦ `hullConsistent`; `gviol_hull` ↦
`gviolHull`; `hull_rule14` ↦ `hullRule14`; `gd_hull` ↦ `gdHull`;
`gd_hull_deps` ↦ `gdHullDeps`; `hull_deps_consistent` ↦ `hullDepsConsistent`;
`omap_gmsg_hull` ↦ `omapGmsgHull`; `hull_linearizes` ↦ `hullLinearizes`;
`gfull_cut` ↦ `gfullCut`; `gfull_filter_gmo` ↦ `gfullFilterGmo`;
`gfull_filter_gwrites` ↦ `gfullFilterGwrites`; `hren_full` ↦ `hrenFull`;
`hull_ok_full` ↦ `hullOkFull`; `zip_with_take_full` ↦ `zipWithTakeFull`;
`gx_hull_full` ↦ `gxHullFull`; `ecs`; `erg_cut` ↦ `ergCut`; `erg_hull_ok` ↦
`ergHullOk`; `erg_hull_viol_free` ↦ `ergHullViolFree`; `ergd`;
`ergd_consistent` ↦ `ergdConsistent`; `erg_hull_linearizes` ↦
`ergHullLinearizes`; `erg_hull_beats_restr` ↦ `ergHullBeatsRestr`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `WeakRvwmoHull.lblRenShape`'s `LIo` arms are `True` (`gwf`'s flip).
-/
import Weak.WeakRvwmoRestr
import Weak.WeakRvwmoAcyc
import Weak.WeakRvwmoProbeRestr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 1. THE GENERIC KIT -/

/-- Filters commute. -/
theorem filterComm {A : Type _} (p q : A → Bool) (l : List A) :
    (l.filter q).filter p = (l.filter p).filter q := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro x _
  exact Bool.and_comm _ _

/-- A filter that drops nothing is the identity. -/
theorem WeakRvwmoHull.filterAll {A : Type _} (p : A → Bool) (l : List A) :
    (∀ x, x ∈ l → p x = true) → l.filter p = l :=
  fun h => List.filter_eq_self.2 h

/-- THE ORDER-PRESERVATION ENGINE.  In a list sorted strictly by a numeric key,
LIST POSITION and KEY order agree. -/
theorem sortedPosIff {A : Type _} (f : A → Nat) (l : List A) (i1 i2 : Nat) (x1 x2 : A) :
    List.Pairwise (fun x y => f x < f y) l → l[i1]? = some x1 → l[i2]? = some x2 →
    (i1 < i2 ↔ f x1 < f x2) := by
  intro hss h1 h2
  constructor
  · intro hlt
    exact stronglySortedLookupElim _ _ i1 i2 x1 x2 hss h1 h2 hlt
  · intro hlt
    by_cases hi : i1 < i2
    · exact hi
    by_cases heq : i1 = i2
    · subst heq
      rw [h1, Option.some.injEq] at h2
      subst h2
      exact absurd hlt (Nat.lt_irrefl _)
    have hr : f x2 < f x1 := stronglySortedLookupElim _ _ i2 i1 x2 x1 hss h2 h1 (by omega)
    omega

/-- `gxGmo` is sorted by `gpos`; `gwrites` is sorted by `gwix`. -/
theorem gmoGposSorted (G : Gexec) :
    G.gxGmo.Nodup → List.Pairwise (fun x y => gpos G x < gpos G y) G.gxGmo := by
  intro hnd
  apply stronglySortedLookupIntro
  intro i j x y hi hj hlt
  show gpos G x < gpos G y
  rw [gposOfLookup G i x hnd hi, gposOfLookup G j y hnd hj]
  exact hlt

theorem gwritesGwixSorted (G : Gexec) :
    G.gxGmo.Nodup → List.Pairwise (fun x y => gwix G x < gwix G y) (gwrites G) := by
  intro hnd
  apply stronglySortedLookupIntro
  intro i j x y hi hj hlt
  show gwix G x < gwix G y
  rw [gwixOfLookup G i x hnd hi, gwixOfLookup G j y hnd hj]
  omega

/-- `lblRen` preserves `gwf`'s shape clause. -/
theorem WeakRvwmoHull.lblRenShape (π : Nat → Nat) (l : Lbl) :
    (match l with
     | LLoad _ _ ts vs => vs.length = ts.length
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
     | LIo .. => True) →
    (match lblRen π l with
     | LLoad _ _ ts vs => vs.length = ts.length
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
     | LIo .. => True) := by
  intro h
  cases l <;> simp only [lblRen, List.length_map] <;> exact h

/-- The two shapes of `gloadValue`'s ∃-half. -/
theorem gloadSrcElim (G : Gexec) (t : Nat) (a : Int) (v : BitVec 8) (e : Geid) :
    0 < t →
    (match t with
     | 0 => G.gxImg a = some v
     | _ + 1 => ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e) →
    ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e := by
  intro ht h
  cases t with
  | zero => exact absurd ht (Nat.lt_irrefl _)
  | succ i => exact h

theorem gloadSrcIntro (G : Gexec) (t : Nat) (a : Int) (v : BitVec 8) (e : Geid) :
    0 < t →
    (∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e) →
    (match t with
     | 0 => G.gxImg a = some v
     | _ + 1 => ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e) := by
  intro ht h
  cases t with
  | zero => exact absurd ht (Nat.lt_irrefl _)
  | succ i => exact h

/-! # 2. THE CUT: B1a's rows, a FILTERED gmo -/

def gxCut (G : Gexec) (cs : List Nat) : Gexec :=
  ⟨G.gxImg, List.zipWith List.take cs G.gxProg, G.gxGmo.filter (gcut cs)⟩

theorem gxcGmo (G : Gexec) (cs : List Nat) : (gxCut G cs).gxGmo = G.gxGmo.filter (gcut cs) :=
  rfl

theorem gxcImg (G : Gexec) (cs : List Nat) : (gxCut G cs).gxImg = G.gxImg := rfl

/-! ## 2.1 The label layer, BY CONVERSION from B1a -/

theorem gxcProgLookup (G : Gexec) (cs : List Nat) (i : Nat) :
    (gxCut G cs).gxProg[i]? =
      (cs[i]?).bind (fun c => (G.gxProg[i]?).bind (fun p => some (List.take c p))) :=
  gxrProgLookup G cs 0 i

theorem gxcRow (G : Gexec) (cs : List Nat) (i : Nat) :
    ((gxCut G cs).gxProg[i]?).getD [] =
      List.take ((cs[i]?).getD 0) ((G.gxProg[i]?).getD []) :=
  gxrRow G cs 0 i

theorem gxcLbl (G : Gexec) (cs : List Nat) (e : Geid) :
    gxLbl (gxCut G cs) e = if gcut cs e then gxLbl G e else none :=
  gxrLbl G cs 0 e

theorem gxcLblIn (G : Gexec) (cs : List Nat) (e : Geid) :
    gcut cs e = true → gxLbl (gxCut G cs) e = gxLbl G e :=
  gxrLblIn G cs 0 e

theorem gxcGlblIs (G : Gexec) (cs : List Nat) (e : Geid) (P : Lbl → Bool) :
    glblIs (gxCut G cs) e P ↔ gcut cs e = true ∧ glblIs G e P :=
  gxrGlblIs G cs 0 e P

theorem gxcGmem (G : Gexec) (cs : List Nat) (e : Geid) :
    gmem (gxCut G cs) e ↔ gcut cs e = true ∧ gmem G e :=
  gxrGmem G cs 0 e

theorem gxcGisW (G : Gexec) (cs : List Nat) (e : Geid) :
    gisW (gxCut G cs) e = if gcut cs e then gisW G e else false :=
  gxrGisW G cs 0 e

theorem gxcGpo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo (gxCut G cs) e1 e2 ↔ WeakRvwmoGraph.gpo G e1 e2 ∧ gcut cs e2 = true :=
  gxrGpo G cs 0 e1 e2

theorem gxcWrb (G : Gexec) (cs : List Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (gxCut G cs) e a v ↔ gcut cs e = true ∧ gwritesByte G e a v :=
  gxrWrb G cs 0 e a v

theorem gxcRdb (G : Gexec) (cs : List Nat) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte (gxCut G cs) e a t v ↔ gcut cs e = true ∧ greadsByte G e a t v :=
  gxrRdb G cs 0 e a t v

theorem gxcGmsg (G : Gexec) (cs : List Nat) (e : Geid) :
    gcut cs e = true → WeakRvwmoLin.gmsg (gxCut G cs) e = WeakRvwmoLin.gmsg G e :=
  gxrGmsg G cs 0 e

theorem gxcGppo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo (gxCut G cs) e1 e2 → gppo G e1 e2 :=
  gxrGppo G cs 0 e1 e2

theorem gxcGppoCut (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo (gxCut G cs) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true :=
  gxrGppoCut G cs 0 e1 e2

/-! ## 2.2 The gmo layer: a SUBSEQUENCE, order-isomorphically -/

theorem gxcGmoElem (G : Gexec) (cs : List Nat) (e : Geid) :
    e ∈ (gxCut G cs).gxGmo ↔ gcut cs e = true ∧ e ∈ G.gxGmo :=
  elem_of_list_filter

theorem gxcNodup (G : Gexec) (cs : List Nat) : G.gxGmo.Nodup → (gxCut G cs).gxGmo.Nodup :=
  fun hnd => NoDup_filter hnd

theorem gxcGmoSorted (G : Gexec) (cs : List Nat) :
    G.gxGmo.Nodup →
    List.Pairwise (fun x y => gpos G x < gpos G y) (gxCut G cs).gxGmo :=
  fun hnd => stronglySortedFilter _ _ _ (gmoGposSorted G hnd)

theorem gxcGmoLt (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    G.gxGmo.Nodup →
    (gmoLt (gxCut G cs) e1 e2 ↔ gcut cs e1 = true ∧ gcut cs e2 = true ∧ gmoLt G e1 e2) := by
  intro hnd
  have hss := gxcGmoSorted G cs hnd
  constructor
  · rintro ⟨h1, h2, hlt⟩
    obtain ⟨hc1, hm1⟩ := (gxcGmoElem G cs e1).1 h1
    obtain ⟨hc2, hm2⟩ := (gxcGmoElem G cs e2).1 h2
    obtain ⟨i1, hi1, E1⟩ := gposLookup (gxCut G cs) e1 h1
    obtain ⟨i2, hi2, E2⟩ := gposLookup (gxCut G cs) e2 h2
    rw [E1, E2] at hlt
    exact ⟨hc1, hc2, hm1, hm2, (sortedPosIff (gpos G) _ i1 i2 e1 e2 hss hi1 hi2).1 hlt⟩
  · rintro ⟨hc1, hc2, hm1, hm2, hlt⟩
    have h1 := (gxcGmoElem G cs e1).2 ⟨hc1, hm1⟩
    have h2 := (gxcGmoElem G cs e2).2 ⟨hc2, hm2⟩
    obtain ⟨i1, hi1, E1⟩ := gposLookup (gxCut G cs) e1 h1
    obtain ⟨i2, hi2, E2⟩ := gposLookup (gxCut G cs) e2 h2
    refine ⟨h1, h2, ?_⟩
    rw [E1, E2]
    exact (sortedPosIff (gpos G) _ i1 i2 e1 e2 hss hi1 hi2).2 hlt

/-! ## 2.3 The write sub-order: `(gwrites G).filter (gcut cs)` -/

theorem gxcGwrites (G : Gexec) (cs : List Nat) :
    gwrites (gxCut G cs) = (gwrites G).filter (gcut cs) := by
  show (G.gxGmo.filter (gcut cs)).filter (gisW (gxCut G cs)) =
    (G.gxGmo.filter (gisW G)).filter (gcut cs)
  refine Eq.trans (filterIffElem _ (gisW G) _ ?_) (filterComm _ _ _)
  intro e he
  obtain ⟨hc, _⟩ := elem_of_list_filter.1 he
  rw [gxcGisW, if_pos hc]

theorem gxcGwritesElem (G : Gexec) (cs : List Nat) (w : Geid) :
    w ∈ gwrites (gxCut G cs) ↔ gcut cs w = true ∧ w ∈ gwrites G := by
  rw [gxcGwrites]
  exact elem_of_list_filter

theorem gxcGwritesSorted (G : Gexec) (cs : List Nat) :
    G.gxGmo.Nodup →
    List.Pairwise (fun x y => gwix G x < gwix G y) (gwrites (gxCut G cs)) := by
  intro hnd
  rw [gxcGwrites]
  exact stronglySortedFilter _ _ _ (gwritesGwixSorted G hnd)

/-- THE RENUMBERING IS MONOTONE. -/
theorem gxcGwixLt (G : Gexec) (cs : List Nat) (w1 w2 : Geid) :
    G.gxGmo.Nodup →
    w1 ∈ gwrites (gxCut G cs) → w2 ∈ gwrites (gxCut G cs) →
    (gwix (gxCut G cs) w1 < gwix (gxCut G cs) w2 ↔ gwix G w1 < gwix G w2) := by
  intro hnd h1 h2
  obtain ⟨i1, hi1, E1⟩ := gwixLookup (gxCut G cs) w1 h1
  obtain ⟨i2, hi2, E2⟩ := gwixLookup (gxCut G cs) w2 h2
  rw [E1, E2]
  have hiff := sortedPosIff (gwix G) _ i1 i2 w1 w2 (gxcGwritesSorted G cs hnd) hi1 hi2
  constructor
  · intro h
    exact hiff.1 (by omega)
  · intro h
    have := hiff.2 h
    omega

theorem gxcGwixLe (G : Gexec) (cs : List Nat) (w1 w2 : Geid) :
    G.gxGmo.Nodup →
    w1 ∈ gwrites (gxCut G cs) → w2 ∈ gwrites (gxCut G cs) →
    gwix G w1 ≤ gwix G w2 →
    gwix (gxCut G cs) w1 ≤ gwix (gxCut G cs) w2 := by
  intro hnd h1 h2 hle
  by_cases heq : gwix G w1 = gwix G w2
  · have hw : w1 = w2 := gwixInj G w1 w2 hnd ((gxcGwritesElem G cs w1).1 h1).2
      ((gxcGwritesElem G cs w2).1 h2).2 heq
    subst hw
    exact Nat.le_refl _
  · have hlt : gwix G w1 < gwix G w2 := by omega
    have := (gxcGwixLt G cs w1 w2 hnd h1 h2).2 hlt
    omega

/-! # 3. THE RENAMING AND THE HULL -/

/-- `hren G cs t`: THE INDEX OF `gwriteAt G t` AMONG THE HULL'S WRITES (1-based,
`0` at `0`); off the hull the identity. -/
def hren (G : Gexec) (cs : List Nat) (t : Nat) : Nat :=
  match gwriteAt G t with
  | some w => if gcut cs w then gwix (gxCut G cs) w else t
  | none => t

theorem hrenZero (G : Gexec) (cs : List Nat) : hren G cs 0 = 0 := rfl

/-- THE OBJECT: the cut rows, with every kept label's `ts` entries renamed. -/
def gxHull (G : Gexec) (cs : List Nat) : Gexec :=
  ⟨G.gxImg,
   (List.zipWith List.take cs G.gxProg).map (fun row : List Lbl => row.map (lblRen (hren G cs))),
   G.gxGmo.filter (gcut cs)⟩

/-- THE FACTORIZATION: the hull's rows are the CUT rows renamed. -/
theorem hullRowsRel (G : Gexec) (cs : List Nat) : rowsRel (hren G cs) (gxCut G cs) (gxHull G cs) :=
  ⟨rfl, rfl, hrenZero G cs⟩

theorem gxhGmo (G : Gexec) (cs : List Nat) : (gxHull G cs).gxGmo = (gxCut G cs).gxGmo := rfl

theorem gxhGpos (G : Gexec) (cs : List Nat) (e : Geid) :
    gpos (gxHull G cs) e = gpos (gxCut G cs) e := rfl

theorem gxhImg (G : Gexec) (cs : List Nat) : (gxHull G cs).gxImg = G.gxImg := rfl

/-! ## 3.1 The label layer: the cut's, composed with the renaming -/

theorem gxhProgLookup (G : Gexec) (cs : List Nat) (i : Nat) :
    (gxHull G cs).gxProg[i]? =
      (cs[i]?).bind (fun c => (G.gxProg[i]?).bind
        (fun p => some ((List.take c p).map (lblRen (hren G cs))))) := by
  have hp : (gxHull G cs).gxProg =
      (gxCut G cs).gxProg.map (fun row : List Lbl => row.map (lblRen (hren G cs))) := rfl
  rw [hp, List.getElem?_map, gxcProgLookup]
  cases cs[i]? <;> cases G.gxProg[i]? <;> rfl

theorem gxhRow (G : Gexec) (cs : List Nat) (i : Nat) :
    ((gxHull G cs).gxProg[i]?).getD [] =
      (List.take ((cs[i]?).getD 0) ((G.gxProg[i]?).getD [])).map (lblRen (hren G cs)) := by
  rw [gxhProgLookup]
  cases cs[i]? <;> cases G.gxProg[i]? <;> simp

theorem gxhLbl (G : Gexec) (cs : List Nat) (e : Geid) :
    gxLbl (gxHull G cs) e =
      if gcut cs e then (gxLbl G e).map (lblRen (hren G cs)) else none := by
  rw [rowsRelLbl _ _ _ e (hullRowsRel G cs), gxcLbl]
  cases gcut cs e <;> rfl

theorem gxhGlblIs (G : Gexec) (cs : List Nat) (e : Geid) (P : Lbl → Bool) :
    (∀ π l, P (lblRen π l) = P l) →
    (glblIs (gxHull G cs) e P ↔ gcut cs e = true ∧ glblIs G e P) := by
  intro hP
  exact (rowsRelGlblIs _ _ _ e P (hullRowsRel G cs) (hP _)).trans (gxcGlblIs G cs e P)

theorem gxhGmem (G : Gexec) (cs : List Nat) (e : Geid) :
    gmem (gxHull G cs) e ↔ gcut cs e = true ∧ gmem G e :=
  (rowsRelGmem _ _ _ e (hullRowsRel G cs)).trans (gxcGmem G cs e)

theorem gxhGisW (G : Gexec) (cs : List Nat) (e : Geid) :
    gisW (gxHull G cs) e = if gcut cs e then gisW G e else false := by
  rw [rowsRelGisW _ _ _ e (hullRowsRel G cs)]
  exact gxcGisW G cs e

theorem gxhGpo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo (gxHull G cs) e1 e2 ↔ WeakRvwmoGraph.gpo G e1 e2 ∧ gcut cs e2 = true :=
  (rowsRelGpo _ _ _ e1 e2 (hullRowsRel G cs)).trans (gxcGpo G cs e1 e2)

theorem gxhWrb (G : Gexec) (cs : List Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (gxHull G cs) e a v ↔ gcut cs e = true ∧ gwritesByte G e a v :=
  (rowsRelWrb _ _ _ e a v (hullRowsRel G cs)).trans (gxcWrb G cs e a v)

/-- THE RENAMING'S PAYLOAD: a kept read reads the SAME byte and value at the
RENAMED index. -/
theorem gxhRdbIn (G : Gexec) (cs : List Nat) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gcut cs r = true → greadsByte G r a t v →
    greadsByte (gxHull G cs) r a (hren G cs t) v := by
  intro hc hrd
  exact rowsRelRdb _ _ _ r a t v (hullRowsRel G cs) ((gxcRdb G cs r a t v).2 ⟨hc, hrd⟩)

theorem gxhRdbInv (G : Gexec) (cs : List Nat) (r : Geid) (a : Int) (t' : Nat) (v : BitVec 8) :
    greadsByte (gxHull G cs) r a t' v →
    gcut cs r = true ∧ ∃ t, greadsByte G r a t v ∧ t' = hren G cs t := by
  intro h
  obtain ⟨t, rfl, hrd⟩ := rowsRelRdbInv _ _ _ r a t' v (hullRowsRel G cs) h
  obtain ⟨hc, hrd⟩ := (gxcRdb G cs r a t v).1 hrd
  exact ⟨hc, t, hrd, rfl⟩

theorem gxhGppo (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo (gxHull G cs) e1 e2 → gppo G e1 e2 :=
  fun h => gxcGppo G cs e1 e2 ((rowsRelGppo _ _ _ e1 e2 (hullRowsRel G cs)).1 h)

theorem gxhGppoCut (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    gppo (gxHull G cs) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true :=
  fun h => gxcGppoCut G cs e1 e2 ((rowsRelGppo _ _ _ e1 e2 (hullRowsRel G cs)).1 h)

theorem gxhGmsg (G : Gexec) (cs : List Nat) (e : Geid) :
    gcut cs e = true → WeakRvwmoLin.gmsg (gxHull G cs) e = WeakRvwmoLin.gmsg G e := by
  intro hc
  unfold WeakRvwmoLin.gmsg
  rw [rowsRelLbl _ _ _ e (hullRowsRel G cs), gxcLblIn G cs e hc]
  cases gxLbl G e with
  | none => rfl
  | some l => simp [lblRenWr, lblRenCls]

/-! ## 3.2 The gmo and write-index layers, in terms of `G` -/

theorem gxhGmoLt (G : Gexec) (cs : List Nat) (e1 e2 : Geid) :
    G.gxGmo.Nodup →
    (gmoLt (gxHull G cs) e1 e2 ↔ gcut cs e1 = true ∧ gcut cs e2 = true ∧ gmoLt G e1 e2) :=
  gxcGmoLt G cs e1 e2

theorem gxhGwrites (G : Gexec) (cs : List Nat) : gwrites (gxHull G cs) = gwrites (gxCut G cs) := by
  unfold gwrites
  rw [gxhGmo]
  apply filterIffElem
  intro e _
  rw [rowsRelGisW _ _ _ e (hullRowsRel G cs)]

theorem gxhGwritesG (G : Gexec) (cs : List Nat) :
    gwrites (gxHull G cs) = (gwrites G).filter (gcut cs) := by
  rw [gxhGwrites, gxcGwrites]

theorem gxhGwritesElem (G : Gexec) (cs : List Nat) (w : Geid) :
    w ∈ gwrites (gxHull G cs) ↔ gcut cs w = true ∧ w ∈ gwrites G := by
  rw [gxhGwrites]
  exact gxcGwritesElem G cs w

theorem gxhGwix (G : Gexec) (cs : List Nat) (w : Geid) :
    gwix (gxHull G cs) w = gwix (gxCut G cs) w := by
  unfold gwix
  rw [gxhGwrites]

theorem gxhGwriteAt (G : Gexec) (cs : List Nat) (t : Nat) :
    gwriteAt (gxHull G cs) t = gwriteAt (gxCut G cs) t := by
  cases t with
  | zero => rfl
  | succ i =>
    show (gwrites (gxHull G cs))[i]? = (gwrites (gxCut G cs))[i]?
    rw [gxhGwrites]

theorem gxhGwixLt (G : Gexec) (cs : List Nat) (w1 w2 : Geid) :
    G.gxGmo.Nodup →
    w1 ∈ gwrites (gxHull G cs) → w2 ∈ gwrites (gxHull G cs) →
    (gwix (gxHull G cs) w1 < gwix (gxHull G cs) w2 ↔ gwix G w1 < gwix G w2) := by
  intro hnd h1 h2
  rw [gxhGwix, gxhGwix]
  rw [gxhGwrites] at h1 h2
  exact gxcGwixLt G cs w1 w2 hnd h1 h2

theorem gxhGwixLe (G : Gexec) (cs : List Nat) (w1 w2 : Geid) :
    G.gxGmo.Nodup →
    w1 ∈ gwrites (gxHull G cs) → w2 ∈ gwrites (gxHull G cs) →
    gwix G w1 ≤ gwix G w2 →
    gwix (gxHull G cs) w1 ≤ gwix (gxHull G cs) w2 := by
  intro hnd h1 h2
  rw [gxhGwix, gxhGwix]
  rw [gxhGwrites] at h1 h2
  exact gxcGwixLe G cs w1 w2 hnd h1 h2

/-! ## 3.3 `hren`, spelled through the hull -/

/-- THE DEFINING EQUATION. -/
theorem hrenWix (G : Gexec) (cs : List Nat) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → gcut cs w = true →
    hren G cs t = gwix (gxHull G cs) w := by
  intro ht hc
  simp only [hren, ht, hc, if_true, gxhGwix]

theorem hrenGwix (G : Gexec) (cs : List Nat) (w : Geid) :
    G.gxGmo.Nodup → w ∈ gwrites G → gcut cs w = true →
    hren G cs (gwix G w) = gwix (gxHull G cs) w :=
  fun _ hw hc => hrenWix G cs _ w (gwriteAtGwix G w hw) hc

theorem hrenWat (G : Gexec) (cs : List Nat) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → gcut cs w = true →
    gwriteAt (gxHull G cs) (hren G cs t) = some w := by
  intro ht hc
  rw [hrenWix G cs t w ht hc]
  exact gwriteAtGwix _ w ((gxhGwritesElem G cs w).2 ⟨hc, gwriteAtGwrites G t w ht⟩)

theorem hrenPos (G : Gexec) (cs : List Nat) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → gcut cs w = true → 0 < hren G cs t := by
  intro ht hc
  rw [hrenWix G cs t w ht hc]
  exact WeakRvwmoGraph.gwixPos _ w ((gxhGwritesElem G cs w).2 ⟨hc, gwriteAtGwrites G t w ht⟩)

/-- `hren` REFLECTS `0`. -/
theorem hrenZeroInv (G : Gexec) (cs : List Nat) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → gcut cs w = true → hren G cs t ≠ 0 := by
  intro ht hc
  have := hrenPos G cs t w ht hc
  omega

/-! # 4. THE HULL CONDITION AND CONSISTENCY -/

/-- `hullOk`: po-closure is free (a per-hart cut is a prefix), so only
RF-CLOSURE is a clause. -/
def hullOk (G : Gexec) (cs : List Nat) : Prop :=
  cs.length = G.gxProg.length ∧
  (∀ (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (w : Geid),
    gcut cs r = true → greadsByte G r a t v → gwriteAt G t = some w → gcut cs w = true)

theorem hullOkLen (G : Gexec) (cs : List Nat) : hullOk G cs → cs.length = G.gxProg.length :=
  fun h => h.1

theorem hullOkRf (G : Gexec) (cs : List Nat) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (w : Geid) :
    hullOk G cs → gcut cs r = true → greadsByte G r a t v →
    gwriteAt G t = some w → gcut cs w = true :=
  fun h hc hrd hw => h.2 r a t v w hc hrd hw

/-- The same clause in `WeakRvwmoAcyc`'s vocabulary: the cut is closed under
`grf`. -/
theorem hullOkGrf (G : Gexec) (cs : List Nat) (w r : Geid) :
    hullOk G cs → gcut cs r = true → WeakRvwmoAcyc.grf G w r → gcut cs w = true := by
  rintro hok hc ⟨a, t, v, hrd, hat⟩
  exact hullOkRf G cs r a t v w hok hc hrd hat

theorem hullConsistent (G : Gexec) (cs : List Nat) :
    rvwmoMinusConsistent G → hullOk G cs → rvwmoMinusConsistent (gxHull G cs) := by
  intro hcons hok
  have hwf := hcons.1
  have hppo := hcons.2.1
  have hlv := hcons.2.2.1
  have hat := hcons.2.2.2
  have hnd := hwf.1
  have hmem := hwf.2.1
  have hsh := hwf.2.2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- gwf: nodup
    exact gxcNodup G cs hnd
  · -- gwf: membership
    intro e
    rw [gxhGmo, gxcGmoElem, gxhGmem]
    constructor
    · rintro ⟨hc, he⟩
      exact ⟨hc, (hmem e).1 he⟩
    · rintro ⟨hc, he⟩
      exact ⟨hc, (hmem e).2 he⟩
  · -- gwf: shapes
    intro i p' k l' hp' hk'
    rw [gxhProgLookup] at hp'
    cases hc : cs[i]? with
    | none => rw [hc] at hp'; simp at hp'
    | some c =>
      cases hp : G.gxProg[i]? with
      | none => rw [hc, hp] at hp'; simp at hp'
      | some p =>
        rw [hc, hp] at hp'
        simp at hp'
        subst hp'
        obtain ⟨hk'', _⟩ := lookup_take_Some.1 hk'
        rw [List.getElem?_map] at hk''
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hk''
        exact WeakRvwmoHull.lblRenShape _ l (hsh i p k l hp hl)
  · -- ppo⁻ ⊆ gmo
    intro e1 e2 hppo'
    obtain ⟨hc1, hc2⟩ := gxhGppoCut G cs e1 e2 hppo'
    have hmo := hppo e1 e2 (gxhGppo G cs e1 e2 hppo')
    exact (gxhGmoLt G cs e1 e2 hnd).2 ⟨hc1, hc2, hmo⟩
  · -- load value
    intro e a t' v hrd'
    obtain ⟨hce, t, hrd, rfl⟩ := gxhRdbInv G cs e a t' v hrd'
    obtain ⟨hsrc, hmax⟩ := hlv e a t v hrd
    -- the source facts, once: available to BOTH halves
    have hsrcw : 0 < t → ∃ w, gwriteAt G t = some w ∧ gcut cs w = true ∧
        gwritesByte G w a v ∧ gvisible G w e ∧
        w ∈ gwrites (gxHull G cs) ∧ gwix G w = t := by
      intro ht
      obtain ⟨w, hwat, hwb, hvis⟩ := gloadSrcElim G t a v e ht hsrc
      have hcw := hullOkRf G cs e a t v w hok hce hrd hwat
      obtain ⟨hwg, hwix⟩ := gwriteAtInv G t w hnd hwat
      exact ⟨w, hwat, hcw, hwb, hvis, (gxhGwritesElem G cs w).2 ⟨hcw, hwg⟩, hwix⟩
    refine ⟨?_, ?_⟩
    · -- the ∃ / visibility half: the source is IN the hull, at `hren t`
      cases t with
      | zero => exact hsrc
      | succ i =>
        obtain ⟨w, hwat, hcw, hwb, hvis, _, _⟩ := hsrcw (Nat.succ_pos i)
        apply gloadSrcIntro _ _ a v e (hrenPos G cs _ w hwat hcw)
        refine ⟨w, hrenWat G cs _ w hwat hcw, (gxhWrb G cs w a v).2 ⟨hcw, hwb⟩, ?_⟩
        rcases hvis with hmo | hpo
        · exact Or.inl ((gxhGmoLt G cs w e hnd).2 ⟨hcw, hce, hmo⟩)
        · exact Or.inr ((gxhGpo G cs w e).2 ⟨hpo, hce⟩)
    · -- the co-max half: FEWER writes only weakens it
      intro w' v' hwb' hvis'
      obtain ⟨hcw', hwb'⟩ := (gxhWrb G cs w' a v').1 hwb'
      have hvis : gvisible G w' e := by
        rcases hvis' with hmo | hpo
        · exact Or.inl ((gxhGmoLt G cs w' e hnd).1 hmo).2.2
        · exact Or.inr ((gxhGpo G cs w' e).1 hpo).1
      have hle := hmax w' v' hwb' hvis
      have hw'g : w' ∈ gwrites G := gwritesByteInGwrites G w' a v' hwf hwb'
      have hw'h : w' ∈ gwrites (gxHull G cs) := (gxhGwritesElem G cs w').2 ⟨hcw', hw'g⟩
      cases t with
      | zero =>
        have := WeakRvwmoGraph.gwixPos G w' hw'g
        omega
      | succ i =>
        obtain ⟨w, hwat, hcw, _, _, hwh, hwix⟩ := hsrcw (Nat.succ_pos i)
        rw [hrenWix G cs (i + 1) w hwat hcw]
        exact gxhGwixLe G cs w' w hnd hw'h hwh (by omega)
  · -- atomicity
    intro e a t' v hrd' hw' w' v' hwb' hlt
    obtain ⟨hce, t, hrd, rfl⟩ := gxhRdbInv G cs e a t' v hrd'
    have hw := ((gxhGlblIs G cs e lbIsW (fun π l => lblRenIsW π l)).1 hw').2
    obtain ⟨hsrc, _⟩ := hlv e a t v hrd
    obtain ⟨hlt1, hlt2⟩ := hlt
    obtain ⟨hcw', hwb⟩ := (gxhWrb G cs w' a v').1 hwb'
    have heg : e ∈ gwrites G :=
      (gwritesElemOf G e).2 ⟨gwfMemGmo G e hwf (WeakRvwmoGraph.glblIsWGmem G e hw),
        glblIsWGisW G e hw⟩
    have heh := (gxhGwritesElem G cs e).2 ⟨hce, heg⟩
    have hw'g : w' ∈ gwrites G := gwritesByteInGwrites G w' a v' hwf hwb
    have hw'h := (gxhGwritesElem G cs w').2 ⟨hcw', hw'g⟩
    apply hat e a t v hrd hw w' v' hwb
    refine ⟨?_, (gxhGwixLt G cs w' e hnd hw'h heh).1 hlt2⟩
    cases t with
    | zero => exact WeakRvwmoGraph.gwixPos G w' hw'g
    | succ i =>
      obtain ⟨w, hwat, _, _⟩ := gloadSrcElim G (i + 1) a v e (Nat.succ_pos i) hsrc
      have hcw := hullOkRf G cs e a (i + 1) v w hok hce hrd hwat
      obtain ⟨hwg, hwix⟩ := gwriteAtInv G (i + 1) w hnd hwat
      have hwh := (gxhGwritesElem G cs w).2 ⟨hcw, hwg⟩
      rw [hrenWix G cs (i + 1) w hwat hcw] at hlt1
      have := (gxhGwixLt G cs w w' hnd hwh hw'h).1 hlt1
      omega

/-! # 5. RULE 14 FROM VIOLATION-FREEDOM OF THE HULL -/

theorem gviolHull (G : Gexec) (cs : List Nat) (e w : Geid) :
    G.gxGmo.Nodup → gviol (gxHull G cs) e w →
    gviol G e w ∧ gcut cs e = true ∧ gcut cs w = true := by
  rintro hnd ⟨hpo, hme, hw, hmo⟩
  obtain ⟨hpo, hcw⟩ := (gxhGpo G cs e w).1 hpo
  obtain ⟨hce, hme⟩ := (gxhGmem G cs e).1 hme
  have hw := ((gxhGlblIs G cs w lbIsW (fun π l => lblRenIsW π l)).1 hw).2
  have hmo := ((gxhGmoLt G cs w e hnd).1 hmo).2.2
  exact ⟨⟨hpo, hme, hw, hmo⟩, hce, hcw⟩

theorem hullRule14 (G : Gexec) (cs : List Nat) :
    rvwmoMinusConsistent G → hullOk G cs →
    (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol G e w) →
    grule14 (gxHull G cs) := by
  intro hc hok hvf
  have hnd := hc.1.1
  apply gviolGrule14
  · exact (hullConsistent G cs hc hok).1
  · intro e w hv
    obtain ⟨hv', hce, hcw⟩ := gviolHull G cs e w hnd hv
    exact hvf e w hce hcw hv'

/-! # 6. THE `Gdexec` FORM: the dep fragment restricts by filtering -/

def gdHull (GD : Gdexec) (cs : List Nat) : Gdexec :=
  ⟨gxHull GD.gdG cs,
   GD.gdDeps.filter (fun p : Geid × Geid => gcut cs p.1 && gcut cs p.2)⟩

theorem gdHullDeps (GD : Gdexec) (cs : List Nat) (p : Geid × Geid) :
    p ∈ (gdHull GD cs).gdDeps ↔
      p ∈ GD.gdDeps ∧ gcut cs p.1 = true ∧ gcut cs p.2 = true := by
  simp [gdHull, List.mem_filter]

theorem hullDepsConsistent (GD : Gdexec) (cs : List Nat) :
    rvwmoMinusDepsConsistent GD → hullOk GD.gdG cs →
    rvwmoMinusDepsConsistent (gdHull GD cs) := by
  rintro ⟨hc, hdwf, hdmo⟩ hok
  have hnd := hc.1.1
  refine ⟨hullConsistent GD.gdG cs hc hok, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (gdHullDeps GD cs p).1 hp
    obtain ⟨h1, h2, h3, h4⟩ := hdwf p hp
    exact ⟨h1, h2, (gxhGlblIs GD.gdG cs p.1 lbIsR (fun π l => lblRenIsR π l)).2 ⟨hc1, h3⟩,
      (gxhGlblIs GD.gdG cs p.2 lbIsW (fun π l => lblRenIsW π l)).2 ⟨hc2, h4⟩⟩
  · intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (gdHullDeps GD cs p).1 hp
    exact (gxhGmoLt GD.gdG cs p.1 p.2 hnd).2 ⟨hc1, hc2, hdmo p hp⟩

/-! # 7. THE COMPOSITION: a violation-free hull LINEARIZES -/

theorem omapGmsgHull (G : Gexec) (cs : List Nat) (l : List Geid) :
    (∀ e, e ∈ l → gcut cs e = true) →
    l.filterMap (WeakRvwmoLin.gmsg (gxHull G cs)) = l.filterMap (WeakRvwmoLin.gmsg G) := by
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro hcut
    rw [List.filterMap_cons, List.filterMap_cons, gxhGmsg G cs e (hcut e (by simp)),
      ih (fun x hx => hcut x (by simp [hx]))]

theorem hullLinearizes (GD : Gdexec) (cs : List Nat) :
    rvwmoMinusDepsConsistent GD → hullOk GD.gdG cs →
    (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol GD.gdG e w) →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      (∀ i, (c.cdTr.filter (fun s : Estep => decide (s.esAg = i))).map (fun s => s.esLb) =
        (List.take ((cs[i]?).getD 0) ((GD.gdG.gxProg[i]?).getD [])).map
          (lblRen (hren GD.gdG cs))) ∧
      cdLog c c.cdTr.length =
        ((gwrites GD.gdG).filter (gcut cs)).filterMap (WeakRvwmoLin.gmsg GD.gdG) := by
  intro hD hok hvf
  have hc := hD.1
  obtain ⟨c, hsr, himg, hrow, hlog⟩ := rule14Linearization (gxHull GD.gdG cs)
    (hullConsistent _ _ hc hok) (hullRule14 _ _ hc hok hvf)
  refine ⟨c, hsr, himg, ?_, ?_⟩
  · intro i
    rw [hrow i, gxhRow]
  · rw [hlog, gxhGwritesG]
    exact omapGmsgHull _ cs _ (fun e he => (elem_of_list_filter.1 he).1)

/-! # 8. THE FULL CUT IS A HULL, AND IT IS THE IDENTITY -/

theorem gfullCut (G : Gexec) (e : Geid) :
    (gxLbl G e).isSome = true → gcut (gfullCs G) e = true := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome h
  unfold gxLbl at hl
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at hl; simp at hl
  | some p =>
    rw [hp] at hl
    have hl' : p[e.2]? = some l := hl
    exact gcutIntro _ _ p.length (by simp [gfullCs, hp]) (lookup_lt_Some hl')

theorem gfullFilterGmo (G : Gexec) : gwf G → G.gxGmo.filter (gcut (gfullCs G)) = G.gxGmo := by
  intro hwf
  apply WeakRvwmoHull.filterAll
  intro e he
  apply gfullCut
  obtain ⟨l, hl, _⟩ := gwfGmoMem G e hwf he
  simp [hl]

theorem gfullFilterGwrites (G : Gexec) :
    gwf G → (gwrites G).filter (gcut (gfullCs G)) = gwrites G := by
  intro hwf
  apply WeakRvwmoHull.filterAll
  intro e he
  apply gfullCut
  obtain ⟨l, hl, _⟩ := gwfGmoMem G e hwf ((gwritesElemOf G e).1 he).1
  simp [hl]

theorem hrenFull (G : Gexec) : gwf G → ∀ t, hren G (gfullCs G) t = t := by
  intro hwf t
  have hnd := hwf.1
  unfold hren
  cases ht : gwriteAt G t with
  | none => rfl
  | some w =>
    show (if gcut (gfullCs G) w = true then gwix (gxCut G (gfullCs G)) w else t) = t
    split
    · unfold gwix
      rw [gxcGwrites, gfullFilterGwrites G hwf]
      exact (gwriteAtInv G t w hnd ht).2
    · rfl

theorem hullOkFull (G : Gexec) : gwf G → hullOk G (gfullCs G) := by
  intro hwf
  refine ⟨by simp [gfullCs], ?_⟩
  intro r a t v w _ _ hwat
  apply gfullCut
  obtain ⟨hm, _⟩ := (gwritesElemOf G w).1 (gwriteAtGwrites G t w hwat)
  obtain ⟨l, hl, _⟩ := gwfGmoMem G w hwf hm
  simp [hl]

theorem zipWithTakeFull (prog : List (List Lbl)) :
    List.zipWith List.take (prog.map List.length) prog = prog := by
  induction prog with
  | nil => rfl
  | cons p prog ih => simp [ih]

theorem gxHullFull (G : Gexec) : gwf G → gxHull G (gfullCs G) = G := by
  intro hwf
  have hpi := hrenFull G hwf
  have h3 : ∀ r : List Lbl, r.map (lblRen (hren G (gfullCs G))) = r := by
    intro r
    have : lblRen (hren G (gfullCs G)) = lblRen (fun t => t) :=
      funext (fun l => lblRenExt _ _ l hpi)
    rw [this]
    exact rowRenId r
  have h4 : G.gxProg.map (fun row : List Lbl => row.map (lblRen (hren G (gfullCs G)))) =
      G.gxProg := by
    simp only [h3, fmapIdGen]
  show (⟨G.gxImg,
    (List.zipWith List.take (gfullCs G) G.gxProg).map
      (fun row : List Lbl => row.map (lblRen (hren G (gfullCs G)))),
    G.gxGmo.filter (gcut (gfullCs G))⟩ : Gexec) = G
  rw [show List.zipWith List.take (gfullCs G) G.gxProg = G.gxProg from zipWithTakeFull G.gxProg,
    h4, gfullFilterGmo G hwf]

/-! # 9. NON-VACUITY, AT THE PROBE THAT MOTIVATED THE GENERALIZATION

The hull `ecs = [1, 0]` keeps exactly hart 0's load `(0,0)`: it reads the
ERA-INITIAL image, so there is no source to keep, and a one-event cut carries no
po edge, so it is violation-free. -/

def ecs : List Nat := [1, 0]

theorem ergCut (e : Geid) : gcut ecs e = true ↔ e = (0, 0) := by
  obtain ⟨i, k⟩ := e
  constructor
  · intro h
    rcases i with _ | _ | i <;> simp [gcut, ecs] at h ⊢ <;> omega
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    decide

theorem ergHullOk : hullOk erg ecs := by
  refine ⟨rfl, ?_⟩
  intro r a t v w hcr hrd hwat
  rw [ergCut] at hcr
  subst hcr
  obtain ⟨l, base, ts, vs, j, hl, hrd, ht, _⟩ := hrd
  -- the load names the era-initial index, which is no write at all
  simp [gxLbl, erg] at hl
  subst hl
  simp [lbRd] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rcases j with _ | j <;> simp at ht
  subst ht
  simp [gwriteAt] at hwat

theorem ergHullViolFree :
    ∀ e w, gcut ecs e = true → gcut ecs w = true → ¬ gviol erg e w := by
  intro e w he hw
  rw [ergCut] at he hw
  subst he
  subst hw
  rintro ⟨⟨_, hlt, _⟩, _⟩
  exact Nat.lt_irrefl _ hlt

def ergd : Gdexec := ⟨erg, []⟩

theorem ergdConsistent : rvwmoMinusDepsConsistent ergd :=
  ⟨ergConsistent, fun _ h => by simp [ergd] at h, fun _ h => by simp [ergd] at h⟩

/-- THE INSTANTIATION. -/
theorem ergHullLinearizes :
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = erg.gxImg ∧
      (∀ i, (c.cdTr.filter (fun s : Estep => decide (s.esAg = i))).map (fun s => s.esLb) =
        (List.take ((ecs[i]?).getD 0) ((erg.gxProg[i]?).getD [])).map (lblRen (hren erg ecs))) ∧
      cdLog c c.cdTr.length =
        ((gwrites erg).filter (gcut ecs)).filterMap (WeakRvwmoLin.gmsg erg) :=
  hullLinearizes ergd ecs ergdConsistent ergHullOk ergHullViolFree

/-- THE CONTRAST: the hull condition is SATISFIABLE at `erg` while B1a's
restriction condition is NOT. -/
theorem ergHullBeatsRestr : hullOk erg ecs ∧ (∀ cs, ¬ restrOk erg cs 1) :=
  ⟨ergHullOk, ergNoRestr⟩

end Weak
