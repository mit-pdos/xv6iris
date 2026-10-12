/-
Weak: **B2d′(a) — a topological order of `racy` IS a consistent rule-14 gmo**
(route-b §4d.1 F2(ii), §4d.4 "the direct linearization").

Rocq: `iris/WeakRvwmoTopo.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakRvwmoNorm.normalize` reaches a rule-14 graph
by the exchange induction and pays for it with the KILL INTERFACE.  F2(ii) says
the interface is unnecessary: RE-TIME the graph.  Keep the rows and the image;
replace the global memory order by ANY list `L` that is a permutation of the old
order and puts every `racyD` edge forward (`linExtD`).  The result `retime G L`
is `rvwmoMinusDepsConsistent` AND `grule14`, with exactly `normalize`'s output
correspondence (`rowsRel` / `wperm` / same deps) — `topoLinearizes`.  Re-timing
moves write INDICES, so a read's `ts` entries are renamed by `tren G L`: the old
index of a write ↦ its rank in the new order (`gwixL`), and the identity off the
write range (load-bearing for `wperm`'s injectivity on all of `Nat`).

Where each edge class is spent: `gwf` — permutation facts and `lblRenShape`;
`gppoGmo` — the ppo⁻ arm; `gloadValue` — rf for the source, fr / co for
co-maximality (the fused-RMW `w' = e` case by `gvisible`'s irreflexivity);
`gatomicity` — `tren` is MONOTONE ON SAME-BYTE WRITES both ways (`linCoFwd`,
`linCoInv`, by co and trichotomy); `grule14` — the po-into-a-write arm; the deps
— their own arm of `racyD`.

EXISTENCE (§4): a finite topological sort (`topoSortExists`) needs only
`Decidable (R x y)` (the descent `topoMinDesc` walks down one edge at a time;
acyclicity of `tc R` stops re-entry).  `topoExists` therefore carries the
hypothesis `∀ x y, Decidable (racyD GD x y)` — Rocq's recorded open item (D), a
genuine side condition, not a hole.  `normalizeOfAcyclic` is `normalize`'s
conclusion from acyclicity alone.  A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The Rocq names of
   this file listed in `notes/weak-port-dupnames.json` (`lbl_ren_shape`,
   `topo_min`, `topo_sort_aux`, `step_dep`) are FILE-QUALIFIED
   (`WeakRvwmoTopo.lblRenShape`, …).  `Racy`/`RacyD` are `WeakRvwmoAcyc`'s
   `racy`/`racyD`.
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2; `≡ₚ` ↦ `List.Perm`, `Decision`
   ↦ `Decidable`, the `sumbool`-like `{x | …} + (∀ …)` of `list_ex_dec` ↦
   `PSum` (its second summand is a `Prop`), `list_find (λ e', e' = w)` ↦
   `listFind (fun e' => decide (e' = w))`, `GDExec g d` ↦ `⟨g, d⟩`.
3. SECTION `topo_lin`: the Rocq section's `Local Lemma`s are top-level theorems
   over the section variables `GD L` and the hypotheses `hcons hlin` (all four
   `include`d in every lemma of the section, so each lemma's Lean statement takes
   both hypotheses even when its proof uses only one; Rocq's section closing
   keeps only the used ones).  `topoLinearizes`'s closed statement is Rocq's.
   The `topo_sort` section's context `R Rdec Hacy` is explicit in each lemma.
4. `list_ex_dec` is a `def` (its result is data).

**Name map** (Rocq → Lean): `before`; `before_cons` ↦ `beforeCons`;
`perm_elem_of` ↦ `permElemOf`; `before_head` ↦ `beforeHead`; `gwixL`; `tren`;
`retime`; `lin_ext` ↦ `linExt`; `lin_extD` ↦ `linExtD`; `lin_extD_lin_ext` ↦
`linExtDLinExt`; `tren_zero`/`_at`/`_none` ↦ `trenZero`/`trenAt`/`trenNone`;
`retime_rows_rel`/`_gis_w`/`_gwrites`/`_gwix` ↦ `retimeRowsRel`/`retimeGisW`/
`retimeGwrites`/`retimeGwix`; `lbl_ren_shape` ↦ `WeakRvwmoTopo.lblRenShape`;
`lin_wf`/`lin_lv`/`lin_at`/`lin_perm`/`lin_rows`/`lin_nodup`/`lin_wfilter`/
`lin_wlen`/`lin_welem`/`lin_wat`/`lin_wperm`/`lin_before` ↦ `linWf`/`linLv`/
`linAt`/`linPerm`/`linRows`/`linNodup`/`linWfilter`/`linWlen`/`linWelem`/
`linWat`/`linWperm`/`linBefore`; `step_racy` ↦ `stepRacy`; `step_dep` ↦
`WeakRvwmoTopo.stepDep`; `lin_co_fwd`/`_inv` ↦ `linCoFwd`/`linCoInv`;
`lin_gwf`/`lin_gppo`/`lin_grule14`/`lin_gload_value`/`lin_gatomicity`/
`lin_gdeps_wf`/`lin_gdeps_gmo` ↦ `linGwf`/`linGppo`/`linGrule14`/
`linGloadValue`/`linGatomicity`/`linGdepsWf`/`linGdepsGmo`; `topo_linearizes`
↦ `topoLinearizes`; `list_ex_dec` ↦ `listExDec`; `topo_min_desc` ↦
`topoMinDesc`; `topo_min` ↦ `WeakRvwmoTopo.topoMin`; `topo_sort_aux` ↦
`WeakRvwmoTopo.topoSortAux`; `topo_sort_exists` ↦ `topoSortExists`;
`RacyD_mem` ↦ `racyDMem`; `topo_exists` ↦ `topoExists`;
`normalize_of_acyclic` ↦ `normalizeOfAcyclic`.

**Not ported:** nothing (the three `Print Assumptions` are commands, not
declarations).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `WeakRvwmoTopo.lblRenShape`'s `LIo` arms are `True` (`gwf`'s flip).
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoNorm
import Weak.WeakRvwmoAcyc

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. `before`: the order a list induces -/

def before {A : Type _} (L : List A) (x y : A) : Prop :=
  ∃ i j : Nat, L[i]? = some x ∧ L[j]? = some y ∧ i < j

theorem beforeCons {A : Type _} (m : A) (L : List A) (x y : A) :
    before L x y → before (m :: L) x y := by
  rintro ⟨i, j, hi, hj, hlt⟩
  exact ⟨i + 1, j + 1, by simpa using hi, by simpa using hj, by omega⟩

theorem permElemOf {A : Type _} (l1 l2 : List A) (x : A) : l1.Perm l2 → (x ∈ l1 ↔ x ∈ l2) :=
  fun hp => hp.mem_iff

theorem beforeHead {A : Type _} (m : A) (L : List A) (y : A) : y ∈ L → before (m :: L) m y := by
  intro hy
  obtain ⟨j, hj⟩ := elem_of_list_lookup_1 hy
  exact ⟨0, j + 1, rfl, by simpa using hj, by omega⟩

/-! # 2. RE-TIMING: the new order, and the write-index renaming it forces -/

/-- The rank (1-based, exactly as `gwix`) of `w` among the writes of `L`. -/
def gwixL (G : Gexec) (L : List Geid) (w : Geid) : Nat :=
  match listFind (fun e' => decide (e' = w)) (L.filter (gisW G)) with
  | some (i, _) => i + 1
  | none => 0

/-- The write-index renaming: old index ↦ new index of the SAME write; the
identity off the write range. -/
def tren (G : Gexec) (L : List Geid) (t : Nat) : Nat :=
  match gwriteAt G t with
  | some w => gwixL G L w
  | none => t

def retime (G : Gexec) (L : List Geid) : Gexec :=
  ⟨G.gxImg, G.gxProg.map (fun row : List Lbl => row.map (lblRen (tren G L))), L⟩

/-- A LINEAR EXTENSION of `racy` — the input the re-timing consumes. -/
def linExt (G : Gexec) (L : List Geid) : Prop :=
  L.Perm G.gxGmo ∧ ∀ x y, racy G x y → before L x y

/-- … and its `Gdexec` form (the store-dep fragment ordered too). -/
def linExtD (GD : Gdexec) (L : List Geid) : Prop :=
  L.Perm GD.gdG.gxGmo ∧ ∀ x y, racyD GD x y → before L x y

theorem linExtDLinExt (GD : Gdexec) (L : List Geid) : linExtD GD L → linExt GD.gdG L := by
  rintro ⟨hL, hord⟩
  exact ⟨hL, fun x y hR => hord x y (Or.inl hR)⟩

/-! ## 2.1 The hypothesis-free half of the correspondence -/

theorem trenZero (G : Gexec) (L : List Geid) : tren G L 0 = 0 := rfl

theorem trenAt (G : Gexec) (L : List Geid) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → tren G L t = gwixL G L w := by
  intro ht
  simp only [tren, ht]

theorem trenNone (G : Gexec) (L : List Geid) (t : Nat) :
    gwriteAt G t = none → tren G L t = t := by
  intro ht
  simp only [tren, ht]

theorem retimeRowsRel (G : Gexec) (L : List Geid) : rowsRel (tren G L) G (retime G L) :=
  ⟨rfl, rfl, trenZero G L⟩

theorem retimeGisW (G : Gexec) (L : List Geid) (e : Geid) : gisW (retime G L) e = gisW G e :=
  rowsRelGisW _ G _ e (retimeRowsRel G L)

theorem retimeGwrites (G : Gexec) (L : List Geid) : gwrites (retime G L) = L.filter (gisW G) := by
  have h : gisW (retime G L) = gisW G := funext (retimeGisW G L)
  unfold gwrites
  rw [h]
  rfl

theorem retimeGwix (G : Gexec) (L : List Geid) (w : Geid) : gwix (retime G L) w = gwixL G L w := by
  unfold gwix gwixL
  rw [retimeGwrites]
  rfl

/-- `lblRen` preserves `gwf`'s shape clause. -/
theorem WeakRvwmoTopo.lblRenShape (pi : Nat → Nat) (l : Lbl) :
    (match l with
     | LLoad _ _ ts vs => vs.length = ts.length
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
     | LIo .. => True) →
    (match lblRen pi l with
     | LLoad _ _ ts vs => vs.length = ts.length
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
     | LIo .. => True) := by
  intro h
  cases l <;> simp only [lblRen, List.length_map] at h ⊢ <;> exact h

/-! # 3. THE LINEARIZATION THEOREM -/

section TopoLin

variable (GD : Gdexec) (L : List Geid)
variable (hcons : rvwmoMinusDepsConsistent GD) (hlin : linExtD GD L)
include hcons hlin

theorem linWf : gwf GD.gdG := hcons.1.1
theorem linLv : gloadValue GD.gdG := hcons.1.2.2.1
theorem linAt : gatomicity GD.gdG := hcons.1.2.2.2
theorem linPerm : L.Perm GD.gdG.gxGmo := hlin.1

theorem linRows : rowsRel (tren GD.gdG L) GD.gdG (retime GD.gdG L) := retimeRowsRel GD.gdG L

/-! ## 3.1 `L` is a well-formed order, and `tren` is a write permutation -/

theorem linNodup : L.Nodup := (linPerm GD L hcons hlin).nodup_iff.2 (linWf GD L hcons hlin).1

theorem linWfilter : (L.filter (gisW GD.gdG)).Perm (gwrites GD.gdG) :=
  (linPerm GD L hcons hlin).filter _

theorem linWlen : (gwrites (retime GD.gdG L)).length = (gwrites GD.gdG).length := by
  rw [retimeGwrites]
  exact (linWfilter GD L hcons hlin).length_eq

theorem linWelem (w : Geid) : w ∈ gwrites (retime GD.gdG L) ↔ w ∈ gwrites GD.gdG := by
  rw [retimeGwrites]
  exact (linWfilter GD L hcons hlin).mem_iff

theorem linWat (t : Nat) : gwriteAt (retime GD.gdG L) (tren GD.gdG L t) = gwriteAt GD.gdG t := by
  cases ht : gwriteAt GD.gdG t with
  | some w =>
    rw [trenAt GD.gdG L t w ht, ← retimeGwix]
    exact gwriteAtGwix _ w ((linWelem GD L hcons hlin w).2 (gwriteAtGwrites GD.gdG t w ht))
  | none =>
    rw [trenNone GD.gdG L t ht]
    cases t with
    | zero => rfl
    | succ i =>
      simp only [gwriteAt] at ht ⊢
      apply lookup_ge_None_2
      rw [linWlen GD L hcons hlin]
      exact lookup_ge_None_1 ht

theorem linWperm : wperm (tren GD.gdG L) GD.gdG (retime GD.gdG L) := by
  refine ⟨?_, linWat GD L hcons hlin, linWlen GD L hcons hlin⟩
  intro t1 t2 heq
  have h1 := linWat GD L hcons hlin t1
  have h2 := linWat GD L hcons hlin t2
  rw [heq, h2] at h1
  cases e1 : gwriteAt GD.gdG t1 with
  | some w =>
    rw [e1] at h1
    have a := (gwriteAtInv GD.gdG t1 w (linWf GD L hcons hlin).1 e1).2
    have b := (gwriteAtInv GD.gdG t2 w (linWf GD L hcons hlin).1 h1).2
    omega
  | none =>
    rw [e1] at h1
    have a := trenNone GD.gdG L t1 e1
    have b := trenNone GD.gdG L t2 h1
    omega

/-! ## 3.2 The bridge: `before L` IS `gmoLt` of the re-timed graph -/

theorem linBefore (x y : Geid) : before L x y ↔ gmoLt (retime GD.gdG L) x y := by
  have hnd : (retime GD.gdG L).gxGmo.Nodup := linNodup GD L hcons hlin
  constructor
  · rintro ⟨i, j, hi, hj, hlt⟩
    refine ⟨elem_of_list_lookup_2 hi, elem_of_list_lookup_2 hj, ?_⟩
    rw [gposOfLookup (retime GD.gdG L) i x hnd hi, gposOfLookup (retime GD.gdG L) j y hnd hj]
    exact hlt
  · rintro ⟨hx, hy, hlt⟩
    exact ⟨gpos (retime GD.gdG L) x, gpos (retime GD.gdG L) y,
      gposElemLookup (retime GD.gdG L) x hx, gposElemLookup (retime GD.gdG L) y hy, hlt⟩

theorem stepRacy (x y : Geid) : racy GD.gdG x y → gmoLt (retime GD.gdG L) x y :=
  fun hR => (linBefore GD L hcons hlin x y).1 (hlin.2 x y (Or.inl hR))

theorem WeakRvwmoTopo.stepDep (x y : Geid) : (x, y) ∈ GD.gdDeps → gmoLt (retime GD.gdG L) x y :=
  fun hd => (linBefore GD L hcons hlin x y).1 (hlin.2 x y (Or.inr hd))

/-! ## 3.3 `tren` is MONOTONE ON SAME-BYTE WRITES, both ways -/

theorem linCoFwd (w1 w2 : Geid) (a : Int) (u1 u2 : BitVec 8) :
    gwritesByte GD.gdG w1 a u1 → gwritesByte GD.gdG w2 a u2 →
    gwix GD.gdG w1 < gwix GD.gdG w2 → gwix (retime GD.gdG L) w1 < gwix (retime GD.gdG L) w2 := by
  intro h1 h2 hlt
  have hmo : gmoLt (retime GD.gdG L) w1 w2 :=
    stepRacy GD L hcons hlin w1 w2 (Or.inr (Or.inr (Or.inl ⟨a, u1, u2, h1, h2, hlt⟩)))
  exact (gwixGposLt (retime GD.gdG L) w1 w2 (linNodup GD L hcons hlin)
    ((linWelem GD L hcons hlin w1).2
      (gwritesByteInGwrites GD.gdG w1 a u1 (linWf GD L hcons hlin) h1))
    ((linWelem GD L hcons hlin w2).2
      (gwritesByteInGwrites GD.gdG w2 a u2 (linWf GD L hcons hlin) h2))).2 hmo.2.2

theorem linCoInv (w1 w2 : Geid) (a : Int) (u1 u2 : BitVec 8) :
    gwritesByte GD.gdG w1 a u1 → gwritesByte GD.gdG w2 a u2 →
    gwix (retime GD.gdG L) w1 < gwix (retime GD.gdG L) w2 → gwix GD.gdG w1 < gwix GD.gdG w2 := by
  intro h1 h2 hlt
  have hin1 := gwritesByteInGwrites GD.gdG w1 a u1 (linWf GD L hcons hlin) h1
  have hin2 := gwritesByteInGwrites GD.gdG w2 a u2 (linWf GD L hcons hlin) h2
  rcases Nat.lt_trichotomy (gwix GD.gdG w1) (gwix GD.gdG w2) with h | h | h
  · exact h
  · exfalso
    have := gwixInj GD.gdG w1 w2 (linWf GD L hcons hlin).1 hin1 hin2 h
    subst this
    omega
  · exfalso
    have := linCoFwd GD L hcons hlin w2 w1 a u2 u1 h2 h1 h
    omega

/-! ## 3.4 The axioms of the re-timed graph -/

theorem linGwf : gwf (retime GD.gdG L) := by
  obtain ⟨_, hmem, hsh⟩ := linWf GD L hcons hlin
  have hperm := linPerm GD L hcons hlin
  have hrows := linRows GD L hcons hlin
  refine ⟨linNodup GD L hcons hlin, ?_, ?_⟩
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

theorem linGppo : gppoGmo (retime GD.gdG L) := by
  intro e1 e2 hppo'
  exact stepRacy GD L hcons hlin e1 e2 (Or.inr (Or.inr (Or.inr (Or.inr
    ((rowsRelGppo _ GD.gdG _ e1 e2 (linRows GD L hcons hlin)).1 hppo')))))

theorem linGrule14 : grule14 (retime GD.gdG L) := by
  intro e w hpo hmem hw
  have hrows := linRows GD L hcons hlin
  exact stepRacy GD L hcons hlin e w (Or.inl
    ⟨(rowsRelGpo _ GD.gdG _ e w hrows).1 hpo, (rowsRelGmem _ GD.gdG _ e hrows).1 hmem,
     glblIsWGisW GD.gdG w ((rowsRelGlblIs _ GD.gdG _ w lbIsW hrows (lblRenIsW _)).1 hw)⟩)

theorem linGloadValue : gloadValue (retime GD.gdG L) := by
  intro e a t' v hrd'
  have hrows := linRows GD L hcons hlin
  obtain ⟨t, rfl, hrd⟩ := rowsRelRdbInv _ GD.gdG _ e a t' v hrows hrd'
  have hwf := linWf GD L hcons hlin
  obtain ⟨hsrc, hmax⟩ := linLv GD L hcons hlin e a t v hrd
  have hinj := (linWperm GD L hcons hlin).1
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
          Or.inl (stepRacy GD L hcons hlin w e (Or.inr (Or.inl ⟨a, t0 + 1, v, hrd, hwat⟩)))⟩
        rw [← hpt, linWat GD L hcons hlin]
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
          stepRacy GD L hcons hlin w' e (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hpo, a, Or.inl ⟨v', hwb⟩, Or.inr ⟨t, v, hrd⟩⟩)))))
        exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hew hwe)
    rcases Nat.lt_or_ge t (gwix GD.gdG w') with hgt | hle
    · exact absurd (stepRacy GD L hcons hlin e w' (Or.inr (Or.inr (Or.inr (Or.inl
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
          exact Nat.le_of_lt (linCoFwd GD L hcons hlin w' w a v' v hwb hwbw (by omega))

theorem linGatomicity : gatomicity (retime GD.gdG L) := by
  rintro e a t' v hrd' hw' w' v' hwb' ⟨_, hlt2⟩
  have hrows := linRows GD L hcons hlin
  obtain ⟨t, hpt, hrd⟩ := rowsRelRdbInv _ GD.gdG _ e a t' v hrows hrd'
  have hwf := linWf GD L hcons hlin
  have hw := (rowsRelGlblIs _ GD.gdG _ e lbIsW hrows (lblRenIsW _)).1 hw'
  have hwb := (rowsRelWrb _ GD.gdG _ w' a v' hrows).1 hwb'
  have hw'in := gwritesByteInGwrites GD.gdG w' a v' hwf hwb
  obtain ⟨ve, hwbe⟩ := greadByteWriteByte GD.gdG e a t v hwf (glblIsWGisW GD.gdG e hw) hrd
  -- the upper bound
  have hup : gwix GD.gdG w' < gwix GD.gdG e :=
    linCoInv GD L hcons hlin w' e a v' ve hwb hwbe hlt2
  -- the lower bound
  have hlow : t < gwix GD.gdG w' := by
    cases t with
    | zero =>
      have := WeakRvwmoGraph.gwixPos GD.gdG w' hw'in
      omega
    | succ t0 =>
      obtain ⟨w, hwat, hwbw, _⟩ := (linLv GD L hcons hlin e a (t0 + 1) v hrd).1
      have hwix : gwix GD.gdG w = t0 + 1 := (gwriteAtInv GD.gdG (t0 + 1) w hwf.1 hwat).2
      have hgw : gwix (retime GD.gdG L) w = t' := by
        rw [retimeGwix, hpt, trenAt GD.gdG L (t0 + 1) w hwat]
      rw [← hwix]
      exact linCoInv GD L hcons hlin w w' a v v' hwbw hwb (by omega)
  exact linAt GD L hcons hlin e a t v hrd hw w' v' hwb ⟨hlow, hup⟩

theorem linGdepsWf : gdepsWf (retime GD.gdG L) GD.gdDeps := by
  intro rw hrw
  have hrows := linRows GD L hcons hlin
  obtain ⟨h1, h2, h3, h4⟩ := hcons.2.1 rw hrw
  exact ⟨h1, h2, (rowsRelGlblIs _ GD.gdG _ rw.1 lbIsR hrows (lblRenIsR _)).2 h3,
    (rowsRelGlblIs _ GD.gdG _ rw.2 lbIsW hrows (lblRenIsW _)).2 h4⟩

theorem linGdepsGmo : gdepsGmo (retime GD.gdG L) GD.gdDeps := by
  rintro ⟨r, w⟩ hrw
  exact WeakRvwmoTopo.stepDep GD L hcons hlin r w hrw

/-- THE DELIVERABLE. -/
theorem topoLinearizes :
    rvwmoMinusDepsConsistent ⟨retime GD.gdG L, GD.gdDeps⟩ ∧
    grule14 (retime GD.gdG L) ∧
    rowsRel (tren GD.gdG L) GD.gdG (retime GD.gdG L) ∧
    wperm (tren GD.gdG L) GD.gdG (retime GD.gdG L) :=
  ⟨⟨⟨linGwf GD L hcons hlin, linGppo GD L hcons hlin, linGloadValue GD L hcons hlin,
      linGatomicity GD L hcons hlin⟩,
    linGdepsWf GD L hcons hlin, linGdepsGmo GD L hcons hlin⟩,
   linGrule14 GD L hcons hlin, linRows GD L hcons hlin, linWperm GD L hcons hlin⟩

end TopoLin

/-! # 4. EXISTENCE: a finite topological sort

A minimal element of a finite carrier under an acyclic relation cannot be
produced constructively without deciding the relation, so this section takes
`Decidable (R x y)` — and NOTHING more (in particular not `Decidable (tc R x y)`). -/

def listExDec {A : Type _} (P : A → Prop) (Pdec : ∀ x, Decidable (P x)) :
    (l : List A) → PSum {x : A // x ∈ l ∧ P x} (∀ x, x ∈ l → ¬ P x)
  | [] => .inr (fun x hx => by simp at hx)
  | a :: l =>
    match Pdec a with
    | isTrue hp => .inl ⟨a, List.mem_cons.2 (Or.inl rfl), hp⟩
    | isFalse hnp =>
      match listExDec P Pdec l with
      | .inl ⟨x, hx, hpx⟩ => .inl ⟨x, List.mem_cons.2 (Or.inr hx), hpx⟩
      | .inr hno => .inr (fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hnp
          · exact hno x hx)

/-- DESCEND to a minimal element: from any `a ∈ M`, walk one `R`-edge down at a
time inside a shrinking list. -/
theorem topoMinDesc {A : Type _} (R : A → A → Prop) (Rdec : ∀ x y, Decidable (R x y))
    (hacy : ∀ x, ¬ tc R x x) (n : Nat) :
    ∀ (M : List A), M.length ≤ n → M.Nodup → ∀ a, a ∈ M →
    ∃ m, m ∈ M ∧ (m = a ∨ tc R m a) ∧ (∀ y, y ∈ M → ¬ R y m) := by
  induction n with
  | zero =>
    intro M hlen _ a ha
    cases M with
    | nil => simp at ha
    | cons z M => simp at hlen
  | succ n ih =>
    intro M hlen hnd a ha
    rcases listExDec (fun y => R y a) (fun y => Rdec y a) M with ⟨y, hy, hry⟩ | hno
    · have hya : y ≠ a := by
        rintro rfl
        exact hacy y (tc_once hry)
      obtain ⟨M1, hperm⟩ := elem_of_Permutation.1 ha
      have hnd' : (a :: M1).Nodup := hperm.nodup_iff.1 hnd
      have hy1 : y ∈ M1 := by
        rcases List.mem_cons.1 (hperm.mem_iff.1 hy) with h | h
        · exact absurd h hya
        · exact h
      have hlen1 : M1.length ≤ n := by
        have := hperm.length_eq
        rw [List.length_cons] at this
        omega
      obtain ⟨m, hm, hmy, hmin⟩ := ih M1 hlen1 (List.nodup_cons.1 hnd').2 y hy1
      have hma : tc R m a := by
        rcases hmy with h | h
        · subst h; exact tc_once hry
        · exact tc_r h hry
      refine ⟨m, hperm.mem_iff.2 (List.mem_cons.2 (Or.inr hm)), Or.inr hma, ?_⟩
      intro z hz hrz
      rcases List.mem_cons.1 (hperm.mem_iff.1 hz) with h | h
      · subst h
        exact hacy z (tc_l hrz hma)
      · exact hmin z h hrz
    · exact ⟨a, ha, Or.inl rfl, hno⟩

theorem WeakRvwmoTopo.topoMin {A : Type _} (R : A → A → Prop) (Rdec : ∀ x y, Decidable (R x y))
    (hacy : ∀ x, ¬ tc R x x) (M : List A) :
    M.Nodup → ∀ a, a ∈ M → ∃ m, m ∈ M ∧ (∀ y, y ∈ M → ¬ R y m) := by
  intro hnd a ha
  obtain ⟨m, hm, _, hmin⟩ := topoMinDesc R Rdec hacy M.length M (Nat.le_refl _) hnd a ha
  exact ⟨m, hm, hmin⟩

theorem WeakRvwmoTopo.topoSortAux {A : Type _} (R : A → A → Prop)
    (Rdec : ∀ x y, Decidable (R x y)) (hacy : ∀ x, ¬ tc R x x) (n : Nat) :
    ∀ (M : List A), M.length ≤ n → M.Nodup →
    ∃ L, L.Perm M ∧ (∀ x y, x ∈ M → y ∈ M → R x y → before L x y) := by
  induction n with
  | zero =>
    intro M hlen _
    cases M with
    | nil => exact ⟨[], List.Perm.refl _, fun x y hx => by simp at hx⟩
    | cons z M => simp at hlen
  | succ n ih =>
    intro M hlen hnd
    cases M with
    | nil => exact ⟨[], List.Perm.refl _, fun x y hx => by simp at hx⟩
    | cons a M0 =>
      obtain ⟨m, hm, hmin⟩ :=
        WeakRvwmoTopo.topoMin R Rdec hacy (a :: M0) hnd a (List.mem_cons.2 (Or.inl rfl))
      obtain ⟨M1, hperm⟩ := elem_of_Permutation.1 hm
      have hnd1 : (m :: M1).Nodup := hperm.nodup_iff.1 hnd
      have hlen1 : M1.length ≤ n := by
        have := hperm.length_eq
        rw [List.length_cons, List.length_cons] at this
        rw [List.length_cons] at hlen
        omega
      obtain ⟨L1, hL1, hord⟩ := ih M1 hlen1 (List.nodup_cons.1 hnd1).2
      refine ⟨m :: L1, (hL1.cons m).trans hperm.symm, ?_⟩
      intro x y hx hy hr
      have hym : y ≠ m := by
        rintro rfl
        exact hmin x hx hr
      have hy1 : y ∈ M1 := by
        rcases List.mem_cons.1 (hperm.mem_iff.1 hy) with h | h
        · exact absurd h hym
        · exact h
      rcases List.mem_cons.1 (hperm.mem_iff.1 hx) with h | hx1
      · subst h
        exact beforeHead _ _ _ (hL1.mem_iff.2 hy1)
      · exact beforeCons m L1 x y (hord x y hx1 hy1 hr)

theorem topoSortExists {A : Type _} (R : A → A → Prop) (Rdec : ∀ x y, Decidable (R x y))
    (hacy : ∀ x, ¬ tc R x x) (M : List A) :
    M.Nodup → ∃ L, L.Perm M ∧ (∀ x y, x ∈ M → y ∈ M → R x y → before L x y) :=
  fun hnd => WeakRvwmoTopo.topoSortAux R Rdec hacy M.length M (Nat.le_refl _) hnd

/-- Every `racyD` edge runs between members of the order.  (Not derivable from
`rdGmo` here: that route needs `grule14`, which is what we are trying to reach.) -/
theorem racyDMem (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → racyD GD x y →
    x ∈ GD.gdG.gxGmo ∧ y ∈ GD.gdG.gxGmo := by
  rintro ⟨hc, hdwf, _⟩ hR
  have hwf := hc.1
  rcases hR with (h | h | h | h | h) | hd
  · obtain ⟨_, hm, hw⟩ := h
    exact ⟨gwfMemGmo _ x hwf hm, gwfMemGmo _ y hwf (WeakRvwmoAcyc.gisWGmem _ y hw)⟩
  · exact ⟨gwfMemGmo _ x hwf (WeakRvwmoAcyc.gisWGmem _ x (grfGisW _ x y h)),
      gwfMemGmo _ y hwf (grfGmemR _ x y h)⟩
  · obtain ⟨a, v, v', h1, h2, _⟩ := h
    exact ⟨gwritesByteGmo _ x a v hwf h1, gwritesByteGmo _ y a v' hwf h2⟩
  · obtain ⟨_, a, t, v, v', h1, h2, _⟩ := h
    exact ⟨greadsByteGmo _ x a t v hwf h1, gwritesByteGmo _ y a v' hwf h2⟩
  · obtain ⟨h1, h2⟩ := gppoGmem _ x y h
    exact ⟨gwfMemGmo _ x hwf h1, gwfMemGmo _ y hwf h2⟩
  · obtain ⟨_, _, h1, h2⟩ := hdwf (x, y) hd
    exact ⟨gwfMemGmo _ x hwf (WeakRvwmoGraph.glblIsRGmem _ x h1),
      gwfMemGmo _ y hwf (WeakRvwmoGraph.glblIsWGmem _ y h2)⟩

/-- THE EXISTENCE THEOREM. -/
theorem topoExists (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x y, Decidable (racyD GD x y)) →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ L, linExtD GD L := by
  intro hcons hdec hacy
  have hnd : GD.gdG.gxGmo.Nodup := hcons.1.1.1
  obtain ⟨L, hL, hord⟩ := topoSortExists (racyD GD) hdec hacy _ hnd
  refine ⟨L, hL, ?_⟩
  intro x y hR
  obtain ⟨hx, hy⟩ := racyDMem GD x y hcons hR
  exact hord x y hx hy hR

/-! # 5. THE COROLLARY: `normalize`'s conclusion, from acyclicity alone -/

theorem normalizeOfAcyclic (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x y, Decidable (racyD GD x y)) →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GD.gdG GD'.gdG ∧
      GD'.gdDeps = GD.gdDeps ∧
      wperm pi GD.gdG GD'.gdG := by
  intro hcons hdec hacy
  obtain ⟨L, hlin⟩ := topoExists GD hcons hdec hacy
  obtain ⟨hc', h14, hr, hw⟩ := topoLinearizes GD L hcons hlin
  exact ⟨⟨retime GD.gdG L, GD.gdDeps⟩, tren GD.gdG L, hc', h14, hr, rfl, hw⟩

end Weak
