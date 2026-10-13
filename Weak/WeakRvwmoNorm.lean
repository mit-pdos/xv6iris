/-
Weak: **the exchange normalization** (route B, stage B2d).

Rocq: `iris/WeakRvwmoNorm.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§3b′, the "TERMINATION — RESOLVED" block, whose PO-MINIMAL-WITNESS discipline
this file mechanizes).  The kit it composes is `WeakRvwmoXchg` (B2a/B2c/B2b);
the model is `WeakRvwmoGraph`'s RVWMO⁻ + the dep fragment.

THE POINT.  Route B's chain starts by NORMALIZING an RVWMO⁻(+deps) consistent
graph towards `grule14`, by a sequence of ADJACENT gmo exchanges: OUTER
induction on the number of rule-14 inversions `nviol` (§2); pick `w`, the
gmo-MINIMAL violating write, and `e`, its PO-MINIMAL witness; INNER induction
(`descent`, §8): descend `e` one gmo slot at a time until it sits directly
above `w`, then swap the pair itself (`gswapResolves` / `gswapwResolves`), where
the measure strictly drops.

THE ENGINE is §6's vacuity lemma `poMinNoBlocker`: a same-hart po-earlier
memory event sitting gmo-between `w` and `e` would itself be a witness of `w`,
contradicting `e`'s po-minimality.

WHAT IS LEFT OVER — the three KILL configurations (§5), explicit hypotheses
of `normalize`, discharged later by B2e: `killK1` (`e` a read whose cross-hart
rf-source sits gmo-in the interval), `killK2` (`e` a write and an interval
event reads one of `e`'s bytes at an older write index), `killK3` (`e` a write
and a cross-hart same-byte write sits gmo-in the interval).  Each kill
quantifies over every `GD'` with `gdEquiv GD GD'` (same rows and write
messages modulo the write-index renaming, still consistent with the same dep
fragment), because the kill configurations arise at INTERMEDIATE graphs of the
exchange chain and cannot be pulled back to `GD`.  `lbgdKillK1False` shows K1
is a real obligation: the LB non-collapse witness refutes it.

THE OUTPUT correspondence: `rowsRel π` (same image, same rows up to renaming
every read's `ts` entries by `π`, `π 0 = 0`) and `wperm π` (`π` injective,
`gwriteAt G' (π t) = gwriteAt G t`, same write count).

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The four Rocq
   names of this file in `notes/weak-port-dupnames.json` (`gmem_dec`,
   `glbl_is_dec`, `gpo_dec`, `gmo_lt_dec`) are FILE-QUALIFIED
   (`WeakRvwmoNorm.gmemDec`, …).  The `WeakRvwmoGraph` duplicates used are
   referred to qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `f <$> l` ↦ `l.map f`, `mjoin` ↦ `List.flatten`, `seq 0 n` ↦
   `List.range' 0 n`, `default [] o` ↦ `o.getD []`, `is_Some o` ↦
   `o.isSome = true`, `NoDup` ↦ `List.Nodup`, `⊆+`/`≡ₚ` ↦
   `List.Subperm`/`List.Perm`).
3. FILTERS (the `StdppList` shim convention): `filter_length_le`/`_lt`/
   `filter_pos`'s `P`, `Q` with `Decision` instances are Boolean predicates
   `p`, `q` (`P x` ↦ `p x = true`, `¬ P x` ↦ `p x = false`); `nviol` and the
   two filters of `normalizeAux` filter by `decide` of the (local) decidability
   instances.
4. The `Local Instance`s are `local instance`s; `gpo_dec`/`gmo_lt_dec`/
   `gviol_dec`/`violp_dec` are built by `unfold; infer_instance`.
5. `rows_rel_is_Some` (an `↔` of `is_Some`) is stated as an `↔` of
   `isSome = true`.
6. Rocq's `Section descent` (contexts `GD0 HK1 HK2 HK3`) is flattened:
   `descent` takes them as its first four arguments (as Rocq's section
   closing does).
7. `lbgd_kill_K1_false`'s closed `vm_compute` side conditions are `decide`.
8. D35-fix ([OWN.54]; `WeakRvwmoGraph` deviation 7): the Lean-only `lblRenRcsc` (moved here
   from `CatLinHull`) sits beside `lblRenAq`/`lblRenRl`, BELOW `WeakRvwmoAcyc.rowsRelGppo`,
   which now rewrites `gppo`'s `grcsc` arm with it.

**Name map** (Rocq → Lean): `filter_length_le` ↦ `filterLengthLe`;
`filter_length_lt` ↦ `filterLengthLt`; `filter_pos` ↦ `filterPos`;
`list_min_by` ↦ `listMinBy`; `nrow`; `gevs'`; `elem_of_gevs'` ↦
`elemOfGevs'`; `gpairs`; `elem_of_gpairs` ↦ `elemOfGpairs`; `gmem_dec` ↦
`WeakRvwmoNorm.gmemDec`; `glbl_is_dec` ↦ `WeakRvwmoNorm.glblIsDec`; `gpo_dec`
↦ `WeakRvwmoNorm.gpoDec`; `gmo_lt_dec` ↦ `WeakRvwmoNorm.gmoLtDec`;
`gviol_dec` ↦ `gviolDec`; `violp`; `violp_dec` ↦ `violpDec`; `nviol`;
`gviol_gpairs` ↦ `gviolGpairs`; `nviol_zero` ↦ `nviolZero`; `nviol_le` ↦
`nviolLe`; `nviol_lt` ↦ `nviolLt`; `fmap_id_gen` ↦ `fmapIdGen`;
`fmap_fmap_gen` ↦ `fmapFmapGen`; `lbl_ren` ↦ `lblRen`; `lbl_ren_tswap` ↦
`lblRenTswap`; `lbl_ren_id` ↦ `lblRenId`; `lbl_ren_comp` ↦ `lblRenComp`;
`lbl_ren_ext` ↦ `lblRenExt`; `row_ren_id` ↦ `rowRenId`; `row_ren_comp` ↦
`rowRenComp`; `prog_ren_id` ↦ `progRenId`; `prog_ren_comp` ↦ `progRenComp`;
`lbl_ren_is_r`/`_is_w`/`_is_mem`/`_aq`/`_rl`/`_cls`/`_wr`/`_rd` ↦
`lblRenIsR`/`lblRenIsW`/`lblRenIsMem`/`lblRenAq`/`lblRenRl`/`lblRenCls`/
`lblRenWr`/`lblRenRd`; `rows_rel` ↦ `rowsRel`; `rows_rel_img`/`_zero`/
`_nharts`/`_row`/`_nrow`/`_lbl`/`_is_Some`/`_glbl_is`/`_gis_w`/`_gmem`/`_gpo`/
`_wrb`/`_rdb`/`_gevs`/`_gpairs`/`_refl`/`_trans` ↦ `rowsRelImg`/`rowsRelZero`/
`rowsRelNharts`/`rowsRelRow`/`rowsRelNrow`/`rowsRelLbl`/`rowsRelIsSome`/
`rowsRelGlblIs`/`rowsRelGisW`/`rowsRelGmem`/`rowsRelGpo`/`rowsRelWrb`/
`rowsRelRdb`/`rowsRelGevs`/`rowsRelGpairs`/`rowsRelRefl`/`rowsRelTrans`;
`wperm`; `wperm_refl`/`_trans`/`_gwix`/`_range`/`_surj` ↦ `wpermRefl`/
`wpermTrans`/`wpermGwix`/`wpermRange`/`wpermSurj`; `rows_rel_gswap` ↦
`rowsRelGswap`; `wperm_gswap_hi` ↦ `wpermGswapHi`; `wperm_gswap_lo` ↦
`wpermGswapLo`; `rows_rel_gswapw` ↦ `rowsRelGswapw`; `wperm_gswapw` ↦
`wpermGswapw`; `gd_equiv` ↦ `gdEquiv`; `gd_equiv_refl` ↦ `gdEquivRefl`;
`gd_equiv_trans` ↦ `gdEquivTrans`; `kill_K1`/`_K2`/`_K3` ↦ `killK1`/`killK2`/
`killK3`; `lbgd_kill_K1_false` ↦ `lbgdKillK1False`; `po_min_no_blocker` ↦
`poMinNoBlocker`; `po_min_no_gppo` ↦ `poMinNoGppo`; `po_min_no_gpo` ↦
`poMinNoGpo`; `po_min_no_dep` ↦ `poMinNoDep`; `gpos_gmo_eq` ↦ `gposGmoEq`;
`gmo_lt_gmo_eq` ↦ `gmoLtGmoEq`; `swap_invariant` ↦ `swapInvariant`;
`descent`; `normalize_aux` ↦ `normalizeAux`; `normalize`.

**Not ported:** nothing.
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. A GENERIC LIST KIT: filter counts and minima -/

theorem filterLengthLe {A : Type _} (p q : A → Bool) (l : List A) :
    (∀ y, p y = true → q y = true) → (l.filter p).length ≤ (l.filter q).length := by
  intro hpq
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, hpq a hp] <;> omega
    · by_cases hq : q a = true <;> simp [hp, hq] <;> omega

theorem filterLengthLt {A : Type _} (p q : A → Bool) (l : List A) (x : A) :
    (∀ y, p y = true → q y = true) → x ∈ l → q x = true → p x = false →
    (l.filter p).length < (l.filter q).length := by
  intro hpq hx hqx hpx
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · have := filterLengthLe p q l hpq
      simp [hpx, hqx] <;> omega
    · have := ih hx'
      simp only [List.filter_cons]
      by_cases hp : p a = true
      · simp [hp, hpq a hp] <;> omega
      · by_cases hq : q a = true <;> simp [hp, hq] <;> omega

theorem filterPos {A : Type _} (p : A → Bool) (l : List A) (x : A) :
    x ∈ l → p x = true → 0 < (l.filter p).length := by
  intro hx hpx
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨hx, hpx⟩)

/-- A non-empty list has an element of minimal key. -/
theorem listMinBy {A : Type _} (f : A → Nat) (l : List A) :
    l ≠ [] → ∃ y, y ∈ l ∧ ∀ z, z ∈ l → f y ≤ f z := by
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    cases l with
    | nil =>
      refine ⟨a, by simp, fun z hz => ?_⟩
      rw [List.mem_singleton] at hz
      subst hz
      exact Nat.le_refl _
    | cons b l' =>
      obtain ⟨y, hy, hmin⟩ := ih (by simp)
      by_cases hle : f a ≤ f y
      · refine ⟨a, by simp, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact Nat.le_refl _
        · have := hmin z hz
          omega
      · refine ⟨y, List.mem_cons_of_mem a hy, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · omega
        · exact hmin z hz

/-! # 2. THE MEASURE: the number of rule-14 inversions -/

def nrow (G : Gexec) (i : Nat) : Nat := (G.gxProg[i]?.getD []).length

def gevs' (G : Gexec) : List Geid :=
  ((List.range' 0 G.gxProg.length).map
    (fun i => (List.range' 0 (nrow G i)).map (fun k => (i, k)))).flatten

theorem elemOfGevs' (G : Gexec) (e : Geid) : (gxLbl G e).isSome = true → e ∈ gevs' G := by
  intro hs
  obtain ⟨l, hl⟩ := someOfIsSome hs
  unfold gxLbl at hl
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at hl; simp at hl
  | some p =>
    rw [hp] at hl
    change p[e.2]? = some l at hl
    have h1 : e.1 < G.gxProg.length := lookup_lt_Some hp
    have h2 : e.2 < p.length := lookup_lt_Some hl
    have hn : nrow G e.1 = p.length := by simp [nrow, hp]
    unfold gevs'
    rw [List.mem_flatten]
    refine ⟨(List.range' 0 (nrow G e.1)).map (fun k => (e.1, k)), ?_, ?_⟩
    · rw [List.mem_map]
      refine ⟨e.1, ?_, rfl⟩
      rw [List.mem_range'_1]
      exact ⟨by omega, by omega⟩
    · rw [List.mem_map]
      refine ⟨e.2, ?_, rfl⟩
      rw [List.mem_range'_1]
      exact ⟨by omega, by omega⟩

def gpairs (G : Gexec) : List (Geid × Geid) :=
  ((gevs' G).map (fun e => (gevs' G).map (fun w => (e, w)))).flatten

theorem elemOfGpairs (G : Gexec) (e w : Geid) :
    e ∈ gevs' G → w ∈ gevs' G → (e, w) ∈ gpairs G := by
  intro he hw
  unfold gpairs
  rw [List.mem_flatten]
  exact ⟨(gevs' G).map (fun w' => (e, w')), List.mem_map.2 ⟨e, he, rfl⟩,
    List.mem_map.2 ⟨w, hw, rfl⟩⟩

/-! ## 2.1 Decidability of the model's predicates -/

local instance WeakRvwmoNorm.gmemDec (G : Gexec) (e : Geid) : Decidable (gmem G e) :=
  match h : gxLbl G e with
  | some l =>
    if hm : lbIsMem l = true then isTrue ⟨l, h, hm⟩
    else isFalse (fun ⟨l', hl', hm'⟩ => hm (by rw [h] at hl'; cases hl'; exact hm'))
  | none => isFalse (fun ⟨l', hl', _⟩ => by rw [h] at hl'; cases hl')

local instance WeakRvwmoNorm.glblIsDec (G : Gexec) (e : Geid) (P : Lbl → Bool) :
    Decidable (glblIs G e P) :=
  match h : gxLbl G e with
  | some l =>
    if hm : P l = true then isTrue ⟨l, h, hm⟩
    else isFalse (fun ⟨l', hl', hm'⟩ => hm (by rw [h] at hl'; cases hl'; exact hm'))
  | none => isFalse (fun ⟨l', hl', _⟩ => by rw [h] at hl'; cases hl')

local instance WeakRvwmoNorm.gpoDec (G : Gexec) (e1 e2 : Geid) :
    Decidable (WeakRvwmoGraph.gpo G e1 e2) := by
  unfold WeakRvwmoGraph.gpo; infer_instance

local instance WeakRvwmoNorm.gmoLtDec (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

local instance gviolDec (G : Gexec) (e w : Geid) : Decidable (gviol G e w) := by
  unfold gviol; infer_instance

/-! ## 2.2 The count -/

def violp (G : Gexec) (p : Geid × Geid) : Prop := gviol G p.1 p.2

local instance violpDec (G : Gexec) (p : Geid × Geid) : Decidable (violp G p) := by
  unfold violp; infer_instance

def nviol (G : Gexec) : Nat := ((gpairs G).filter (fun p => decide (violp G p))).length

/-- A violating pair is one of the enumerated pairs. -/
theorem gviolGpairs (G : Gexec) (e w : Geid) : gviol G e w → (e, w) ∈ gpairs G := by
  rintro ⟨_, ⟨l, hl, _⟩, ⟨lw, hlw, _⟩, _⟩
  exact elemOfGpairs G e w (elemOfGevs' G e (by simp [hl])) (elemOfGevs' G w (by simp [hlw]))

theorem nviolZero (G : Gexec) : gwf G → nviol G = 0 → grule14 G := by
  intro hwf h0
  apply gviolGrule14 G hwf
  intro e w hv
  have := filterPos (fun p => decide (violp G p)) (gpairs G) (e, w) (gviolGpairs G e w hv)
    (by simp only [decide_eq_true_eq]; exact hv)
  unfold nviol at h0
  omega

theorem nviolLe (G G' : Gexec) :
    gpairs G' = gpairs G → (∀ e w, gviol G' e w → gviol G e w) → nviol G' ≤ nviol G := by
  intro hp hmono
  unfold nviol
  rw [hp]
  apply filterLengthLe
  intro ⟨e, w⟩ h
  simp only [decide_eq_true_eq] at h ⊢
  exact hmono e w h

theorem nviolLt (G G' : Gexec) (e w : Geid) :
    gpairs G' = gpairs G → (∀ e' w', gviol G' e' w' → gviol G e' w') →
    gviol G e w → ¬ gviol G' e w → nviol G' < nviol G := by
  intro hp hmono hv hnv
  unfold nviol
  rw [hp]
  refine filterLengthLt _ _ _ (e, w) ?_ (gviolGpairs G e w hv)
    (by simp only [decide_eq_true_eq]; exact hv)
    (by simp only [decide_eq_false_iff_not]; exact hnv)
  intro ⟨e', w'⟩ h
  simp only [decide_eq_true_eq] at h ⊢
  exact hmono e' w' h

/-! # 3. THE OUTPUT CORRESPONDENCE: `rowsRel` and `wperm` -/

/-! ## 3.1 Renaming a label's `ts` entries -/

theorem fmapIdGen {A : Type _} (l : List A) : (l.map fun x => x) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

theorem fmapFmapGen {A B C : Type _} (f : A → B) (g : B → C) (l : List A) :
    (l.map f).map g = l.map (fun x => g (f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

def lblRen (π : Nat → Nat) (l : Lbl) : Lbl :=
  match l with
  | LLoad aq base ts vs => LLoad aq base (ts.map π) vs
  | LStore rl base vs k => LStore rl base vs k
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LRmw aq rl base ts rvs wvs k => LRmw aq rl base (ts.map π) rvs wvs k
  | LIo kd base vs => LIo kd base vs

theorem lblRenTswap (k1 : Nat) (l : Lbl) : lblRen (tswap k1) l = lblTswap k1 l := by
  cases l <;> rfl

theorem lblRenId (l : Lbl) : lblRen (fun t => t) l = l := by
  cases l <;> simp only [lblRen, fmapIdGen]

theorem lblRenComp (π1 π2 : Nat → Nat) (l : Lbl) :
    lblRen π2 (lblRen π1 l) = lblRen (fun t => π2 (π1 t)) l := by
  cases l <;> simp only [lblRen, fmapFmapGen]

theorem lblRenExt (π1 π2 : Nat → Nat) (l : Lbl) :
    (∀ t, π1 t = π2 t) → lblRen π1 l = lblRen π2 l := by
  intro h
  have : π1 = π2 := funext h
  rw [this]

theorem rowRenId (r : List Lbl) : r.map (lblRen fun t => t) = r := by
  induction r with
  | nil => rfl
  | cons l r ih => simp only [List.map_cons, lblRenId, ih]

theorem rowRenComp (π1 π2 π : Nat → Nat) (r : List Lbl) :
    (∀ t, π t = π2 (π1 t)) → (r.map (lblRen π1)).map (lblRen π2) = r.map (lblRen π) := by
  intro h
  have hl : ∀ l, lblRen π2 (lblRen π1 l) = lblRen π l := fun l => by
    rw [lblRenComp]
    exact lblRenExt _ _ l (fun t => (h t).symm)
  induction r with
  | nil => rfl
  | cons l r ih => simp only [List.map_cons, hl, ih]

theorem progRenId (p : List (List Lbl)) :
    p.map (fun row : List Lbl => row.map (lblRen fun t => t)) = p := by
  induction p with
  | nil => rfl
  | cons r p ih => rw [List.map_cons, rowRenId, ih]

theorem progRenComp (π1 π2 π : Nat → Nat) (p : List (List Lbl)) :
    (∀ t, π t = π2 (π1 t)) →
    (p.map (fun row : List Lbl => row.map (lblRen π1))).map
        (fun row : List Lbl => row.map (lblRen π2))
      = p.map (fun row : List Lbl => row.map (lblRen π)) := by
  intro h
  induction p with
  | nil => rfl
  | cons r p ih => simp only [List.map_cons, rowRenComp π1 π2 π r h, ih]

theorem lblRenIsR (π : Nat → Nat) (l : Lbl) : lbIsR (lblRen π l) = lbIsR l := by cases l <;> rfl
theorem lblRenIsW (π : Nat → Nat) (l : Lbl) : lbIsW (lblRen π l) = lbIsW l := by cases l <;> rfl
theorem lblRenIsMem (π : Nat → Nat) (l : Lbl) : lbIsMem (lblRen π l) = lbIsMem l := by
  cases l <;> rfl
theorem lblRenAq (π : Nat → Nat) (l : Lbl) : lbAq (lblRen π l) = lbAq l := by cases l <;> rfl
theorem lblRenRl (π : Nat → Nat) (l : Lbl) : lbRl (lblRen π l) = lbRl l := by cases l <;> rfl
theorem lblRenRcsc (π : Nat → Nat) (l : Lbl) : lbRcsc (lblRen π l) = lbRcsc l := by
  simp only [lbRcsc, lblRenAq, lblRenRl]
theorem lblRenCls (π : Nat → Nat) (l : Lbl) : lbCls (lblRen π l) = lbCls l := by cases l <;> rfl
theorem lblRenWr (π : Nat → Nat) (l : Lbl) : lbWr (lblRen π l) = lbWr l := by cases l <;> rfl
theorem lblRenRd (π : Nat → Nat) (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd l = some (base, ts, vs) → lbRd (lblRen π l) = some (base, ts.map π, vs) := by
  intro h
  cases l <;> simp_all [lblRen, lbRd]

/-! ## 3.2 `rowsRel`: the SAME OBSERVABLES, modulo the renaming -/

def rowsRel (π : Nat → Nat) (G G' : Gexec) : Prop :=
  G'.gxImg = G.gxImg ∧
  G'.gxProg = G.gxProg.map (fun row : List Lbl => row.map (lblRen π)) ∧
  π 0 = 0

theorem rowsRelImg (π : Nat → Nat) (G G' : Gexec) : rowsRel π G G' → G'.gxImg = G.gxImg :=
  fun h => h.1

theorem rowsRelZero (π : Nat → Nat) (G G' : Gexec) : rowsRel π G G' → π 0 = 0 :=
  fun h => h.2.2

/-- Same number of harts. -/
theorem rowsRelNharts (π : Nat → Nat) (G G' : Gexec) :
    rowsRel π G G' → G'.gxProg.length = G.gxProg.length := by
  intro h
  rw [h.2.1, List.length_map]

/-- Same row, renamed. -/
theorem rowsRelRow (π : Nat → Nat) (G G' : Gexec) (i : Nat) (r : List Lbl) :
    rowsRel π G G' → G.gxProg[i]? = some r → G'.gxProg[i]? = some (r.map (lblRen π)) := by
  intro h hr
  simp [h.2.1, hr]

theorem rowsRelNrow (π : Nat → Nat) (G G' : Gexec) (i : Nat) :
    rowsRel π G G' → nrow G' i = nrow G i := by
  intro h
  unfold nrow
  rw [h.2.1, List.getElem?_map]
  cases G.gxProg[i]? <;> simp

/-- THE EVENT-LEVEL EQUATION. -/
theorem rowsRelLbl (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → gxLbl G' e = (gxLbl G e).map (lblRen π) := by
  intro h
  unfold gxLbl
  rw [h.2.1, List.getElem?_map]
  cases G.gxProg[e.1]? with
  | none => rfl
  | some r => simp

theorem rowsRelIsSome (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → ((gxLbl G' e).isSome = true ↔ (gxLbl G e).isSome = true) := by
  intro h
  rw [rowsRelLbl π G G' e h]
  simp

theorem rowsRelGlblIs (π : Nat → Nat) (G G' : Gexec) (e : Geid) (P : Lbl → Bool) :
    rowsRel π G G' → (∀ l, P (lblRen π l) = P l) → (glblIs G' e P ↔ glblIs G e P) := by
  intro hr hP
  unfold glblIs
  rw [rowsRelLbl π G G' e hr]
  constructor
  · rintro ⟨l, hl, hPl⟩
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact ⟨l0, hl0, by rw [← hP]; exact hPl⟩
  · rintro ⟨l, hl, hPl⟩
    exact ⟨lblRen π l, by simp [hl], by rw [hP]; exact hPl⟩

theorem rowsRelGisW (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → gisW G' e = gisW G e := by
  intro hr
  unfold gisW
  rw [rowsRelLbl π G G' e hr]
  cases gxLbl G e with
  | none => rfl
  | some l => simp [lblRenIsW]

theorem rowsRelGmem (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → (gmem G' e ↔ gmem G e) :=
  fun hr => rowsRelGlblIs π G G' e lbIsMem hr (lblRenIsMem π)

theorem rowsRelGpo (π : Nat → Nat) (G G' : Gexec) (e1 e2 : Geid) :
    rowsRel π G G' → (WeakRvwmoGraph.gpo G' e1 e2 ↔ WeakRvwmoGraph.gpo G e1 e2) := by
  intro hr
  have h1 : (gxLbl G' e1).isSome = (gxLbl G e1).isSome := by
    rw [rowsRelLbl π G G' e1 hr]; simp
  have h2 : (gxLbl G' e2).isSome = (gxLbl G e2).isSome := by
    rw [rowsRelLbl π G G' e2 hr]; simp
  simp only [WeakRvwmoGraph.gpo, h1, h2]

/-- Write footprints and values are UNTOUCHED. -/
theorem rowsRelWrb (π : Nat → Nat) (G G' : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    rowsRel π G G' → (gwritesByte G' e a v ↔ gwritesByte G e a v) := by
  intro hr
  unfold gwritesByte
  rw [rowsRelLbl π G G' e hr]
  constructor
  · rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [lblRenWr] at hwr
    exact ⟨l0, base, vs, j, hl0, hwr, hv, ha⟩
  · rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    exact ⟨lblRen π l, base, vs, j, by simp [hl], by rw [lblRenWr]; exact hwr, hv, ha⟩

/-- Read footprints and values are untouched; the `ts` entry `t` becomes `π t`. -/
theorem rowsRelRdb (π : Nat → Nat) (G G' : Gexec) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    rowsRel π G G' → greadsByte G e a t v → greadsByte G' e a (π t) v := by
  rintro hr ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  refine ⟨lblRen π l, base, ts.map π, vs, j, ?_, lblRenRd π l base ts vs hrd, ?_, hv, ha⟩
  · simp [rowsRelLbl π G G' e hr, hl]
  · simp [ht]

/-- The measure's enumeration is LITERALLY the same list. -/
theorem rowsRelGevs (π : Nat → Nat) (G G' : Gexec) : rowsRel π G G' → gevs' G' = gevs' G := by
  intro hr
  have hn : ∀ i, nrow G' i = nrow G i := fun i => rowsRelNrow π G G' i hr
  unfold gevs'
  rw [rowsRelNharts π G G' hr]
  simp only [hn]

theorem rowsRelGpairs (π : Nat → Nat) (G G' : Gexec) : rowsRel π G G' → gpairs G' = gpairs G := by
  intro hr
  unfold gpairs
  rw [rowsRelGevs π G G' hr]

/-! ## 3.3 Composition -/

theorem rowsRelRefl (G : Gexec) : rowsRel (fun t => t) G G :=
  ⟨rfl, (progRenId _).symm, rfl⟩

theorem rowsRelTrans (π1 π2 π : Nat → Nat) (G1 G2 G3 : Gexec) :
    rowsRel π1 G1 G2 → rowsRel π2 G2 G3 → (∀ t, π t = π2 (π1 t)) → rowsRel π G1 G3 := by
  rintro ⟨hi1, hp1, hz1⟩ ⟨hi2, hp2, hz2⟩ hpi
  refine ⟨by rw [hi2, hi1], ?_, by rw [hpi, hz1, hz2]⟩
  rw [hp2, hp1]
  exact progRenComp π1 π2 π _ hpi

/-! ## 3.4 `wperm`: the write MESSAGES are preserved under the renaming -/

def wperm (π : Nat → Nat) (G G' : Gexec) : Prop :=
  (∀ t1 t2, π t1 = π t2 → t1 = t2) ∧
  (∀ t, gwriteAt G' (π t) = gwriteAt G t) ∧
  (gwrites G').length = (gwrites G).length

theorem wpermRefl (G : Gexec) : wperm (fun t => t) G G :=
  ⟨fun _ _ h => h, fun _ => rfl, rfl⟩

theorem wpermTrans (π1 π2 π : Nat → Nat) (G1 G2 G3 : Gexec) :
    wperm π1 G1 G2 → wperm π2 G2 G3 → (∀ t, π t = π2 (π1 t)) → wperm π G1 G3 := by
  rintro ⟨hi1, hw1, hl1⟩ ⟨hi2, hw2, hl2⟩ hpi
  refine ⟨fun t1 t2 heq => ?_, fun t => by rw [hpi, hw2, hw1], by rw [hl2, hl1]⟩
  rw [hpi t1, hpi t2] at heq
  exact hi1 _ _ (hi2 _ _ heq)

/-! ## 3.5 The bijection statement, derived -/

theorem wpermGwix (π : Nat → Nat) (G G' : Gexec) (w : Geid) :
    G'.gxGmo.Nodup → wperm π G G' → w ∈ gwrites G → gwix G' w = π (gwix G w) := by
  rintro hnd ⟨_, hw, _⟩ hin
  have hat : gwriteAt G' (π (gwix G w)) = some w := by
    rw [hw]; exact gwriteAtGwix G w hin
  exact (gwriteAtInv G' _ w hnd hat).2

theorem wpermRange (π : Nat → Nat) (G G' : Gexec) (t : Nat) :
    G'.gxGmo.Nodup → wperm π G G' → 0 < t → t ≤ (gwrites G).length →
    0 < π t ∧ π t ≤ (gwrites G).length := by
  rintro hnd ⟨hinj, hw, hlen⟩ ht hle
  obtain _ | i := t
  · omega
  have hi : i < (gwrites G).length := by omega
  obtain ⟨x, hx⟩ := someOfIsSome (lookup_lt_is_Some_2 hi)
  have hat : gwriteAt G (i + 1) = some x := hx
  rw [← hw] at hat
  cases hpi : π (i + 1) with
  | zero => rw [hpi] at hat; simp [gwriteAt] at hat
  | succ j =>
    rw [hpi] at hat
    have := lookup_lt_Some (show (gwrites G')[j]? = some x from hat)
    exact ⟨by omega, by omega⟩

/-- SURJECTIVITY, by pigeonhole: an injective self-map of `{1..N}` is onto. -/
theorem wpermSurj (π : Nat → Nat) (G G' : Gexec) (t' : Nat) :
    G'.gxGmo.Nodup → wperm π G G' → 0 < t' → t' ≤ (gwrites G).length →
    ∃ t, 0 < t ∧ t ≤ (gwrites G).length ∧ π t = t' := by
  intro hnd hwp ht' hle'
  have hinj := hwp.1
  have hsub : List.Subperm ((List.range' 1 (gwrites G).length).map π)
      (List.range' 1 (gwrites G).length) := by
    apply NoDup_submseteq
    · exact NoDup_fmap_2_strong (fun x y _ _ h => hinj x y h) NoDup_seq
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_range'_1] at ht ⊢
      have := wpermRange π G G' t hnd hwp (by omega) (by omega)
      exact ⟨by omega, by omega⟩
  have hperm := submseteq_length_Permutation hsub (by simp)
  have hin : t' ∈ (List.range' 1 (gwrites G).length).map π := by
    rw [hperm.mem_iff, List.mem_range'_1]
    exact ⟨by omega, by omega⟩
  obtain ⟨t, ht, heq⟩ := List.mem_map.1 hin
  rw [List.mem_range'_1] at ht
  exact ⟨t, by omega, by omega, heq⟩

/-! # 4. THE MOVES' CORRESPONDENCES -/

theorem rowsRelGswap (G : Gexec) (n : Nat) : rowsRel (fun t => t) G (gswap G n) :=
  rowsRelRefl G

theorem wpermGswapHi (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r → gisW G r = false →
    wperm (fun t => t) G (gswap G n) := by
  intro hx hr hnw
  exact ⟨fun _ _ h => h, fun t => gswapGwriteAt G n x r t hx hr hnw,
    by rw [gswapGwrites G n x r hx hr hnw]⟩

theorem wpermGswapLo (G : Gexec) (n : Nat) (x e : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e → gisW G x = false →
    wperm (fun t => t) G (gswap G n) := by
  intro hx he hnw
  exact ⟨fun _ _ h => h, fun t => gswapGwriteAtLo G n x e t hx he hnw,
    by rw [gswapGwritesLo G n x e hx he hnw]⟩

theorem rowsRelGswapw (G : Gexec) (n k1 : Nat) : 0 < k1 → rowsRel (tswap k1) G (gswapw G n k1) := by
  intro hk
  refine ⟨rfl, ?_, tswapZero k1 hk⟩
  show G.gxProg.map (fun row => row.map (lblTswap k1))
    = G.gxProg.map (fun row => row.map (lblRen (tswap k1)))
  have : lblTswap k1 = lblRen (tswap k1) := funext fun l => (lblRenTswap k1 l).symm
  rw [this]

theorem wpermGswapw (G : Gexec) (n : Nat) (x e : Geid) :
    G.gxGmo.Nodup →
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = true → gisW G e = true →
    wperm (tswap (gwix G x)) G (gswapw G n (gwix G x)) := by
  intro hnd hx he hwx hwe
  obtain ⟨m, hm, hsm, hkx, _, hgws⟩ := gswapwWritesKit G n (gwix G x) x e hnd hx he hwx hwe
  rw [hkx] at hgws ⊢
  refine ⟨tswapInj (m + 1), fun t => ?_, ?_⟩
  · rw [gswapwGwriteAt G n x e m hm hsm hgws, tswapInvol]
  · rw [hgws]
    exact lswapLength _ m x e hm hsm

/-! # 5. THE KILL INTERFACE — B2e's three obligations -/

def gdEquiv (GD GD' : Gdexec) : Prop :=
  ∃ π, rowsRel π GD.gdG GD'.gdG ∧
       wperm π GD.gdG GD'.gdG ∧
       GD'.gdDeps = GD.gdDeps ∧
       rvwmoMinusDepsConsistent GD'

theorem gdEquivRefl (GD : Gdexec) : rvwmoMinusDepsConsistent GD → gdEquiv GD GD :=
  fun hc => ⟨fun t => t, rowsRelRefl _, wpermRefl _, rfl, hc⟩

theorem gdEquivTrans (GD1 GD2 GD3 : Gdexec) :
    gdEquiv GD1 GD2 → gdEquiv GD2 GD3 → gdEquiv GD1 GD3 := by
  rintro ⟨π1, hr1, hw1, hd1, _⟩ ⟨π2, hr2, hw2, hd2, hc2⟩
  exact ⟨fun t => π2 (π1 t), rowsRelTrans _ _ _ _ _ _ hr1 hr2 (fun _ => rfl),
    wpermTrans _ _ _ _ _ _ hw1 hw2 (fun _ => rfl), by rw [hd2, hd1], hc2⟩

/-- K1: the PO-MINIMAL WITNESS is a READ, and its CROSS-HART rf-source sits
gmo-strictly inside the descent interval `(w, e)`. -/
def killK1 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (w0 : Geid),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = false →
    greadsByte GD'.gdG e a t v →
    gwriteAt GD'.gdG t = some w0 →
    w0.1 ≠ e.1 →
    gmoLt GD'.gdG w w0 → gmoLt GD'.gdG w0 e →
    False

/-- K2: the PO-MINIMAL WITNESS is a WRITE, and an event `z` sitting
gmo-strictly inside the interval reads one of `e`'s bytes at an OLDER write
index. -/
def killK2 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (t : Nat) (v v' : BitVec 8),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = true →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    greadsByte GD'.gdG z a t v →
    gwritesByte GD'.gdG e a v' →
    t < gwix GD'.gdG e →
    False

/-- K3: the PO-MINIMAL WITNESS is a WRITE, and a CROSS-HART SAME-BYTE write sits
gmo-strictly inside the interval. -/
def killK3 (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (v v' : BitVec 8),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = true →
    gisW GD'.gdG z = true → z.1 ≠ e.1 →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    gwritesByte GD'.gdG z a v → gwritesByte GD'.gdG e a v' →
    False

/-! ## 5.1 THE KILLS ARE REAL OBLIGATIONS — the LB non-collapse check

In `lbg` the gmo-minimal violating write is hart 0's store `(0,1)`, its only
witness is hart 0's load `(0,0)`, and the event the load must descend past is
hart 1's store `(1,1)` — exactly the load's own cross-hart rf-source. -/

theorem lbgdKillK1False : ¬ killK1 lbgd := by
  intro hK
  refine hK lbgd (gdEquivRefl lbgd lbGraphDepsConsistent) (0, 1) (0, 0) 0 2 b1 (1, 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the violation
    refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ?_, ?_⟩ <;> decide
  · -- `(0,1)` is gmo-minimal: it sits at gmo position 0
    rintro e' w' _ ⟨_, _, hlt⟩
    have h0 : gpos lbgd.gdG (0, 1) = 0 := by decide
    omega
  · -- `(0,0)` is po-minimal: it sits at po position 0
    intro e' _ hlt
    exact Nat.not_lt_zero _ hlt
  · -- the witness is a read
    rfl
  · -- it reads byte 0 at write index 2
    exact ⟨LLoad false 0 [2] [b1], 0, [2], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
  · -- write index 2 is hart 1's store
    decide
  · -- which is CROSS-HART
    decide
  · -- and sits gmo-above the violating write ...
    refine ⟨?_, ?_, ?_⟩ <;> decide
  · -- ... and gmo-below the witness
    refine ⟨?_, ?_, ?_⟩ <;> decide

/-! # 6. THE VACUITY LEMMA — the descent's engine -/

theorem poMinNoBlocker (G : Gexec) (w e z : Geid) :
    gviol G e w →
    (∀ e', gviol G e' w → ¬ e'.2 < e.2) →
    gmem G z → gmoLt G w z → z.1 = e.1 → z.2 < e.2 → False := by
  intro hv hpmin hz hmo hag hlt
  obtain ⟨⟨hag', hlt', _, hsw⟩, _, hw, _⟩ := hv
  have hsz : (gxLbl G z).isSome = true := by
    obtain ⟨l, hl, _⟩ := hz
    simp [hl]
  exact hpmin z ⟨⟨hag.trans hag', by omega, hsz, hsw⟩, hz, hw, hmo⟩ hlt

theorem poMinNoGppo (G : Gexec) (w e z : Geid) :
    gviol G e w →
    (∀ e', gviol G e' w → ¬ e'.2 < e.2) →
    gmem G z → gmoLt G w z → ¬ gppo G z e := by
  intro hv hpmin hz hmo hppo
  obtain ⟨hag, hlt⟩ := gppoPoLt G z e hppo
  exact poMinNoBlocker G w e z hv hpmin hz hmo hag hlt

theorem poMinNoGpo (G : Gexec) (w e z : Geid) :
    gviol G e w →
    (∀ e', gviol G e' w → ¬ e'.2 < e.2) →
    gmem G z → gmoLt G w z → ¬ WeakRvwmoGraph.gpo G z e := by
  rintro hv hpmin hz hmo ⟨hag, hlt, _, _⟩
  exact poMinNoBlocker G w e z hv hpmin hz hmo hag hlt

/-- A dep edge INTO the descending witness is refused the same way. -/
theorem poMinNoDep (GD : Gdexec) (w e z : Geid) :
    gdepsWf GD.gdG GD.gdDeps →
    gviol GD.gdG e w →
    (∀ e', gviol GD.gdG e' w → ¬ e'.2 < e.2) →
    gmem GD.gdG z → gmoLt GD.gdG w z → (z, e) ∉ GD.gdDeps := by
  intro hdwf hv hpmin hz hmo hdep
  obtain ⟨hag, hlt, _, _⟩ := hdwf (z, e) hdep
  exact poMinNoBlocker GD.gdG w e z hv hpmin hz hmo hag hlt

/-! # 7. ONE DESCENT STEP, ABSTRACTLY -/

theorem gposGmoEq (G1 G2 : Gexec) (e : Geid) : G1.gxGmo = G2.gxGmo → gpos G1 e = gpos G2 e := by
  intro h
  unfold gpos
  rw [h]

theorem gmoLtGmoEq (G1 G2 : Gexec) (e1 e2 : Geid) :
    G1.gxGmo = G2.gxGmo → (gmoLt G1 e1 e2 ↔ gmoLt G2 e1 e2) := by
  intro h
  simp only [gmoLt, gpos, h]

theorem swapInvariant (π : Nat → Nat) (G G' : Gexec) (w e z : Geid) (n : Nat) :
    gwf G →
    G.gxGmo[n]? = some z → G.gxGmo[n + 1]? = some e →
    rowsRel π G G' →
    G'.gxGmo = (gswap G n).gxGmo →
    (∀ e' w', gviol G' e' w' → gviol G e' w') →
    gviol G e w → gpos G w < n →
    (∀ e' w', gviol G e' w' → ¬ gmoLt G w' w) →
    (∀ e', gviol G e' w → ¬ e'.2 < e.2) →
    nviol G' ≤ nviol G ∧
    gviol G' e w ∧
    (∀ e' w', gviol G' e' w' → ¬ gmoLt G' w' w) ∧
    (∀ e', gviol G' e' w → ¬ e'.2 < e.2) ∧
    gpos G' e = n ∧ gpos G' w = gpos G w := by
  intro hwf hz he hrows hgmo hmono hv hwn hmin hpmin
  have hnd := hwf.1
  have hzne : w ≠ z := by
    intro h
    subst h
    rw [gposOfLookup G n _ hnd hz] at hwn
    omega
  obtain ⟨hpo, hme, hww, hmo⟩ := id hv
  have hwin : w ∈ G.gxGmo := hmo.1
  refine ⟨nviolLe G G' (rowsRelGpairs π G G' hrows) hmono, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (rowsRelGpo π G G' e w hrows).2 hpo
  · exact (rowsRelGmem π G G' e hrows).2 hme
  · exact (rowsRelGlblIs π G G' w lbIsW hrows (lblRenIsW π)).2 hww
  · rw [gmoLtGmoEq G' (gswap G n) w e hgmo]
    exact gswapGmoLt G n z e w e hnd hz he hmo (fun ⟨h, _⟩ => hzne h)
  · intro e' w' hv' hlt'
    rw [gmoLtGmoEq G' (gswap G n) w' w hgmo] at hlt'
    rcases gswapGmoLtInv G n z e w' w hnd hz he hlt' with hg | ⟨_, h⟩
    · exact hmin e' w' (hmono e' w' hv') hg
    · exact hzne h
  · intro e' hv'
    exact hpmin e' (hmono e' w hv')
  · rw [gposGmoEq G' (gswap G n) e hgmo]
    exact gswapGposUpper G n z e hnd hz he
  · rw [gposGmoEq G' (gswap G n) w hgmo, gswapGpos G n z e w hnd hz he hwin]
    apply sidxId <;> omega

/-! # 8. THE DESCENT

`w` is the gmo-minimal violating write and `e` its po-minimal witness.  Slide
`e` down one gmo slot at a time until it sits directly above `w`, then swap the
pair. -/

theorem descent (GD0 : Gdexec) (hK1 : killK1 GD0) (hK2 : killK2 GD0) (hK3 : killK3 GD0)
    (D : Nat) (GD : Gdexec) (w e : Geid) :
    gdEquiv GD0 GD →
    gviol GD.gdG e w →
    (∀ e' w', gviol GD.gdG e' w' → ¬ gmoLt GD.gdG w' w) →
    (∀ e', gviol GD.gdG e' w → ¬ e'.2 < e.2) →
    gpos GD.gdG e - gpos GD.gdG w ≤ D →
    ∃ GD', gdEquiv GD0 GD' ∧ nviol GD'.gdG < nviol GD.gdG := by
  induction D generalizing GD w e with
  | zero =>
    intro _ hv _ _ hd
    exfalso
    obtain ⟨_, _, _, ⟨_, _, hlt⟩⟩ := hv
    omega
  | succ D ih =>
    intro heq hv hmin hpmin hd
    obtain ⟨π, hrows0, hwp0, hdeps0, hcons⟩ := id heq
    have hc := hcons.1
    have hdwf := hcons.2.1
    have hwf := hc.1
    have hppo := hc.2.1
    have hlv := hc.2.2.1
    have hnd := hwf.1
    obtain ⟨⟨hag_ew, hlt_ew, hse, hsw⟩, hmem_e, hlw, hmo_we⟩ := id hv
    obtain ⟨hwin, hein, hposlt⟩ := id hmo_we
    have hwisw : gisW GD.gdG w = true := glblIsWGisW _ _ hlw
    have hSn : GD.gdG.gxGmo[gpos GD.gdG e]? = some e := gposElemLookup _ _ hein
    by_cases hfin : gpos GD.gdG e = gpos GD.gdG w + 1
    · -- THE FINAL SWAP: `e` is directly above `w`.
      have hn : GD.gdG.gxGmo[gpos GD.gdG w]? = some w := gposElemLookup _ _ hwin
      have hSn' : GD.gdG.gxGmo[gpos GD.gdG w + 1]? = some e := by rw [← hfin]; exact hSn
      have hnppo : ¬ gppo GD.gdG w e := by
        intro hp
        have := (gppoPoLt _ _ _ hp).2
        omega
      cases hew : gisW GD.gdG e with
      | true =>
        -- `e` a write: the (W,W) move, byte-disjoint by poloc
        have hdisj : ∀ a, (∃ v, gwritesByte GD.gdG w a v) →
            ¬ ∃ v', gwritesByte GD.gdG e a v' := by
          rintro a ⟨v, hwv⟩ ⟨v', hev⟩
          have hpl : gppo GD.gdG e w :=
            Or.inl ⟨⟨hag_ew, hlt_ew, hse, hsw⟩, a, Or.inl ⟨v', hev⟩, Or.inl ⟨v, hwv⟩⟩
          have := (hppo e w hpl).2.2
          omega
        have hdep : (w, e) ∉ GD.gdDeps := by
          intro hin
          have : w.2 < e.2 := (hdwf (w, e) hin).2.1
          omega
        have hcons' := gswapwWwDeps GD (gpos GD.gdG w) w e hcons hn hSn' hwisw hew
          hdisj hnppo hdep
        have hk : 0 < gwix GD.gdG w :=
          WeakRvwmoGraph.gwixPos _ _ (gisWGwrites _ _ hwf hsw hwisw)
        refine ⟨⟨gswapw GD.gdG (gpos GD.gdG w) (gwix GD.gdG w), GD.gdDeps⟩,
          ⟨fun t => tswap (gwix GD.gdG w) (π t), ?_, ?_, hdeps0, hcons'⟩, ?_⟩
        · exact rowsRelTrans _ _ _ _ _ _ hrows0 (rowsRelGswapw GD.gdG _ _ hk) (fun _ => rfl)
        · exact wpermTrans _ _ _ _ _ _ hwp0
            (wpermGswapw GD.gdG _ w e hnd hn hSn' hwisw hew) (fun _ => rfl)
        · have hres := (gswapwResolves GD.gdG _ w e hwf hn hSn' hwisw hew hag_ew hlt_ew).2
          refine nviolLt GD.gdG _ e w (rowsRelGpairs _ _ _ (rowsRelGswapw GD.gdG _ _ hk)) ?_ hv hres
          intro e' w' hv'
          exact gswapwViolMono GD.gdG _ (gwix GD.gdG w) w e e' w' hnd hn hSn'
            (fun hp => by have := hp.2.1; omega) hv'
      | false =>
        -- `e` a read: the read-down move
        have hnrf : ∀ a t v, greadsByte GD.gdG e a t v → gwriteAt GD.gdG t ≠ some w := by
          intro a t v hrd hsrc
          have hwb := greadSourceByte GD.gdG e a t v w hlv hrd hsrc
          have hpl : gppo GD.gdG e w :=
            Or.inl ⟨⟨hag_ew, hlt_ew, hse, hsw⟩, a, Or.inr ⟨t, v, hrd⟩, Or.inl ⟨v, hwb⟩⟩
          have := (hppo e w hpl).2.2
          omega
        have hcons' := gswapReadDownDeps GD _ w e hcons hn hSn' hew hnrf hnppo
        refine ⟨⟨gswap GD.gdG (gpos GD.gdG w), GD.gdDeps⟩, ⟨π, ?_, ?_, hdeps0, hcons'⟩, ?_⟩
        · exact rowsRelTrans _ _ _ _ _ _ hrows0 (rowsRelGswap GD.gdG _) (fun _ => rfl)
        · exact wpermTrans _ _ _ _ _ _ hwp0 (wpermGswapHi GD.gdG _ w e hn hSn' hew)
            (fun _ => rfl)
        · have hres := (gswapResolves GD.gdG _ w e hwf hn hSn' hew hwisw hag_ew hlt_ew).2
          refine nviolLt GD.gdG _ e w (rowsRelGpairs _ _ _ (rowsRelGswap GD.gdG _)) ?_ hv hres
          intro e' w' hv'
          exact gswapViolMono GD.gdG _ w e e' w' hnd hn hSn' hew hv'
    · -- AN INTERIOR SWAP: something sits between `w` and `e`.
      have hgap : gpos GD.gdG w + 1 < gpos GD.gdG e := by omega
      obtain ⟨n, hn_def⟩ : ∃ n, n = gpos GD.gdG e - 1 := ⟨_, rfl⟩
      have hSn' : GD.gdG.gxGmo[n + 1]? = some e := by
        rw [show n + 1 = gpos GD.gdG e by omega]
        exact hSn
      have hnlt : n < GD.gdG.gxGmo.length := by
        have := gposLtLen GD.gdG e hein
        omega
      obtain ⟨z, hz⟩ := someOfIsSome (lookup_lt_is_Some_2 hnlt)
      have hzin : z ∈ GD.gdG.gxGmo := elem_of_list_lookup_2 hz
      have hzpos : gpos GD.gdG z = n := gposOfLookup _ _ _ hnd hz
      have hzmem : gmem GD.gdG z := gwfGmoMem _ _ hwf hzin
      have hwn : gpos GD.gdG w < n := by omega
      have hmo_wz : gmoLt GD.gdG w z := ⟨hwin, hzin, by omega⟩
      have hmo_ze : gmoLt GD.gdG z e := ⟨hzin, hein, by omega⟩
      have hposze := hmo_ze.2.2
      have hzs : (gxLbl GD.gdG z).isSome = true := by
        obtain ⟨l, hl, _⟩ := hzmem
        simp [hl]
      have hzne_e : z ≠ e := by
        intro h
        rw [h] at hmo_ze
        exact gmoLtIrrefl _ _ hmo_ze
      -- the vacuous side conditions
      have hnppo : ¬ gppo GD.gdG z e := poMinNoGppo GD.gdG w e z hv hpmin hzmem hmo_wz
      have hnpo : ¬ WeakRvwmoGraph.gpo GD.gdG z e := poMinNoGpo GD.gdG w e z hv hpmin hzmem hmo_wz
      have hdep : (z, e) ∉ GD.gdDeps := poMinNoDep GD w e z hdwf hv hpmin hzmem hmo_wz
      -- the swap: three cases
      have hstep : ∃ (π' : Nat → Nat) (G' : Gexec),
          rowsRel π' GD.gdG G' ∧ wperm π' GD.gdG G' ∧
          G'.gxGmo = (gswap GD.gdG n).gxGmo ∧
          rvwmoMinusDepsConsistent ⟨G', GD.gdDeps⟩ ∧
          (∀ e' w', gviol G' e' w' → gviol GD.gdG e' w') := by
        cases hew : gisW GD.gdG e with
        | true =>
          -- `e` a WRITE
          cases hzw : gisW GD.gdG z with
          | true =>
            -- (W,W): byte-disjoint or K3
            have hkz : 0 < gwix GD.gdG z :=
              WeakRvwmoGraph.gwixPos _ _ (gisWGwrites _ _ hwf hzs hzw)
            have hdisj : ∀ a, (∃ v, gwritesByte GD.gdG z a v) →
                ¬ ∃ v', gwritesByte GD.gdG e a v' := by
              rintro a ⟨v, hzv⟩ ⟨v', hev⟩
              by_cases hag : z.1 = e.1
              · by_cases hlt : z.2 < e.2
                · exact poMinNoBlocker GD.gdG w e z hv hpmin hzmem hmo_wz hag hlt
                · by_cases heq2 : z.2 = e.2
                  · exact hzne_e (Prod.ext hag heq2)
                  · have hpl : gppo GD.gdG e z :=
                      Or.inl ⟨⟨hag.symm, by omega, hse, hzs⟩, a, Or.inl ⟨v', hev⟩, Or.inl ⟨v, hzv⟩⟩
                    have := (hppo e z hpl).2.2
                    omega
              · exact hK3 GD heq w e z a v v' hv hmin hpmin hew hzw hag hmo_wz hmo_ze hzv hev
            refine ⟨tswap (gwix GD.gdG z), gswapw GD.gdG n (gwix GD.gdG z),
              rowsRelGswapw GD.gdG n _ hkz, wpermGswapw GD.gdG n z e hnd hz hSn' hzw hew, rfl,
              gswapwWwDeps GD n z e hcons hz hSn' hzw hew hdisj hnppo hdep, ?_⟩
            intro e' w' hv'
            exact gswapwViolMono GD.gdG n (gwix GD.gdG z) z e e' w' hnd hz hSn' hnpo hv'
          | false =>
            -- (R,W): the co-max condition, or K2
            have hcomax : ∀ a t v, greadsByte GD.gdG z a t v →
                (∃ v', gwritesByte GD.gdG e a v') → gwix GD.gdG e ≤ t := by
              rintro a t v hrd ⟨v', hwb⟩
              by_cases hle : gwix GD.gdG e ≤ t
              · exact hle
              · exact (hK2 GD heq w e z a t v v' hv hmin hpmin hew hmo_wz hmo_ze hrd hwb
                  (by omega)).elim
            refine ⟨fun t => t, gswap GD.gdG n, rowsRelGswap GD.gdG n,
              wpermGswapLo GD.gdG n z e hz hSn' hzw, rfl,
              gswapWriteDownDeps GD n z e hcons hz hSn' hzw hew hnppo hcomax hdep, ?_⟩
            intro e' w' hv'
            exact gswapViolMonoRw GD.gdG n z e e' w' hnd hz hSn' hnpo hv'
        | false =>
          -- `e` a READ: the read-down move; the source block is K1
          have hnrf : ∀ a t v, greadsByte GD.gdG e a t v → gwriteAt GD.gdG t ≠ some z := by
            intro a t v hrd hsrc
            have hwb := greadSourceByte GD.gdG e a t v z hlv hrd hsrc
            by_cases hag : z.1 = e.1
            · by_cases hlt : z.2 < e.2
              · exact poMinNoBlocker GD.gdG w e z hv hpmin hzmem hmo_wz hag hlt
              · by_cases heq2 : z.2 = e.2
                · exact hzne_e (Prod.ext hag heq2)
                · have hpl : gppo GD.gdG e z :=
                    Or.inl ⟨⟨hag.symm, by omega, hse, hzs⟩, a, Or.inr ⟨t, v, hrd⟩, Or.inl ⟨v, hwb⟩⟩
                  have := (hppo e z hpl).2.2
                  omega
            · exact hK1 GD heq w e a t v z hv hmin hpmin hew hrd hsrc hag hmo_wz hmo_ze
          refine ⟨fun t => t, gswap GD.gdG n, rowsRelGswap GD.gdG n,
            wpermGswapHi GD.gdG n z e hz hSn' hew, rfl,
            gswapReadDownDeps GD n z e hcons hz hSn' hew hnrf hnppo, ?_⟩
          intro e' w' hv'
          exact gswapViolMono GD.gdG n z e e' w' hnd hz hSn' hew hv'
      obtain ⟨π', G', hrows', hwp', hgmo', hcons', hmono'⟩ := hstep
      obtain ⟨hnle, hv', hmin', hpmin', hpe', hpw'⟩ :=
        swapInvariant π' GD.gdG G' w e z n hwf hz hSn' hrows' hgmo' hmono' hv hwn hmin hpmin
      have heq' : gdEquiv GD0 ⟨G', GD.gdDeps⟩ :=
        ⟨fun t => π' (π t), rowsRelTrans _ _ _ _ _ _ hrows0 hrows' (fun _ => rfl),
          wpermTrans _ _ _ _ _ _ hwp0 hwp' (fun _ => rfl), hdeps0, hcons'⟩
      obtain ⟨GD'', heq'', hlt''⟩ := ih ⟨G', GD.gdDeps⟩ w e heq' hv' hmin' hpmin'
        (by show gpos G' e - gpos G' w ≤ D; rw [hpe', hpw']; omega)
      have hlt2 : nviol GD''.gdG < nviol G' := hlt''
      exact ⟨GD'', heq'', by omega⟩

/-! # 9. THE NORMALIZATION THEOREM -/

theorem normalizeAux (GD0 : Gdexec) (N : Nat) :
    killK1 GD0 → killK2 GD0 → killK3 GD0 →
    ∀ GD, gdEquiv GD0 GD → nviol GD.gdG ≤ N →
    ∃ GD', gdEquiv GD0 GD' ∧ grule14 GD'.gdG := by
  intro hK1 hK2 hK3
  induction N with
  | zero =>
    -- no inversions left
    intro GD heq hN
    have hwf : gwf GD.gdG := by
      obtain ⟨_, _, _, _, hc⟩ := heq
      exact hc.1.1
    exact ⟨GD, heq, nviolZero _ hwf (by omega)⟩
  | succ N ih =>
    intro GD heq hN
    have hwf : gwf GD.gdG := by
      obtain ⟨_, _, _, _, hc⟩ := heq
      exact hc.1.1
    by_cases h0 : nviol GD.gdG = 0
    · exact ⟨GD, heq, nviolZero _ hwf h0⟩
    -- pick the gmo-minimal violating write `w` ...
    have hne : (gpairs GD.gdG).filter (fun p => decide (violp GD.gdG p)) ≠ [] := by
      intro hnil
      apply h0
      simp only [nviol, hnil, List.length_nil]
    obtain ⟨⟨e0, w⟩, hin, hmin0⟩ := listMinBy (fun p : Geid × Geid => gpos GD.gdG p.2) _ hne
    simp only [List.mem_filter, decide_eq_true_eq] at hin
    obtain ⟨_, hv0⟩ := hin
    have hv0' : gviol GD.gdG e0 w := hv0
    have hmin : ∀ e' w', gviol GD.gdG e' w' → ¬ gmoLt GD.gdG w' w := by
      rintro e' w' hv' ⟨_, _, hlt⟩
      have hin' : (e', w') ∈ (gpairs GD.gdG).filter (fun p => decide (violp GD.gdG p)) :=
        List.mem_filter.2 ⟨gviolGpairs _ _ _ hv', by simp only [decide_eq_true_eq]; exact hv'⟩
      have hle : gpos GD.gdG w ≤ gpos GD.gdG w' := hmin0 _ hin'
      omega
    -- ... and its po-minimal witness `e`.
    have hne2 : (gevs' GD.gdG).filter (fun e' => decide (gviol GD.gdG e' w)) ≠ [] := by
      intro hnil
      have he0 : e0 ∈ (gevs' GD.gdG).filter (fun e' => decide (gviol GD.gdG e' w)) := by
        refine List.mem_filter.2 ⟨?_, by simp only [decide_eq_true_eq]; exact hv0'⟩
        obtain ⟨_, ⟨l, hl, _⟩, _, _⟩ := hv0'
        exact elemOfGevs' _ _ (by simp [hl])
      rw [hnil] at he0
      simp at he0
    obtain ⟨e, hin2, hmin2⟩ := listMinBy (fun e' : Geid => e'.2) _ hne2
    simp only [List.mem_filter, decide_eq_true_eq] at hin2
    obtain ⟨_, hv⟩ := hin2
    have hpmin : ∀ e', gviol GD.gdG e' w → ¬ e'.2 < e.2 := by
      intro e' hv' hlt
      have hin' : e' ∈ (gevs' GD.gdG).filter (fun e'' => decide (gviol GD.gdG e'' w)) := by
        refine List.mem_filter.2 ⟨?_, by simp only [decide_eq_true_eq]; exact hv'⟩
        obtain ⟨_, ⟨l, hl, _⟩, _, _⟩ := hv'
        exact elemOfGevs' _ _ (by simp [hl])
      have hle : e.2 ≤ e'.2 := hmin2 _ hin'
      omega
    obtain ⟨GD1, heq1, hlt1⟩ := descent GD0 hK1 hK2 hK3
      (gpos GD.gdG e - gpos GD.gdG w) GD w e heq hv hmin hpmin (Nat.le_refl _)
    exact ih GD1 heq1 (by omega)

/-- THE DELIVERABLE.  Every RVWMO⁻(+deps)-consistent graph whose three residual
kill configurations are refuted normalizes to a `grule14` graph with the SAME
OBSERVABLES: same image, same rows, same dep fragment, and the write messages
preserved under a write-index permutation `π` that fixes the era-initial
image. -/
theorem normalize (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    killK1 GD → killK2 GD → killK3 GD →
    ∃ (GD' : Gdexec) (π : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel π GD.gdG GD'.gdG ∧
      GD'.gdDeps = GD.gdDeps ∧
      wperm π GD.gdG GD'.gdG := by
  intro hcons hK1 hK2 hK3
  obtain ⟨GD', ⟨π, hrows, hwp, hdeps, hcons'⟩, hr14⟩ :=
    normalizeAux GD (nviol GD.gdG) hK1 hK2 hK3 GD (gdEquivRefl GD hcons) (Nat.le_refl _)
  exact ⟨GD', π, hcons', hr14, hrows, hdeps, hwp⟩

end Weak
