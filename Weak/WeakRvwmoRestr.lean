/-
Weak: **THE RESTRICTION SLICE (route B, stage B1a)**.

Rocq: `iris/WeakRvwmoRestr.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4b).

THE POINT.  The exchange normalization hands its kill interface a po-MINIMAL
violating witness `e` below a gmo-MINIMAL violating write `w`.  Minimality makes
the events strictly below the frontier a DOUBLY CLOSED prefix — closed under
`gpo` within each hart, and closed downwards in `gmo` — and B1b realizes exactly
that prefix as a promise-free machine run.  This file is the order-theoretic
half: cutting a graph down to such a prefix PRESERVES RVWMO⁻ consistency, and —
when the prefix is violation-free — the cut graph satisfies rule 14 and
therefore LINEARIZES by `rule14Linearization`.

THE OBJECT.  `gxRestrict G cs n` cuts each program row `i` at `cs[i]?` and the
global memory order at `n`; `restrOk` ties the two.  The LABEL of a restricted
event is `G`'s label below the cut and `none` above it (`gxrLbl`), so every
label-determined notion restricts by conjunction with the cut predicate `gcut`;
the gmo prefix is a literal `take`, so `gpos` is PRESERVED for its members
(`gxrGpos`); `gwrites` of the restriction is `gwpre G n`, a PREFIX of
`gwrites G` (`gwpreApp`) — hence `gwix` agrees below the cut (`gxrGwix`).

WHAT IS PROVED: `restrictConsistent`, `restrictRule14`,
`restrictDepsConsistent`, and the composition `restrictLinearizes`; §9.1 the
non-vacuity check (`gxRestrictFull`, `restrOkFull`).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  Duplicated Rocq
   names (protocol rule) are FILE-QUALIFIED: `WeakRvwmoRestr.glblIsRGmem`,
   `WeakRvwmoRestr.glblIsWGmem`.  Uses of duplicated names refer to the
   imported files' qualified names (`WeakRvwmoGraph.gpo`,
   `WeakRvwmoGraph.gwritesByteGisW`, `WeakRvwmoLin.gmsg`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2; `zip_with take` ↦
   `List.zipWith List.take`, `default d o` ↦ `o.getD d`, `omap f l` ↦
   `l.filterMap f`, `GExec`/`GDExec` ↦ anonymous constructors,
   `bool_decide (e.2 < c)` ↦ `decide (e.2 < c)`, `x ← o; ...` ↦ `Option.bind`.
3. `filterIffElem` takes Boolean predicates (`p x = true ↔ q x = true`), the
   shim's `filter` convention (`Decision` ↦ `Bool`).
4. `restrictRule14`: `gviolGrule14` (Lean) takes `gwf G`, so the restriction's
   consistency is projected to its `gwf` component — same statement.

**Name map** (Rocq → Lean): `filter_iff_elem` ↦ `filterIffElem`; `take_NoDup` ↦
`takeNoDup`; `gcut`; `gcut_intro` ↦ `gcutIntro`; `gcut_elim` ↦ `gcutElim`;
`gcut_po_down` ↦ `gcutPoDown`; `gx_restrict` ↦ `gxRestrict`; `restr_ok` ↦
`restrOk`; `restr_ok_len` ↦ `restrOkLen`; `restr_ok_in` ↦ `restrOkIn`;
`restr_ok_cut` ↦ `restrOkCut`; `gxr_prog_lookup` ↦ `gxrProgLookup`; `gxr_row` ↦
`gxrRow`; `gxr_lbl` ↦ `gxrLbl`; `gxr_lbl_in` ↦ `gxrLblIn`; `gxr_lbl_Some` ↦
`gxrLblSome`; `gxr_is_Some` ↦ `gxrIsSome`; `gxr_glbl_is` ↦ `gxrGlblIs`;
`gxr_gmem` ↦ `gxrGmem`; `gxr_gis_w` ↦ `gxrGisW`; `gxr_gis_w_true` ↦
`gxrGisWTrue`; `gxr_gpo` ↦ `gxrGpo`; `gxr_wrb` ↦ `gxrWrb`; `gxr_rdb` ↦ `gxrRdb`;
`gxr_gaccesses` ↦ `gxrGaccesses`; `gxr_gmsg` ↦ `gxrGmsg`; `wrb_gmem` ↦
`wrbGmem`; `rdb_gmem` ↦ `rdbGmem`; `glbl_is_w_gmem` ↦
`WeakRvwmoRestr.glblIsWGmem`; `glbl_is_r_gmem` ↦ `WeakRvwmoRestr.glblIsRGmem`;
`gppo_lbl` ↦ `gppoLbl`; `gxr_gppo` ↦ `gxrGppo`; `gxr_gppo_cut` ↦ `gxrGppoCut`;
`take_elem_gmo` ↦ `takeElemGmo`; `gxr_gpos` ↦ `gxrGpos`; `gpos_take_lt` ↦
`gposTakeLt`; `gpos_lt_take` ↦ `gposLtTake`; `gxr_gmo_lt` ↦ `gxrGmoLt`;
`gwpre`; `gwrites_restrict` ↦ `gwritesRestrict`; `gwpre_app` ↦ `gwpreApp`;
`gwpre_lookup` ↦ `gwpreLookup`; `gwpre_take` ↦ `gwpreTake`; `gwpre_elem` ↦
`gwpreElem`; `gxr_gwrites_in` ↦ `gxrGwritesIn`; `gxr_gwrites_out` ↦
`gxrGwritesOut`; `gxr_gwix` ↦ `gxrGwix`; `gxr_gwrite_at` ↦ `gxrGwriteAt`;
`gxr_gwrite_at_in` ↦ `gxrGwriteAtIn`; `restrict_consistent` ↦
`restrictConsistent`; `gviol_restrict` ↦ `gviolRestrict`; `restrict_rule14` ↦
`restrictRule14`; `gd_restrict` ↦ `gdRestrict`; `gd_restrict_deps` ↦
`gdRestrictDeps`; `restrict_deps_consistent` ↦ `restrictDepsConsistent`;
`omap_gmsg_cut` ↦ `omapGmsgCut`; `restrict_linearizes` ↦ `restrictLinearizes`;
`gfull_cs` ↦ `gfullCs`; `gx_restrict_full` ↦ `gxRestrictFull`; `restr_ok_full` ↦
`restrOkFull`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakRvwmoLin
import Weak.WeakRvwmoXchg

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 1. A GENERIC LIST KIT -/

/-- `filter` only looks at the list's own elements. -/
theorem filterIffElem {A : Type _} (p q : A → Bool) (l : List A) :
    (∀ x, x ∈ l → (p x = true ↔ q x = true)) → l.filter p = l.filter q := by
  intro h
  apply List.filter_congr
  intro x hx
  exact Bool.eq_iff_iff.2 (h x hx)

theorem takeNoDup {A : Type _} (l : List A) (m : Nat) : l.Nodup → (l.take m).Nodup :=
  fun h => h.sublist (List.take_sublist _ _)

/-! # 2. THE CUT PREDICATE AND THE RESTRICTED GRAPH -/

/-- `gcut cs e`: `e` survives its hart's row cut.  A BOOLEAN — the restriction
filters with it. -/
def gcut (cs : List Nat) (e : Geid) : Bool :=
  match cs[e.1]? with
  | some c => decide (e.2 < c)
  | none => false

theorem gcutIntro (cs : List Nat) (e : Geid) (c : Nat) :
    cs[e.1]? = some c → e.2 < c → gcut cs e = true := by
  intro hc hlt
  simp [gcut, hc, hlt]

theorem gcutElim (cs : List Nat) (e : Geid) :
    gcut cs e = true → ∃ c, cs[e.1]? = some c ∧ e.2 < c := by
  unfold gcut
  cases hc : cs[e.1]? with
  | none => intro h; exact absurd h (by simp)
  | some c =>
    intro h
    exact ⟨c, rfl, of_decide_eq_true h⟩

/-- THE CUT IS PO-DOWN-CLOSED. -/
theorem gcutPoDown (cs : List Nat) (e1 e2 : Geid) :
    e1.1 = e2.1 → e1.2 < e2.2 → gcut cs e2 = true → gcut cs e1 = true := by
  intro hag hlt hc
  obtain ⟨c, hc, hlt2⟩ := gcutElim cs e2 hc
  exact gcutIntro cs e1 c (by rw [hag]; exact hc) (by omega)

/-- THE OBJECT: per-hart row cuts `cs` plus a gmo cut `n`. -/
def gxRestrict (G : Gexec) (cs : List Nat) (n : Nat) : Gexec :=
  ⟨G.gxImg, List.zipWith List.take cs G.gxProg, G.gxGmo.take n⟩

/-- `restrOk`: the cuts' MEM events are exactly the gmo prefix (the iff split
into its two inclusions, the `gmem` guard dropped on the ⇐ side — as Rocq). -/
def restrOk (G : Gexec) (cs : List Nat) (n : Nat) : Prop :=
  cs.length = G.gxProg.length ∧
  (∀ e, gmem G e → gcut cs e = true → e ∈ G.gxGmo.take n) ∧
  (∀ e, e ∈ G.gxGmo.take n → gcut cs e = true)

theorem restrOkLen (G : Gexec) (cs : List Nat) (n : Nat) :
    restrOk G cs n → cs.length = G.gxProg.length :=
  fun h => h.1

theorem restrOkIn (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    restrOk G cs n → gmem G e → gcut cs e = true → e ∈ G.gxGmo.take n :=
  fun h hm hc => h.2.1 e hm hc

theorem restrOkCut (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    restrOk G cs n → e ∈ G.gxGmo.take n → gcut cs e = true :=
  fun h he => h.2.2 e he

/-! # 3. THE LABEL LAYER: everything label-determined restricts by `gcut` -/

theorem gxrProgLookup (G : Gexec) (cs : List Nat) (n i : Nat) :
    (gxRestrict G cs n).gxProg[i]? =
      (cs[i]?).bind (fun c => (G.gxProg[i]?).bind (fun p => some (List.take c p))) := by
  show (List.zipWith List.take cs G.gxProg)[i]? = _
  exact lookup_zip_with

/-- The row of the restriction, in the shape `restrictLinearizes` reports. -/
theorem gxrRow (G : Gexec) (cs : List Nat) (n i : Nat) :
    ((gxRestrict G cs n).gxProg[i]?).getD [] =
      List.take ((cs[i]?).getD 0) ((G.gxProg[i]?).getD []) := by
  rw [gxrProgLookup]
  cases cs[i]? <;> cases G.gxProg[i]? <;> simp

/-- THE LABEL EQUATION. -/
theorem gxrLbl (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gxLbl (gxRestrict G cs n) e = if gcut cs e then gxLbl G e else none := by
  unfold gxLbl gcut
  rw [gxrProgLookup]
  cases hc : cs[e.1]? with
  | none => simp
  | some c =>
    cases hp : G.gxProg[e.1]? with
    | none => simp
    | some p =>
      by_cases hlt : e.2 < c
      · simp [hlt, lookup_take hlt]
      · simp [hlt, lookup_take_ge (by omega : c ≤ e.2)]

theorem gxrLblIn (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gcut cs e = true → gxLbl (gxRestrict G cs n) e = gxLbl G e := by
  intro h
  rw [gxrLbl, if_pos h]

theorem gxrLblSome (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) (l : Lbl) :
    gxLbl (gxRestrict G cs n) e = some l → gcut cs e = true ∧ gxLbl G e = some l := by
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrIsSome (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    (gxLbl (gxRestrict G cs n) e).isSome = true ↔
      gcut cs e = true ∧ (gxLbl G e).isSome = true := by
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrGlblIs (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) (P : Lbl → Bool) :
    glblIs (gxRestrict G cs n) e P ↔ gcut cs e = true ∧ glblIs G e P := by
  unfold glblIs
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrGmem (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gmem (gxRestrict G cs n) e ↔ gcut cs e = true ∧ gmem G e := by
  unfold gmem
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrGisW (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gisW (gxRestrict G cs n) e = if gcut cs e then gisW G e else false := by
  unfold gisW
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrGisWTrue (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gisW (gxRestrict G cs n) e = true ↔ gcut cs e = true ∧ gisW G e = true := by
  rw [gxrGisW]
  cases gcut cs e <;> simp

/-- `gpo` restricts by the cut of its TARGET — the source follows by
`gcutPoDown`. -/
theorem gxrGpo (G : Gexec) (cs : List Nat) (n : Nat) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo (gxRestrict G cs n) e1 e2 ↔
      WeakRvwmoGraph.gpo G e1 e2 ∧ gcut cs e2 = true := by
  unfold WeakRvwmoGraph.gpo
  simp only [gxrIsSome]
  constructor
  · rintro ⟨hag, hlt, ⟨_, hs1⟩, ⟨hc2, hs2⟩⟩
    exact ⟨⟨hag, hlt, hs1, hs2⟩, hc2⟩
  · rintro ⟨⟨hag, hlt, hs1, hs2⟩, hc2⟩
    exact ⟨hag, hlt, ⟨gcutPoDown cs e1 e2 hag hlt hc2, hs1⟩, ⟨hc2, hs2⟩⟩

theorem gxrWrb (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (gxRestrict G cs n) e a v ↔ gcut cs e = true ∧ gwritesByte G e a v := by
  unfold gwritesByte
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrRdb (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    greadsByte (gxRestrict G cs n) e a t v ↔ gcut cs e = true ∧ greadsByte G e a t v := by
  unfold greadsByte
  rw [gxrLbl]
  cases gcut cs e <;> simp

theorem gxrGaccesses (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) (a : Int) :
    gaccesses (gxRestrict G cs n) e a → gaccesses G e a := by
  rintro (⟨v, hw⟩ | ⟨t, v, hr⟩)
  · exact Or.inl ⟨v, ((gxrWrb G cs n e a v).1 hw).2⟩
  · exact Or.inr ⟨t, v, ((gxrRdb G cs n e a t v).1 hr).2⟩

theorem gxrGmsg (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    gcut cs e = true → WeakRvwmoLin.gmsg (gxRestrict G cs n) e = WeakRvwmoLin.gmsg G e := by
  intro h
  unfold WeakRvwmoLin.gmsg
  rw [gxrLblIn G cs n e h]

/-- The "this byte footprint makes the event a memory event" bridges. -/
theorem wrbGmem (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → gmem G e := by
  rintro ⟨l, base, vs, j, hl, hwr, _⟩
  exact WeakRvwmoGraph.glblIsWGmem G e ⟨l, hl, lbWrIsW l _ hwr⟩

theorem rdbGmem (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → gmem G e := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, _⟩
  exact WeakRvwmoGraph.glblIsRGmem G e ⟨l, hl, lbRdIsR l _ hrd⟩

theorem WeakRvwmoRestr.glblIsWGmem (G : Gexec) (e : Geid) : glblIs G e lbIsW → gmem G e :=
  WeakRvwmoGraph.glblIsWGmem G e

theorem WeakRvwmoRestr.glblIsRGmem (G : Gexec) (e : Geid) : glblIs G e lbIsR → gmem G e :=
  WeakRvwmoGraph.glblIsRGmem G e

/-- EVERY ppo⁻ ARM PINS BOTH ENDPOINTS' LABELS. -/
theorem gppoLbl (G : Gexec) (e1 e2 : Geid) :
    gppo G e1 e2 → (gxLbl G e1).isSome = true ∧ (gxLbl G e2).isSome = true := by
  rintro (⟨⟨_, _, h1, h2⟩, _⟩ | ⟨pr, pw, sr, sw, _, hk1, hk2⟩ | ⟨⟨_, _, h1, h2⟩, _⟩ |
    ⟨⟨_, _, h1, h2⟩, _⟩)
  · exact ⟨h1, h2⟩
  · refine ⟨?_, ?_⟩
    · rcases hk1 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> simp [hl]
    · rcases hk2 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> simp [hl]
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

/-- THE ppo⁻ TRANSFER: an edge of the restriction is an edge of `G`. -/
theorem gxrGppo (G : Gexec) (cs : List Nat) (n : Nat) (e1 e2 : Geid) :
    gppo (gxRestrict G cs n) e1 e2 → gppo G e1 e2 := by
  rintro (⟨hpo, a, h1, h2⟩ | ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk3, hk4, hlf⟩, hk1, hk2⟩ |
    ⟨hpo, h1, h2, h3⟩ | ⟨hpo, h1, h2⟩)
  · exact Or.inl ⟨((gxrGpo G cs n e1 e2).1 hpo).1, a, gxrGaccesses G cs n e1 a h1,
      gxrGaccesses G cs n e2 a h2⟩
  · refine Or.inr (Or.inl ⟨pr, pw, sr, sw,
      ⟨hag, hlt, kf, hk3, hk4, (gxrLblSome G cs n _ _ hlf).2⟩, ?_, ?_⟩)
    · rcases hk1 with ⟨h, hb⟩ | ⟨h, hb⟩
      · exact Or.inl ⟨((gxrGlblIs G cs n e1 _).1 h).2, hb⟩
      · exact Or.inr ⟨((gxrGlblIs G cs n e1 _).1 h).2, hb⟩
    · rcases hk2 with ⟨h, hb⟩ | ⟨h, hb⟩
      · exact Or.inl ⟨((gxrGlblIs G cs n e2 _).1 h).2, hb⟩
      · exact Or.inr ⟨((gxrGlblIs G cs n e2 _).1 h).2, hb⟩
  · exact Or.inr (Or.inr (Or.inl ⟨((gxrGpo G cs n e1 e2).1 hpo).1,
      ((gxrGlblIs G cs n e1 _).1 h1).2, ((gxrGlblIs G cs n e1 _).1 h2).2,
      ((gxrGmem G cs n e2).1 h3).2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨((gxrGpo G cs n e1 e2).1 hpo).1,
      ((gxrGlblIs G cs n e1 _).1 h1).2, ((gxrGlblIs G cs n e2 _).1 h2).2⟩))

theorem gxrGppoCut (G : Gexec) (cs : List Nat) (n : Nat) (e1 e2 : Geid) :
    gppo (gxRestrict G cs n) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true := by
  intro h
  obtain ⟨h1, h2⟩ := gppoLbl _ _ _ h
  exact ⟨((gxrIsSome G cs n e1).1 h1).1, ((gxrIsSome G cs n e2).1 h2).1⟩

/-! # 4. THE GMO PREFIX: positions are PRESERVED -/

theorem takeElemGmo (G : Gexec) (n : Nat) (e : Geid) : e ∈ G.gxGmo.take n → e ∈ G.gxGmo :=
  fun h => List.mem_of_mem_take h

theorem gxrGpos (G : Gexec) (cs : List Nat) (n : Nat) (e : Geid) :
    G.gxGmo.Nodup → e ∈ G.gxGmo.take n → gpos (gxRestrict G cs n) e = gpos G e := by
  intro hnd he
  obtain ⟨i, hi, h⟩ := gposLookup (gxRestrict G cs n) e he
  rw [h]
  change (G.gxGmo.take n)[i]? = some e at hi
  exact (gposOfLookup G i e hnd (lookup_take_Some.1 hi).1).symm

theorem gposTakeLt (G : Gexec) (n : Nat) (e : Geid) :
    G.gxGmo.Nodup → e ∈ G.gxGmo.take n → gpos G e < n := by
  intro hnd he
  obtain ⟨i, hi, hlt⟩ := elem_of_take.1 he
  rw [gposOfLookup G i e hnd hi]
  exact hlt

theorem gposLtTake (G : Gexec) (n : Nat) (e : Geid) :
    e ∈ G.gxGmo → gpos G e < n → e ∈ G.gxGmo.take n :=
  fun he hlt => elem_of_take.2 ⟨gpos G e, gposElemLookup G e he, hlt⟩

theorem gxrGmoLt (G : Gexec) (cs : List Nat) (n : Nat) (e1 e2 : Geid) :
    G.gxGmo.Nodup →
    (gmoLt (gxRestrict G cs n) e1 e2 ↔
      e1 ∈ G.gxGmo.take n ∧ e2 ∈ G.gxGmo.take n ∧ gmoLt G e1 e2) := by
  intro hnd
  constructor
  · rintro ⟨h1, h2, hlt⟩
    rw [gxrGpos G cs n e1 hnd h1, gxrGpos G cs n e2 hnd h2] at hlt
    exact ⟨h1, h2, takeElemGmo G n e1 h1, takeElemGmo G n e2 h2, hlt⟩
  · rintro ⟨h1, h2, _, _, hlt⟩
    refine ⟨h1, h2, ?_⟩
    rw [gxrGpos G cs n e1 hnd h1, gxrGpos G cs n e2 hnd h2]
    exact hlt

/-! # 5. THE WRITE SUB-ORDER: a PREFIX of `gwrites G` -/

/-- The restriction's write sub-order, spelled without the restriction. -/
def gwpre (G : Gexec) (n : Nat) : List Geid := (G.gxGmo.take n).filter (gisW G)

theorem gwritesRestrict (G : Gexec) (cs : List Nat) (n : Nat) :
    (∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) →
    gwrites (gxRestrict G cs n) = gwpre G n := by
  intro hcut
  show (G.gxGmo.take n).filter (gisW (gxRestrict G cs n)) = (G.gxGmo.take n).filter (gisW G)
  apply filterIffElem
  intro e he
  rw [gxrGisW, if_pos (hcut e he)]

theorem gwpreApp (G : Gexec) (n : Nat) :
    gwrites G = gwpre G n ++ (G.gxGmo.drop n).filter (gisW G) := by
  unfold gwrites gwpre
  rw [← List.filter_append, List.take_append_drop]

theorem gwpreLookup (G : Gexec) (n i : Nat) (w : Geid) :
    (gwpre G n)[i]? = some w → (gwrites G)[i]? = some w := by
  intro hi
  rw [gwpreApp G n]
  exact lookup_app_l_Some hi

theorem gwpreTake (G : Gexec) (n : Nat) : gwpre G n = (gwrites G).take (gwpre G n).length := by
  rw [gwpreApp G n, take_app_length]

theorem gwpreElem (G : Gexec) (n : Nat) (w : Geid) : w ∈ gwpre G n → w ∈ G.gxGmo.take n :=
  fun h => (elem_of_list_filter.1 h).2

theorem gxrGwritesIn (G : Gexec) (cs : List Nat) (n : Nat) (w : Geid) :
    gcut cs w = true → w ∈ G.gxGmo.take n → gisW G w = true →
    w ∈ gwrites (gxRestrict G cs n) :=
  fun hc hm hw => (gwritesElemOf _ w).2 ⟨hm, (gxrGisWTrue G cs n w).2 ⟨hc, hw⟩⟩

theorem gxrGwritesOut (G : Gexec) (cs : List Nat) (n : Nat) (w : Geid) :
    w ∈ gwrites (gxRestrict G cs n) →
    gcut cs w = true ∧ w ∈ G.gxGmo.take n ∧ gisW G w = true := by
  intro h
  obtain ⟨hm, hw⟩ := (gwritesElemOf _ w).1 h
  obtain ⟨hc, hw'⟩ := (gxrGisWTrue G cs n w).1 hw
  exact ⟨hc, hm, hw'⟩

theorem gxrGwix (G : Gexec) (cs : List Nat) (n : Nat) (w : Geid) :
    G.gxGmo.Nodup → (∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) →
    w ∈ gwrites (gxRestrict G cs n) →
    gwix (gxRestrict G cs n) w = gwix G w := by
  intro hnd hcut hw
  obtain ⟨i, hi, h⟩ := gwixLookup (gxRestrict G cs n) w hw
  rw [h]
  rw [gwritesRestrict G cs n hcut] at hi
  exact (gwixOfLookup G i w hnd (gwpreLookup G n i w hi)).symm

theorem gxrGwriteAt (G : Gexec) (cs : List Nat) (n t : Nat) (w : Geid) :
    (∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) →
    gwriteAt (gxRestrict G cs n) t = some w → gwriteAt G t = some w := by
  intro hcut ht
  cases t with
  | zero => simp [gwriteAt] at ht
  | succ i =>
    unfold gwriteAt at ht ⊢
    rw [gwritesRestrict G cs n hcut] at ht
    exact gwpreLookup G n i w ht

theorem gxrGwriteAtIn (G : Gexec) (cs : List Nat) (n t : Nat) (w : Geid) :
    G.gxGmo.Nodup → (∀ e, e ∈ G.gxGmo.take n → gcut cs e = true) →
    w ∈ gwrites (gxRestrict G cs n) → gwriteAt G t = some w →
    gwriteAt (gxRestrict G cs n) t = some w := by
  intro hnd hcut hw ht
  obtain ⟨_, hix⟩ := gwriteAtInv G t w hnd ht
  subst hix
  rw [← gxrGwix G cs n w hnd hcut hw]
  exact gwriteAtGwix _ w hw

/-! # 6. CONSISTENCY RESTRICTS -/

theorem restrictConsistent (G : Gexec) (cs : List Nat) (n : Nat) :
    rvwmoMinusConsistent G → restrOk G cs n →
    rvwmoMinusConsistent (gxRestrict G cs n) := by
  rintro ⟨hwf, hppo, hlv, hat⟩ hro
  obtain ⟨hnd, hmem, hsh⟩ := hwf
  have hcut : ∀ e, e ∈ G.gxGmo.take n → gcut cs e = true :=
    fun e he => restrOkCut G cs n e hro he
  -- the "an in-cut memory event is in the prefix" shape, once
  have hin : ∀ e, gcut cs e = true → gmem G e → e ∈ G.gxGmo.take n :=
    fun e hc hm => restrOkIn G cs n e hro hm hc
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- gwf
    exact takeNoDup G.gxGmo n hnd
  · intro e
    show e ∈ G.gxGmo.take n ↔ _
    rw [gxrGmem]
    constructor
    · intro he
      exact ⟨hcut e he, (hmem e).1 (takeElemGmo G n e he)⟩
    · rintro ⟨hc, hm⟩
      exact hin e hc hm
  · intro i p k l hp hk
    rw [gxrProgLookup] at hp
    cases hc : cs[i]? with
    | none => rw [hc] at hp; simp at hp
    | some c =>
      cases hp0 : G.gxProg[i]? with
      | none => rw [hc, hp0] at hp; simp at hp
      | some p0 =>
        rw [hc, hp0] at hp
        simp at hp
        subst hp
        exact hsh i p0 k l hp0 (lookup_take_Some.1 hk).1
  · -- gppo⁻ ⊆ gmo
    intro e1 e2 hppo'
    obtain ⟨hc1, hc2⟩ := gxrGppoCut G cs n e1 e2 hppo'
    have hmo := hppo e1 e2 (gxrGppo G cs n e1 e2 hppo')
    exact (gxrGmoLt G cs n e1 e2 hnd).2
      ⟨hin e1 hc1 ((hmem e1).1 hmo.1), hin e2 hc2 ((hmem e2).1 hmo.2.1), hmo⟩
  · -- load value
    intro e a t v hrd'
    obtain ⟨hce, hrd⟩ := (gxrRdb G cs n e a t v).1 hrd'
    have he : e ∈ G.gxGmo.take n := hin e hce (rdbGmem G e a t v hrd)
    obtain ⟨hsrc, hmax⟩ := hlv e a t v hrd
    refine ⟨?_, ?_⟩
    · cases t with
      | zero => exact hsrc
      | succ t =>
        obtain ⟨w, hwat, hwb, hvis⟩ :=
          (hsrc : ∃ w, gwriteAt G (t + 1) = some w ∧ gwritesByte G w a v ∧ gvisible G w e)
        have hwm : w ∈ G.gxGmo.take n := by
          rcases hvis with hmo | hpo
          · refine gposLtTake G n w hmo.1 ?_
            have h1 := gposTakeLt G n e hnd he
            have h2 := hmo.2.2
            omega
          · exact hin w (gcutPoDown cs w e hpo.1 hpo.2.1 hce) (wrbGmem G w a v hwb)
        have hcw : gcut cs w = true := hcut w hwm
        have hwg : w ∈ gwrites (gxRestrict G cs n) :=
          gxrGwritesIn G cs n w hcw hwm (WeakRvwmoGraph.gwritesByteGisW G w a v hwb)
        show ∃ w, gwriteAt (gxRestrict G cs n) (t + 1) = some w ∧
          gwritesByte (gxRestrict G cs n) w a v ∧ gvisible (gxRestrict G cs n) w e
        refine ⟨w, gxrGwriteAtIn G cs n (t + 1) w hnd hcut hwg hwat,
          (gxrWrb G cs n w a v).2 ⟨hcw, hwb⟩, ?_⟩
        rcases hvis with hmo | hpo
        · exact Or.inl ((gxrGmoLt G cs n w e hnd).2 ⟨hwm, he, hmo⟩)
        · exact Or.inr ((gxrGpo G cs n w e).2 ⟨hpo, hce⟩)
    · intro w' v' hwb' hvis'
      obtain ⟨hcw', hwb⟩ := (gxrWrb G cs n w' a v').1 hwb'
      have hwm' := hin w' hcw' (wrbGmem G w' a v' hwb)
      have hwg' := gxrGwritesIn G cs n w' hcw' hwm'
        (WeakRvwmoGraph.gwritesByteGisW G w' a v' hwb)
      rw [gxrGwix G cs n w' hnd hcut hwg']
      apply hmax w' v' hwb
      rcases hvis' with hmo | hpo
      · exact Or.inl ((gxrGmoLt G cs n w' e hnd).1 hmo).2.2
      · exact Or.inr ((gxrGpo G cs n w' e).1 hpo).1
  · -- atomicity
    intro e a t v hrd' hw' w' v' hwb'
    obtain ⟨hce, hrd⟩ := (gxrRdb G cs n e a t v).1 hrd'
    have hw := ((gxrGlblIs G cs n e lbIsW).1 hw').2
    obtain ⟨hcw', hwb⟩ := (gxrWrb G cs n w' a v').1 hwb'
    have he := hin e hce (rdbGmem G e a t v hrd)
    have hwm' := hin w' hcw' (wrbGmem G w' a v' hwb)
    have heg := gxrGwritesIn G cs n e hce he (glblIsWGisW G e hw)
    have hwg' := gxrGwritesIn G cs n w' hcw' hwm'
      (WeakRvwmoGraph.gwritesByteGisW G w' a v' hwb)
    rw [gxrGwix G cs n w' hnd hcut hwg', gxrGwix G cs n e hnd hcut heg]
    exact hat e a t v hrd hw w' v' hwb

/-! # 7. RULE 14 FROM VIOLATION-FREEDOM OF THE CUT -/

/-- A violation of the restriction is one of `G`, with both ends in the cut. -/
theorem gviolRestrict (G : Gexec) (cs : List Nat) (n : Nat) (e w : Geid) :
    G.gxGmo.Nodup → gviol (gxRestrict G cs n) e w →
    gviol G e w ∧ gcut cs e = true ∧ gcut cs w = true := by
  rintro hnd ⟨hpo, hme, hw, hmo⟩
  obtain ⟨hpo, hcw⟩ := (gxrGpo G cs n e w).1 hpo
  obtain ⟨hce, hme⟩ := (gxrGmem G cs n e).1 hme
  have hw := ((gxrGlblIs G cs n w lbIsW).1 hw).2
  have hmo := ((gxrGmoLt G cs n w e hnd).1 hmo).2.2
  exact ⟨⟨hpo, hme, hw, hmo⟩, hce, hcw⟩

theorem restrictRule14 (G : Gexec) (cs : List Nat) (n : Nat) :
    rvwmoMinusConsistent G → restrOk G cs n →
    (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol G e w) →
    grule14 (gxRestrict G cs n) := by
  intro hc hro hvf
  have hnd := hc.1.1
  apply gviolGrule14
  · exact (restrictConsistent G cs n hc hro).1
  · intro e w hv
    obtain ⟨hv', hce, hcw⟩ := gviolRestrict G cs n e w hnd hv
    exact hvf e w hce hcw hv'

/-! # 8. THE `Gdexec` FORM: the dep fragment restricts by filtering -/

def gdRestrict (GD : Gdexec) (cs : List Nat) (n : Nat) : Gdexec :=
  ⟨gxRestrict GD.gdG cs n,
   GD.gdDeps.filter (fun p : Geid × Geid => gcut cs p.1 && gcut cs p.2),
   GD.gdFetch.filter (fun p : Geid × Geid => gcut cs p.1 && gcut cs p.2)⟩

theorem gdRestrictDeps (GD : Gdexec) (cs : List Nat) (n : Nat) (p : Geid × Geid) :
    p ∈ (gdRestrict GD cs n).gdDeps ↔
      p ∈ GD.gdDeps ∧ gcut cs p.1 = true ∧ gcut cs p.2 = true := by
  simp [gdRestrict, List.mem_filter]

theorem restrictDepsConsistent (GD : Gdexec) (cs : List Nat) (n : Nat) :
    rvwmoMinusDepsConsistent GD → restrOk GD.gdG cs n →
    rvwmoMinusDepsConsistent (gdRestrict GD cs n) := by
  rintro ⟨hc, hdwf, hdmo⟩ hro
  have hnd := hc.1.1
  refine ⟨restrictConsistent GD.gdG cs n hc hro, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (gdRestrictDeps GD cs n p).1 hp
    obtain ⟨h1, h2, h3, h4⟩ := hdwf p hp
    exact ⟨h1, h2, (gxrGlblIs GD.gdG cs n p.1 lbIsR).2 ⟨hc1, h3⟩,
      (gxrGlblIs GD.gdG cs n p.2 lbIsW).2 ⟨hc2, h4⟩⟩
  · intro p hp
    obtain ⟨hp, hc1, hc2⟩ := (gdRestrictDeps GD cs n p).1 hp
    obtain ⟨_, _, h3, h4⟩ := hdwf p hp
    have hmo := hdmo p hp
    exact (gxrGmoLt GD.gdG cs n p.1 p.2 hnd).2
      ⟨restrOkIn _ cs n p.1 hro (WeakRvwmoRestr.glblIsRGmem _ _ h3) hc1,
       restrOkIn _ cs n p.2 hro (WeakRvwmoRestr.glblIsWGmem _ _ h4) hc2, hmo⟩

/-! # 9. THE COMPOSITION: a violation-free restriction LINEARIZES -/

theorem omapGmsgCut (G : Gexec) (cs : List Nat) (n : Nat) (l : List Geid) :
    (∀ e, e ∈ l → gcut cs e = true) →
    l.filterMap (WeakRvwmoLin.gmsg (gxRestrict G cs n)) = l.filterMap (WeakRvwmoLin.gmsg G) := by
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro hcut
    rw [List.filterMap_cons, List.filterMap_cons, gxrGmsg G cs n e (hcut e (by simp)),
      ih (fun x hx => hcut x (by simp [hx]))]

/-- THE B2e-FACING COROLLARY.  A violation-free `restrOk` restriction of a
consistent `Gdexec` is realized by a candidate: same image, the CUT rows, and
the log is the prefix's writes' messages. -/
theorem restrictLinearizes (GD : Gdexec) (cs : List Nat) (n : Nat) :
    rvwmoMinusDepsConsistent GD → restrOk GD.gdG cs n →
    (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol GD.gdG e w) →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      (∀ i, (c.cdTr.filter (fun s : Estep => decide (s.esAg = i))).map (fun s => s.esLb) =
        List.take ((cs[i]?).getD 0) ((GD.gdG.gxProg[i]?).getD [])) ∧
      cdLog c c.cdTr.length = (gwpre GD.gdG n).filterMap (WeakRvwmoLin.gmsg GD.gdG) := by
  intro hD hro hvf
  have hc := hD.1
  have hcut : ∀ e, e ∈ GD.gdG.gxGmo.take n → gcut cs e = true :=
    fun e he => restrOkCut _ cs n e hro he
  obtain ⟨c, hsr, himg, hrow, hlog⟩ := rule14Linearization (gxRestrict GD.gdG cs n)
    (restrictConsistent _ _ _ hc hro) (restrictRule14 _ _ _ hc hro hvf)
  refine ⟨c, hsr, himg, ?_, ?_⟩
  · intro i
    rw [hrow i, gxrRow]
  · rw [hlog, gwritesRestrict _ cs n hcut]
    exact omapGmsgCut _ cs n _ (fun e he => hcut e (gwpreElem _ n e he))

/-! ## 9.1 NON-VACUITY: the FULL cut IS a `restrOk` restriction, and it is the
identity — so `restrOk` is satisfiable and `gcut` is not accidentally empty. -/

def gfullCs (G : Gexec) : List Nat := G.gxProg.map List.length

theorem gxRestrictFull (G : Gexec) : gxRestrict G (gfullCs G) G.gxGmo.length = G := by
  cases G with
  | mk img prog gmo =>
    simp only [gxRestrict, gfullCs, take_ge (Nat.le_refl gmo.length)]
    congr 1
    induction prog with
    | nil => rfl
    | cons p prog ih => simp [ih]

theorem restrOkFull (G : Gexec) : gwf G → restrOk G (gfullCs G) G.gxGmo.length := by
  intro hwf
  have hmem := hwf.2.1
  have hid : G.gxGmo.take G.gxGmo.length = G.gxGmo := take_ge (Nat.le_refl _)
  refine ⟨?_, ?_, ?_⟩
  · simp [gfullCs]
  · intro e hm _
    rw [hid]
    exact (hmem e).2 hm
  · intro e he
    rw [hid] at he
    obtain ⟨l, hl, _⟩ := (hmem e).1 he
    unfold gxLbl at hl
    cases hp : G.gxProg[e.1]? with
    | none => rw [hp] at hl; simp at hl
    | some p =>
      rw [hp] at hl
      have hl' : p[e.2]? = some l := hl
      refine gcutIntro _ _ p.length ?_ (lookup_lt_Some hl')
      simp [gfullCs, hp]

end Weak
