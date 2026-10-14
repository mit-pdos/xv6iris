/-
Weak: **W5d-G G6-3b (4) [OWN.75] — R1: the FETCH-SOURCE-CLOSED cut class and its stability**
(plan `notes/weak-allocproc-plan.md` rev 52, §B(4)(iii) XL risk R1, §C top "W5d-G G6 — LAUNCH
PLAN [rev 50]"; the G6-3 report's open question 4, option (a), FAITHFUL).  Lean-only.

G6-3's induction (`GraphFetchLinInd`, deviation 1) GUARDED its hypothesis: `cycleKillIOZ` hands the
kill acyclicity only of the proper hulls ON WHICH THE ZIFENCEI BUNDLE HOLDS, because the bundle is
NOT hull-stable under an arbitrary `properCut` (a kept fetch may lose its source write: `hullOk`
is rf-closed, not fetch-closed; the hull renames the tag to itself and (Z1) fails).  So the kill
(W11-F) carried the burden of re-proving the bundle on each hull it cuts.  This file removes it:

  §1  the CLASS — `GraphFetchHullZ.emSrcClosed G cs i em`: every fetch item of `em` at a KEPT
      slot (`emSlot < cs[i]`) has every fetched byte's source write kept; and
      `GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs`: the bundle's row clauses at a witness
      emission per row that is source-closed for `cs` (the cut is closed under the fetch sources of
      the kept instructions of the bundle's emissions — a closure condition on the cut, nothing
      about the hull);
  §2  the emission half — `GraphFetchHullZ.gzFetchHull` (`gzFetch` passes to the hull at the
      renamed tags: (Z1) by the source's kept message, (Z2)/(Z3) by `gmo`'s restriction and the
      write-index order's invariance `gxhGwixLt`), `GraphFetchHullZ.fetchEdgeHull` (every fragment
      edge of the hull's renamed emission is an original edge with both ends kept), the hull's
      contributors are original contributors (`GraphFetchHullZ.contribHull`, rf-closure + load
      value), and **`GraphFetchHullZ.emHull`**;
  §3  **`GraphFetchHullZ.gfexecConfZFHull`** — THE STABILITY: the Zifencei bundle passes to the
      hull of every `gfDev`-closed, rf-closed cut in the class (the `gfexecConfHull` pattern, the
      fetch clause by §2);
  §4  the UNGUARDED kill: **`cycleKillIOZC`** (the induction hypothesis over every proper cut in
      the class, NO hull bundle) with `cycleKillIOZOfC : cycleKillIOZC → cycleKillIOZ` (so every
      G6-3 / G6-3b corollary consumes it), the cat twin `CatLin.cycleKillCZC`/`cycleKillCZOfC`,
      and the kernel-text instance `GraphFetchHullZ.emSrcClosedOfImg` (a pinned emission — every
      fetch tag `0` — is source-closed for EVERY cut, so on the kernel-text bundles the class is
      all cuts).

What W11-F now consumes: `cycleKillIOZC` (resp. `CatLin.cycleKillCZC`) as the kill to prove — its
induction hypothesis needs only `properCutF GF cs` and the closure `fetchSrcClosedCut boot fab GF
cs` at the cuts it chooses (no Zifencei bundle on any hull); `t2linSupplyFZIO (cycleKillIOZOfC …)`
etc. for the supply.

Spec marks.  RVWMO/riscv.cat/Zifencei/PMAs are silent on how a proof cuts a graph: the class and
its stability are proof organisation (FAITHFUL, no trusted text).  Lean-only helpers are
file-qualified (`GraphFetchHullZ.*`).
-/
import Weak.GraphFetchAncSupply

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The class -/

/-- The fetch sources of `em`'s fetch items at kept slots are kept. -/
def GraphFetchHullZ.emSrcClosed (G : Gexec) (cs : List Nat) (i : Nat) (em : Hemission) : Prop :=
  ∀ (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
    em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
    GraphFetchSpike.emSlot em.emItems n < (cs[i]?).getD 0 →
    ∀ (j t : Nat) (v : BitVec 8) (w : Geid), tvs[j]? = some (t, v) → gwriteAt G t = some w →
      gcut cs w = true

/-- **THE CLASS**: the Zifencei bundle's row clauses at witness emissions that are source-closed for
the cut `cs`. -/
def GraphFetchHullZ.fetchSrcClosedCut (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) : Prop :=
  ∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
    ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      hartConff i row (boot i) dvi dvo tq em ∧
      (∀ k : Nat, k < row.length →
         ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
      (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
      (emZifencei GF.gfGd.gdG i em ∧ GraphFetch.emFetchIn GF.gfGd i em) ∧
      (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GF.gfGd.gdDeps) ∧
      GraphFetchHullZ.emSrcClosed GF.gfGd.gdG cs i em

/-- The kernel-text instance: a PINNED emission (every fetch tag `0`, `emFetchImg`) is
source-closed for every cut. -/
theorem GraphFetchHullZ.emSrcClosedOfImg (G : Gexec) (cs : List Nat) (i : Nat) (em : Hemission) :
    emFetchImg G.gxImg em → GraphFetchHullZ.emSrcClosed G cs i em := by
  intro hpin n base tvs hn _ j t v w hj hw
  have hp : WeakAxRealize.fetchPin G.gxImg (Wlabel.LIFetch base tvs) :=
    hpin _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hn, rfl⟩)
  have ht : t = 0 := hp.1 t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)
  subst ht
  simp [gwriteAt] at hw

/-- … so a bundle whose witnesses are pinned puts EVERY cut in the class. -/
theorem GraphFetchHullZ.fetchSrcClosedOfImg (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec)
    (cs : List Nat) :
    (∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
      ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
        hartConff i row (boot i) dvi dvo tq em ∧
        (∀ k : Nat, k < row.length →
           ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
        (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
        (emZifencei GF.gfGd.gdG i em ∧ GraphFetch.emFetchIn GF.gfGd i em) ∧
        (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GF.gfGd.gdDeps) ∧
        emFetchImg GF.gfGd.gdG.gxImg em) →
    GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs := by
  intro h i row hrow
  obtain ⟨em, dvi, dvo, tq, h1, h2, h3, h4, h5, h6⟩ := h i row hrow
  exact ⟨em, dvi, dvo, tq, h1, h2, h3, h4, h5,
    GraphFetchHullZ.emSrcClosedOfImg _ cs i em h6⟩

/-! # 2. The emission half -/

/-- A `hemitf` item list ends with a row item (or is empty). -/
theorem GraphFetchHullZ.hemitfLast (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → ∀ it, es.getLast? = some it → it.2.isSome = true := by
  intro h
  induction h with
  | HFnil => intro it hit; cases hit
  | HFone k ws lb row p ls pa da l p' es pfin _ _ _ _ _ _ ih =>
    exact GraphFetchBlocks.lastTagged _ _ _ rfl ih
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ _ _ _ _ _ _ _ _ ih =>
    exact GraphFetchBlocks.lastTagged _ _ _ rfl (GraphFetchBlocks.lastTagged _ _ _ rfl ih)

/-- The slot of an item of a prefix ending with a row item is its slot in the whole list, and is
the tag of an item of the prefix. -/
theorem GraphFetchHullZ.slotPrefix (its' rest : List Eitem) (n : Nat) :
    n < its'.length → (∀ it, its'.getLast? = some it → it.2.isSome = true) →
    ∃ it, it ∈ its' ∧ it.2 = some (GraphFetchSpike.emSlot (its' ++ rest) n) ∧
      GraphFetchSpike.emSlot its' n = GraphFetchSpike.emSlot (its' ++ rest) n := by
  intro hn hlast
  have hne : (its'.drop n).filterMap Prod.snd ≠ [] := by
    obtain ⟨it, hit⟩ : ∃ it, its'.getLast? = some it := by
      cases h : its'.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff] at h
        subst h
        simp at hn
      | some it => exact ⟨it, rfl⟩
    have htag := hlast it hit
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 htag
    intro hnil
    have hmem : it ∈ its'.drop n := by
      rw [List.getLast?_eq_getElem?] at hit
      rw [List.mem_iff_getElem?]
      refine ⟨its'.length - 1 - n, ?_⟩
      rw [List.getElem?_drop, show n + (its'.length - 1 - n) = its'.length - 1 by omega]
      exact hit
    have : j ∈ (its'.drop n).filterMap Prod.snd := List.mem_filterMap.2 ⟨it, hmem, hj⟩
    rw [hnil] at this
    simp at this
  obtain ⟨h, tl, hht⟩ := List.exists_cons_of_ne_nil hne
  have hh : h ∈ (its'.drop n).filterMap Prod.snd := by rw [hht]; exact List.mem_cons_self
  obtain ⟨it, hit, hit2⟩ := List.mem_filterMap.1 hh
  have e1 : GraphFetchSpike.emSlot its' n = h := by
    unfold GraphFetchSpike.emSlot
    rw [hht]
    rfl
  have e2 : GraphFetchSpike.emSlot (its' ++ rest) n = h := by
    unfold GraphFetchSpike.emSlot
    rw [List.drop_append_of_le_length (by omega), List.filterMap_append, hht]
    rfl
  exact ⟨it, List.mem_of_mem_drop hit, by rw [e2]; exact hit2, by rw [e1, e2]⟩

/-- A fence.i site of a prefix emission is a site of the whole emission. -/
theorem GraphFetchHullZ.emFenceIPrefix (em em' : Hemission) (rest : List Eitem) (f : Nat) :
    em.emItems = em'.emItems ++ rest → emFenceI em' f → emFenceI em f := by
  rintro he ⟨pre, ls, rest', he', hpre, hl⟩
  exact ⟨pre, ls, rest' ++ rest, by rw [he, he']; simp, hpre, hl⟩

/-- A fetch item of the renamed prefix is a renamed fetch item of the whole emission. -/
theorem GraphFetchHullZ.itemHull (π : Nat → Nat) (em em' : Hemission) (rest : List Eitem) (n : Nat)
    (base : Int) (tvs' : List (Nat × BitVec 8)) :
    em.emItems = em'.emItems ++ rest →
    (emRen π em').emItems[n]? = some (Wlabel.LIFetch base tvs', none) →
    ∃ tvs, em'.emItems[n]? = some (Wlabel.LIFetch base tvs, none) ∧
      em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) ∧
      tvs' = tvs.map (tvRen π) ∧ n < em'.emItems.length := by
  intro he hn
  have hn0 : (em'.emItems.map (eitemRen π))[n]? = some (Wlabel.LIFetch base tvs', none) := hn
  rw [List.getElem?_map] at hn0
  cases hit : em'.emItems[n]? with
  | none => rw [hit] at hn0; cases hn0
  | some it =>
    rw [hit] at hn0
    obtain ⟨l0, o⟩ := it
    simp only [Option.map_some, Option.some.injEq, eitemRen, Prod.mk.injEq] at hn0
    obtain ⟨hl0, rfl⟩ := hn0
    cases l0 with
    | LIFetch b tvs =>
      simp only [wlblRen, Wlabel.LIFetch.injEq] at hl0
      obtain ⟨rfl, rfl⟩ := hl0
      have hlt : n < em'.emItems.length := lookup_lt_Some hit
      refine ⟨tvs, rfl, ?_, rfl, hlt⟩
      rw [he, List.getElem?_append_left hlt, hit]
    | _ => simp [wlblRen] at hl0

/-- A fetched byte's tag: the image (`0`), or a write the closure keeps, renamed to its hull
index. -/
theorem GraphFetchHullZ.tagKept (G : Gexec) (cs : List Nat) (hnd : G.gxGmo.Nodup) (t : Nat)
    (a : Int) (v : BitVec 8) :
    logByte G.gxImg (gwlog G) t a = some v →
    (∀ w, gwriteAt G t = some w → gcut cs w = true) →
    t = 0 ∨ ∃ w, gwriteAt G t = some w ∧ gcut cs w = true ∧ w ∈ gwrites G ∧ gwix G w = t ∧
      gwriteAt (gxHull G cs) (hren G cs t) = some w ∧ hren G cs t = gwix (gxHull G cs) w := by
  intro h1 hcl
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · exact .inl rfl
  obtain ⟨w, hw⟩ := GraphFetchCut.gwlogWriteAt G t a htpos (by rw [h1]; rfl)
  have hk := hcl w hw
  obtain ⟨hwg, hwix⟩ := gwriteAtInv G t w hnd hw
  exact .inr ⟨w, hw, hk, hwg, hwix, hrenWat G cs t w hw hk, hrenWix G cs t w hw hk⟩

/-- The hull's write-index order below a kept write reflects the original one. -/
theorem GraphFetchHullZ.ltTransport (G : Gexec) (cs : List Nat) (hnd : G.gxGmo.Nodup) (t : Nat)
    (w' : Geid) :
    (t = 0 ∨ ∃ w, gwriteAt G t = some w ∧ gcut cs w = true ∧ w ∈ gwrites G ∧ gwix G w = t ∧
      gwriteAt (gxHull G cs) (hren G cs t) = some w ∧ hren G cs t = gwix (gxHull G cs) w) →
    w' ∈ gwrites G → gcut cs w' = true →
    hren G cs t < gwix (gxHull G cs) w' → t < gwix G w' := by
  intro hk hw' hc' hlt
  rcases hk with rfl | ⟨w, -, hk, hwg, hwix, -, hrw⟩
  · exact WeakRvwmoGraph.gwixPos G w' hw'
  · rw [hrw] at hlt
    have := (gxhGwixLt G cs w w' hnd ((gxhGwritesElem G cs w).2 ⟨hk, hwg⟩)
      ((gxhGwritesElem G cs w').2 ⟨hc', hw'⟩)).1 hlt
    omega

/-- **`gzFetch` PASSES TO THE HULL** at the renamed tags, when the fetched bytes' sources are kept
and the hull's contributors are original, kept contributors. -/
theorem GraphFetchHullZ.gzFetchHull (G : Gexec) (cs : List Nat) (C CH : Geid → Prop) (i k : Nat)
    (base : Int) (tvs : List (Nat × BitVec 8)) :
    gwf G →
    (∀ c, CH c → C c ∧ gcut cs c = true) →
    gzFetch G C i k base tvs →
    (∀ (j t : Nat) (v : BitVec 8) (w : Geid), tvs[j]? = some (t, v) → gwriteAt G t = some w → gcut cs w = true) →
    gzFetch (gxHull G cs) CH i k base (tvs.map (tvRen (hren G cs))) := by
  intro hwf hCH hz hcl j t' v hj'
  have hnd := linNd G hwf
  rw [List.getElem?_map] at hj'
  cases htj : tvs[j]? with
  | none => rw [htj] at hj'; cases hj'
  | some tv =>
    obtain ⟨t, v0⟩ := tv
    rw [htj] at hj'
    simp only [Option.map_some, Option.some.injEq, tvRen, Prod.mk.injEq] at hj'
    obtain ⟨rfl, rfl⟩ := hj'
    obtain ⟨hz1, hz2, hz3⟩ := hz j t v0 htj
    have hkept := GraphFetchHullZ.tagKept G cs hnd t _ v0 hz1 (fun w hw => hcl j t v0 w htj hw)
    refine ⟨?_, ?_, ?_⟩
    · -- (Z1)
      rcases hkept with rfl | ⟨w, hw, hk, -, -, hwat, -⟩
      · rw [hrenZero]
        exact hz1
      · have hb := linLogByteFinalInv G t w _ v0 hw hz1
        exact linLogByteFinal (gxHull G cs) _ w _ v0 hwat ((gxhWrb G cs w _ v0).2 ⟨hk, hb⟩)
    · -- (Z2)
      intro w k' hw' hkk hm
      rcases hkept with rfl | ⟨w0, hw0, hk0, -, -, hwat, -⟩
      · rw [hrenZero] at hw'
        simp [gwriteAt] at hw'
      · rw [hwat, Option.some.injEq] at hw'
        subst hw'
        obtain ⟨hcm, hm0⟩ := (gxhGmem G cs _).1 hm
        exact (gxhGmoLt G cs _ _ hnd).2 ⟨hk0, hcm, hz2 w0 k' hw0 hkk hm0⟩
    · -- (Z3)
      intro w' v' hwb hlt
      obtain ⟨hk', hwb0⟩ := (gxhWrb G cs w' _ v').1 hwb
      have hw'g : w' ∈ gwrites G := gwritesByteGwrites G w' _ v' hwf hwb0
      have htw := GraphFetchHullZ.ltTransport G cs hnd t w' hkept hw'g hk' hlt
      obtain ⟨hzc, hzl⟩ := hz3 w' v' hwb0 htw
      refine ⟨fun c hc => ?_, fun l tl' vl wl hl' hwl => ?_⟩
      · obtain ⟨hcC, hcc⟩ := hCH c hc
        exact (gxhGmoLt G cs _ _ hnd).2 ⟨hcc, hk', hzc c hcC⟩
      · rw [List.getElem?_map] at hl'
        cases htl : tvs[l]? with
        | none => rw [htl] at hl'; cases hl'
        | some tlv =>
          obtain ⟨tl, vl0⟩ := tlv
          rw [htl] at hl'
          simp only [Option.map_some, Option.some.injEq, tvRen, Prod.mk.injEq] at hl'
          obtain ⟨rfl, rfl⟩ := hl'
          obtain ⟨hzl1, -, -⟩ := hz l tl vl0 htl
          rcases GraphFetchHullZ.tagKept G cs hnd tl _ vl0 hzl1
              (fun w hw => hcl l tl vl0 w htl hw) with rfl | ⟨wl0, hwl0, hkl, -, -, hwatl, -⟩
          · rw [hrenZero] at hwl
            simp [gwriteAt] at hwl
          · rw [hwatl, Option.some.injEq] at hwl
            subst hwl
            exact (gxhGmoLt G cs _ _ hnd).2 ⟨hkl, hk', hzl l tl vl0 wl0 htl hwl0⟩

/-- **THE FRAGMENT PASSES TO THE HULL**: a fetch edge of the hull at the renamed tags is an original
fetch edge with both ends kept. -/
theorem GraphFetchHullZ.fetchEdgeHull (G : Gexec) (cs : List Nat) (C CH : Geid → Prop) (i k : Nat)
    (base : Int) (tvs : List (Nat × BitVec 8)) (x y : Geid) :
    gwf G →
    (∀ c, CH c → C c ∧ gcut cs c = true) →
    gzFetch G C i k base tvs →
    (∀ (j t : Nat) (v : BitVec 8) (w : Geid), tvs[j]? = some (t, v) → gwriteAt G t = some w → gcut cs w = true) →
    GraphFetch.fetchEdge (gxHull G cs) CH i k base (tvs.map (tvRen (hren G cs))) x y →
    GraphFetch.fetchEdge G C i k base tvs x y ∧ gcut cs x = true ∧ gcut cs y = true := by
  intro hwf hCH hz hcl he
  have hnd := linNd G hwf
  -- the renamed entry at `j` and its kept source
  have hent : ∀ (j t' : Nat) (v : BitVec 8), (tvs.map (tvRen (hren G cs)))[j]? = some (t', v) →
      ∃ t, tvs[j]? = some (t, v) ∧ t' = hren G cs t ∧
        (t = 0 ∨ ∃ w, gwriteAt G t = some w ∧ gcut cs w = true ∧ w ∈ gwrites G ∧ gwix G w = t ∧
          gwriteAt (gxHull G cs) (hren G cs t) = some w ∧ hren G cs t = gwix (gxHull G cs) w) := by
    intro j t' v hj'
    rw [List.getElem?_map] at hj'
    cases htj : tvs[j]? with
    | none => rw [htj] at hj'; cases hj'
    | some tv =>
      obtain ⟨t, v0⟩ := tv
      rw [htj] at hj'
      simp only [Option.map_some, Option.some.injEq, tvRen, Prod.mk.injEq] at hj'
      obtain ⟨rfl, rfl⟩ := hj'
      exact ⟨t, rfl, rfl, GraphFetchHullZ.tagKept G cs hnd t _ v0 (hz j t v0 htj).1
        (fun w hw => hcl j t v0 w htj hw)⟩
  rcases he with ⟨j, t', v, k', hj', hx, hkk, hm, rfl⟩ | ⟨j, t', v, v', hj', hy, ht, hc⟩ |
    ⟨j, t', v, v', l, tl', vl, hj', hy, ht, hl', hx⟩
  · -- E1′
    obtain ⟨t, htj, rfl, hk⟩ := hent j t' v hj'
    rcases hk with rfl | ⟨w, hw, hkw, -, -, hwat, -⟩
    · rw [hrenZero] at hx
      simp [gwriteAt] at hx
    · rw [hwat, Option.some.injEq] at hx
      subst hx
      obtain ⟨hcm, hm0⟩ := (gxhGmem G cs _).1 hm
      exact ⟨.inl ⟨j, t, v, k', htj, hw, hkk, hm0, rfl⟩, hkw, hcm⟩
  · -- E2
    obtain ⟨t, htj, rfl, hk⟩ := hent j t' v hj'
    obtain ⟨hky, hy0⟩ := (gxhWrb G cs y _ v').1 hy
    have hyg := gwritesByteGwrites G y _ v' hwf hy0
    have ht0 := GraphFetchHullZ.ltTransport G cs hnd t y hk hyg hky ht
    obtain ⟨hcC, hkc⟩ := hCH x hc
    exact ⟨.inr (.inl ⟨j, t, v, v', htj, hy0, ht0, hcC⟩), hkc, hky⟩
  · -- E3
    obtain ⟨t, htj, rfl, hk⟩ := hent j t' v hj'
    obtain ⟨tl, htl, rfl, hkl⟩ := hent l tl' vl hl'
    obtain ⟨hky, hy0⟩ := (gxhWrb G cs y _ v').1 hy
    have hyg := gwritesByteGwrites G y _ v' hwf hy0
    have ht0 := GraphFetchHullZ.ltTransport G cs hnd t y hk hyg hky ht
    rcases hkl with rfl | ⟨wl, hwl, hkwl, -, -, hwatl, -⟩
    · rw [hrenZero] at hx
      simp [gwriteAt] at hx
    · rw [hwatl, Option.some.injEq] at hx
      subst hx
      exact ⟨.inr (.inr ⟨j, t, v, v', l, tl, vl, htj, hy0, ht0, htl, hwl⟩), hkwl, hky⟩

/-- The hull's contributors (at the renamed prefix emission) are original, kept contributors. -/
theorem GraphFetchHullZ.contribHull (G : Gexec) (cs : List Nat) (em em' : Hemission)
    (rest : List Eitem) (i k : Nat) (c : Geid) :
    gloadValue G → hullOk G cs →
    em.emItems = em'.emItems ++ rest →
    GraphFetch.emContrib (gxHull G cs) (emRen (hren G cs) em') i k c →
    GraphFetch.emContrib G em i k c ∧ gcut cs c = true := by
  intro hlv hok he
  rintro ⟨f, hf, hfi, ⟨hc1, hc2, hcw⟩ | ⟨r, a, t', v, hr1, hr2, hrd, hat⟩⟩
  · have hfi' := GraphFetchHullZ.emFenceIPrefix em em' rest f he
      (GraphFetchRetime.emFenceIRen _ em' f hfi)
    rw [gxhGisW] at hcw
    by_cases hcut : gcut cs c = true
    · rw [if_pos hcut] at hcw
      exact ⟨⟨f, hf, hfi', .inl ⟨hc1, hc2, hcw⟩⟩, hcut⟩
    · rw [if_neg hcut] at hcw
      cases hcw
  · have hfi' := GraphFetchHullZ.emFenceIPrefix em em' rest f he
      (GraphFetchRetime.emFenceIRen _ em' f hfi)
    obtain ⟨hrc, t, hrd0, rfl⟩ := gxhRdbInv G cs r a t' v hrd
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [hrenZero] at hat
      simp [gwriteAt] at hat
    obtain ⟨w, hw, -, -⟩ := gloadSrcElim G t a v r htpos (hlv r a t v hrd0).1
    have hwk := hullOkRf G cs r a t v w hok hrc hrd0 hw
    rw [hrenWat G cs t w hw hwk, Option.some.injEq] at hat
    subst hat
    exact ⟨⟨f, hf, hfi', .inr ⟨r, a, t, v, hr1, hr2, hrd0, hw⟩⟩, hwk⟩

/-- **THE EMISSION HALF OF THE STABILITY**: the renamed prefix of a source-closed emission
satisfies the Zifencei slot at the hull and stores its fragment in the hull's fragment. -/
theorem GraphFetchHullZ.emHull (GD : Gdexec) (cs : List Nat) (i c : Nat) (em em' : Hemission)
    (rest : List Eitem) :
    gwf GD.gdG → gloadValue GD.gdG → hullOk GD.gdG cs → cs[i]? = some c →
    em.emItems = em'.emItems ++ rest →
    (∀ it j, it ∈ em'.emItems → it.2 = some j → j < c) →
    (∀ it, em'.emItems.getLast? = some it → it.2.isSome = true) →
    GraphFetchHullZ.emSrcClosed GD.gdG cs i em →
    GraphFetch.emZif GD.gdG i em → GraphFetch.emFetchIn GD i em →
    GraphFetch.emZif (gxHull GD.gdG cs) i (emRen (hren GD.gdG cs) em') ∧
      GraphFetch.emFetchIn (gdHull GD cs) i (emRen (hren GD.gdG cs) em') := by
  intro hwf hlv hok hcs he htag hlast hcl hz hin
  -- the common decomposition of a renamed fetch item
  have hdec : ∀ (n : Nat) (base : Int) (tvs' : List (Nat × BitVec 8)), (emRen (hren GD.gdG cs) em').emItems[n]? =
        some (Wlabel.LIFetch base tvs', none) →
      ∃ tvs, em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) ∧
        tvs' = tvs.map (tvRen (hren GD.gdG cs)) ∧
        GraphFetchSpike.emSlot (emRen (hren GD.gdG cs) em').emItems n =
          GraphFetchSpike.emSlot em.emItems n ∧
        (∀ (j t : Nat) (v : BitVec 8) (w : Geid), tvs[j]? = some (t, v) → gwriteAt GD.gdG t = some w → gcut cs w = true) := by
    intro n base tvs' hn
    obtain ⟨tvs, -, hit, rfl, hlt⟩ := GraphFetchHullZ.itemHull _ em em' rest n base tvs' he hn
    obtain ⟨it, hitm, hit2, hslot⟩ := GraphFetchHullZ.slotPrefix em'.emItems rest n hlt hlast
    rw [← he] at hit2 hslot
    have hkc := htag it _ hitm hit2
    refine ⟨tvs, hit, rfl, ?_, hcl n base tvs hit (by rw [hcs]; exact hkc)⟩
    show GraphFetchSpike.emSlot (em'.emItems.map (eitemRen (hren GD.gdG cs))) n = _
    rw [GraphFetchRetime.emSlotRen, hslot]
  have hCH : ∀ k x, GraphFetch.emContrib (gxHull GD.gdG cs) (emRen (hren GD.gdG cs) em') i k x →
      GraphFetch.emContrib GD.gdG em i k x ∧ gcut cs x = true :=
    fun k x hx => GraphFetchHullZ.contribHull GD.gdG cs em em' rest i k x hlv hok he hx
  refine ⟨fun n base tvs' hn => ?_, fun x y hxy => ?_⟩
  · obtain ⟨tvs, hit, rfl, hslot, hcln⟩ := hdec n base tvs' hn
    rw [hslot]
    exact GraphFetchHullZ.gzFetchHull GD.gdG cs _ _ i _ base tvs hwf (hCH _) (hz n base tvs hit)
      hcln
  · obtain ⟨n, base, tvs', hn, hfe⟩ := hxy
    obtain ⟨tvs, hit, rfl, hslot, hcln⟩ := hdec n base tvs' hn
    rw [hslot] at hfe
    obtain ⟨hfe0, hkx, hky⟩ := GraphFetchHullZ.fetchEdgeHull GD.gdG cs _ _ i _ base tvs x y hwf
      (hCH _) (hz n base tvs hit) hcln hfe
    exact (gdHullFetch GD cs (x, y)).2 ⟨hin x y ⟨n, base, tvs, hit, hfe0⟩, hkx, hky⟩

/-! # 3. THE STABILITY -/

/-- **THE ZIFENCEI BUNDLE PASSES TO THE HULL OF EVERY CUT IN THE CLASS** (`gfexecConfHull`'s
pattern; `hullOk` for the contributors' rf-sources, load value for their existence). -/
theorem GraphFetchHullZ.gfexecConfZFHull (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (cs : List Nat) :
    gwf GF.gfGd.gdG → gloadValue GF.gfGd.gdG → hullOk GF.gfGd.gdG cs →
    dclosed cs GF.gfDev →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
    GraphFabConf.gfexecConfZF boot d0 fab (gfHull GF cs) := by
  rintro hwf hlv hok hdc ⟨h0, hnd, hbnd, -⟩ hc
  refine ⟨h0, List.Nodup.sublist (List.filter_sublist) hnd, ?_, ?_⟩
  · intro n i k hn
    have hn' := gfHullDevLookup GF cs n (i, k) hdc hn
    have hcut := gfHullDevCut GF cs n (i, k) hn
    obtain ⟨c, hcs, hkc⟩ := gcutElim cs (i, k) hcut
    change cs[i]? = some c at hcs
    change k < c at hkc
    obtain ⟨row, hrow, hlt⟩ := hbnd n i k hn'
    refine ⟨(row.take c).map (lblRen (hren GF.gfGd.gdG cs)), ?_, ?_⟩
    · show (gxHull GF.gfGd.gdG cs).gxProg[i]? = _
      rw [gxhProgLookup, hcs]
      simp [hrow]
    · simp only [List.length_map, List.length_take]
      omega
  · intro i row' hrow'
    change (gxHull GF.gfGd.gdG cs).gxProg[i]? = some row' at hrow'
    rw [gxhProgLookup] at hrow'
    cases hcs : cs[i]? with
    | none => rw [hcs] at hrow'; simp at hrow'
    | some c =>
      rw [hcs] at hrow'
      cases hrow : GF.gfGd.gdG.gxProg[i]? with
      | none => rw [hrow] at hrow'; simp at hrow'
      | some row =>
        rw [hrow] at hrow'
        simp only [Option.bind_some, Option.some.injEq] at hrow'
        subst hrow'
        obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, ⟨hfz, hfin⟩, hdep, hcl⟩ := hc i row hrow
        obtain ⟨em', hem', hpre, _⟩ := hartConffPrefix i row (boot i) dvi dvo tq em c hem
        obtain ⟨rest, hrest⟩ := hpre
        have hem'f : hemitf dvi dvo tq 0 wsInit (row.take c) (boot i) em'.emItems em'.emFin := hem'
        have htag : ∀ it j, it ∈ em'.emItems → it.2 = some j → j < c := by
          intro it j hit hj
          have := (hemitfTagLt _ _ _ _ _ _ _ _ _ it j hem'f hit hj).2
          rw [List.length_take] at this
          omega
        obtain ⟨hzH, hinH⟩ := GraphFetchHullZ.emHull GF.gfGd cs i c em em' rest hwf hlv hok hcs
          hrest.symm htag (GraphFetchHullZ.hemitfLast _ _ _ _ _ _ _ _ _ hem'f) hcl hfz hfin
        refine ⟨emRen (hren GF.gfGd.gdG cs) em', dvi, dvo, tq,
          hartConffRen _ _ _ _ _ _ _ _ hem', ?_, ?_, ⟨hzH, hinH⟩, ?_⟩
        · intro k hk
          rw [List.length_map, List.length_take] at hk
          have hkc : k < c := by omega
          have hrowH : (gfHull GF cs).gfGd.gdG.gxProg[i]? =
              some ((row.take c).map (lblRen (hren GF.gfGd.gdG cs))) := by
            show (gxHull GF.gfGd.gdG cs).gxProg[i]? = _
            rw [gxhProgLookup, hcs, hrow]
            rfl
          rw [WeakRvwmoFabInd.gisIoMapRow (hren GF.gfGd.gdG cs) GF.gfGd.gdG (gfHull GF cs).gfGd.gdG
            i k row _ hrow hrowH (by rw [List.getElem?_map, List.getElem?_take_of_lt hkc]) (by omega)]
          rw [← hiff k (by omega)]
          show (i, k) ∈ GF.gfDev.filter (gcut cs) ↔ (i, k) ∈ GF.gfDev
          rw [List.mem_filter]
          exact ⟨fun h => h.1, fun h => ⟨h, gcutIntro cs (i, k) c hcs hkc⟩⟩
        · intro k n hn
          exact hpin k n (gfHullDevLookup GF cs n (i, k) hdc hn)
        · intro jk hjk
          simp only [emRen] at hjk
          rw [rowDepsRen] at hjk
          obtain ⟨hlt1, hlt2⟩ :=
            hartConffRowDepsLt i (row.take c) (boot i) dvi dvo tq em' jk hem' hjk
          rw [List.length_take] at hlt1 hlt2
          replace hlt1 : jk.1 < c := by omega
          replace hlt2 : jk.2 < c := by omega
          exact (gdHullDeps GF.gfGd cs _).2 ⟨hdep jk (rowDepsPrefix _ _ _ ⟨rest, hrest⟩ hjk),
            gcutIntro cs (i, jk.1) c hcs hlt1, gcutIntro cs (i, jk.2) c hcs hlt2⟩

/-! # 4. THE UNGUARDED KILL -/

/-- **THE KILL OBLIGATION over the class** (`cycleKillIOZ` without the hull bundle): at a conformant
Zifencei graph every proper hull of which, cut in the class, is already `racyDIO`-acyclic, there is
no `racyDIO` cycle.  The induction hypothesis asks nothing of the hull. -/
def cycleKillIOZC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ GF : Gfexec,
    GF.gfGd.gdG.gxImg = im →
    rvwmoMinusDepsConsistent GF.gfGd →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ cs, properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x → False

/-- **The class kill IS a guarded kill**: by the stability, every cut in the class has a hull that
carries the bundle, so the guarded induction hypothesis covers it. -/
theorem cycleKillIOZOfC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    cycleKillIOZC boot d0 fab im → cycleKillIOZ boot d0 fab im := by
  intro hk GF him hc hconf hres hdr hwio hih x hcyc
  refine hk GF him hc hconf hres hdr hwio (fun cs hpc hcl => ?_) x hcyc
  exact hih cs hpc (GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hc.1.1 hc.1.2.2.1
    (properCutOk _ _ hpc.1) hpc.2 hconf hcl)

/-- The cat kill over the class (`CatLin.cycleKillCZ` without the hull bundle). -/
def CatLin.cycleKillCZC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im →
    CatLin.rvwmoCatAD GF.gfGd ad →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    (∀ cs, properCutF GF cs → GraphFetchHullZ.fetchSrcClosedCut boot fab GF cs →
      ∀ x, ¬ tc (racyDIO (gfHull GF cs)) x x) →
    ∀ x, tc (racyDIO GF) x x → False

theorem CatLin.cycleKillCZOfC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) :
    CatLin.cycleKillCZC boot d0 fab im → CatLin.cycleKillCZ boot d0 fab im := by
  intro hk GF ad him hc hconf hres hdr hih x hcyc
  refine hk GF ad him hc hconf hres hdr (fun cs hpc hcl => ?_) x hcyc
  have hcore := CatLin.catADCore _ _ hc
  exact hih cs hpc (GraphFetchHullZ.gfexecConfZFHull boot d0 fab GF cs hcore.1 hcore.2.1
    (properCutOk _ _ hpc.1) hpc.2 hconf hcl)

/-- The supply from the class kill (`t2linSupplyFZIO` through `cycleKillIOZOfC`). -/
theorem t2linSupplyFZIOC (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) :
    cycleKillIOZC boot d0 fab GF.gfGd.gdG.gxImg →
    rvwmoMinusDepsConsistent GF.gfGd → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG → gfDevWIo GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emFenceCyc em ∧ GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCandIO GF'.gfGd.gdG) ∧
      (linCandIO GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCandIO GF'.gfGd.gdG) ∧ candDiskLat (linCandIO GF'.gfGd.gdG) ∧
      trDevOrdered GF' (linCandIO GF'.gfGd.gdG) ∧
      ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
        pst 0 = (List.range' 0 N).map boot ∧
        fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr 0) = d0 ∧
        execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
          (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GF'.gfGd.gdG)) itvOf fiOf) pst
          (fun k => fab (dcnt GF' (linCandIO GF'.gfGd.gdG).cdTr k))
          (candExec (linCandIO GF'.gfGd.gdG)) ∧
        (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) :=
  fun hk => t2linSupplyFZIO boot d0 fab GF N (cycleKillIOZOfC boot d0 fab _ hk)

end Weak
