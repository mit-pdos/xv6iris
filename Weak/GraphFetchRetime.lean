/-
Weak: **W5d-G G4 — the Zifencei clause survives the re-timing** (plan rev 45 §C W5d-G G4,
`notes/W5dG-spike.md` §3.2; D41 RULED (a) [OWN.16], D42 RULED (a) [OWN.18]).  Lean-only, no Rocq
twin.

The normalization (`WeakRvwmoTopo.normalizeOfAcyclicX`, its I/O instance
`WeakRvwmoKillIO.normalizeOfAcyclicIO`) re-times a graph: same rows up to the read renaming
`rowsRel π`, the same write messages under the index permutation `wperm π`, a new gmo.  The fetch
clause `GraphFetch.emZif` (`gzFetch` at every administrative fetch item, E1′ form) names gmo
order and write indices, so it does NOT survive an arbitrary re-timing; it survives one that keeps
the coherence order and the FETCH FRAGMENT's edges.  This file:

* §1 THE gwlog/gwix BRIDGE.  `GraphFetchRetime.gwlogRen`: the realizing log answers the renamed
  tag `π t` at the re-timed graph exactly as it answers `t` at the original (the write at index
  `π t` of the new graph IS the write at index `t` of the old one, `wperm`, and its message is
  unchanged, `rowsRel`); byte footprints transport (`gwritesByteRen`, `greadsByteRenInv`).
* §2 THE FETCH FRAGMENT `GraphFetch.fetchEdge` (one item) / `GraphFetch.emFetchEdge` (an
  emission): the edges E1′ (a fetched byte's source → every own memory event at/after the slot),
  E2 (a fence.i contributor → a co-later write to a fetched byte), E3 (any fetched byte's source →
  such a write) — exactly the gmo facts (Z2)/(Z3) assert (`GraphFetch.fetchEdgeGmo`).
  `GraphFetch.emFetchIn GD i em` — "F_em ⊆ GD.gdFetch", the bundle clause `xv6ConfS` takes
  (mirroring `rowDeps ⊆ gdDeps`); under it every fragment edge is a FETCH ARM edge
  (`GraphFetch.emFetchGfetchE`: `WeakRvwmoAcyc.gfetchE`, the `racyDIO` arm).
* §3 CONTRIBUTOR INVARIANCE.  The re-timed emission's fence.i sites are the original's
  (`GraphFetchRetime.emFenceIRen`) and its contributors are the original's
  (`GraphFetchRetime.emContribRen`: own writes po-before a site are fixed, an rf-source is named
  by the renamed tag of the same write).
* §4 **`GraphFetch.retimeZifencei`**: a re-timing that keeps co (`gco ⊆` new gmo) and the fetch
  arm (`gfetchE ⊆` new gmo) carries `emZif` from the graph to the re-timed graph, for the renamed
  emission `emRen π em` (G2: `wlblRen` renames fetch tags).  (Z1) by the bridge; (Z2) by the kept
  E1′ edge; (Z3): a write `w'` to a fetched byte that is co-after the source in the NEW graph was
  co-after it in the old one (co is kept and total per byte on the old graph's writes), so the old
  (Z3) gives the E2/E3 edges, which are kept.
* §5 **`GraphFetch.normalizeOfAcyclicZ`**: the I/O normalization of a `racyDIO`-acyclic graph
  (whose fetch arm carries the fragment) yields a graph satisfying the renamed fetch clause at
  every hart whose emission's fragment is stored (`emFetchIn`) — the retime half of plan
  §3.2; the cut form at the realizing prefix is G5.

Spec marks.  No new trusted text: `gzFetch` (§B(11), E1′) is the trusted item; this file is proof
organisation (FAITHFUL).  The fetch arm is a proof device (an acyclicity premise's arm).

Deviation (file placement): plan §C W5d-G puts G4 in `WeakRvwmoTopo` ("new section"); `Topo` is
below `GraphFetchSpike` (which imports `Lin` → `Topo`), so `gzFetch` is not visible there.  G4
lives in this NEW leaf (outside the registered roots' closure); `Topo`/`KillIO` gain only the
co-order conjunct of the normalization (`normalizeOfAcyclicX`/`normalizeOfAcyclicIO`).  Lean-only
helpers are file-qualified (`GraphFetchRetime.*`).
-/
import Weak.GraphFetch
import Weak.WeakRvwmoKillIO

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The gwlog/gwix bridge -/

/-- A renaming of a `rowsRel`/`wperm` pair fixes `0` only. -/
theorem GraphFetchRetime.piPos (π : Nat → Nat) (G G' : Gexec) :
    rowsRel π G G' → wperm π G G' → ∀ t, 0 < t → 0 < π t := by
  intro hr hw t ht
  rcases Nat.eq_zero_or_pos (π t) with h | h
  · have := hw.1 t 0 (by rw [h, rowsRelZero π G G' hr])
    omega
  · exact h

/-- The message of an event is blind to the read renaming. -/
theorem GraphFetchRetime.gmsgRen (π : Nat → Nat) (G G' : Gexec) (e : Geid) :
    rowsRel π G G' → WeakRvwmoLin.gmsg G' e = WeakRvwmoLin.gmsg G e := by
  intro hr
  unfold WeakRvwmoLin.gmsg
  rw [rowsRelLbl π G G' e hr]
  cases gxLbl G e with
  | none => rfl
  | some l => simp [lblRenWr, lblRenCls]

/-- The realizing log, entry by entry. -/
theorem GraphFetchRetime.gwlogLookup (G : Gexec) (i : Nat) :
    (gwlog G)[i]? = ((gwrites G)[i]?).bind (WeakRvwmoLin.gmsg G) := by
  cases h : (gwrites G)[i]? with
  | some w => exact linLogFullLookup G i w h
  | none =>
    show ((gwrites G).filterMap (WeakRvwmoLin.gmsg G))[i]? = none
    rw [List.getElem?_eq_none_iff]
    exact Nat.le_trans (List.length_filterMap_le _ _) (List.getElem?_eq_none_iff.1 h)

/-- **THE BRIDGE**: the re-timed graph's log answers the renamed tag as the original answers the
tag. -/
theorem GraphFetchRetime.gwlogRen (π : Nat → Nat) (G G' : Gexec) :
    rowsRel π G G' → wperm π G G' →
    ∀ t a, logByte G'.gxImg (gwlog G') (π t) a = logByte G.gxImg (gwlog G) t a := by
  intro hr hw t a
  cases t with
  | zero => rw [rowsRelZero π G G' hr, logByte0, logByte0, rowsRelImg π G G' hr]
  | succ i =>
    have hpos := GraphFetchRetime.piPos π G G' hr hw (i + 1) (Nat.succ_pos i)
    obtain ⟨i', hi'⟩ : ∃ i', π (i + 1) = i' + 1 := ⟨π (i + 1) - 1, by omega⟩
    have hat : gwriteAt G' (π (i + 1)) = gwriteAt G (i + 1) := hw.2.1 (i + 1)
    rw [hi'] at hat
    have hat' : (gwrites G')[i']? = (gwrites G)[i]? := hat
    rw [hi', logByteS, logByteS, GraphFetchRetime.gwlogLookup, GraphFetchRetime.gwlogLookup, hat']
    cases (gwrites G)[i]? with
    | none => rfl
    | some w => simp [GraphFetchRetime.gmsgRen π G G' w hr]

/-- Write footprints transport along `rowsRel`. -/
theorem GraphFetchRetime.gwritesByteRen (π : Nat → Nat) (G G' : Gexec) (e : Geid) (a : Int)
    (v : BitVec 8) : rowsRel π G G' → (gwritesByte G' e a v ↔ gwritesByte G e a v) := by
  intro hr
  unfold gwritesByte
  rw [rowsRelLbl π G G' e hr]
  constructor
  · rintro ⟨l', base, vs, j, hl, hw, hv, ha⟩
    cases h : gxLbl G e with
    | none => rw [h] at hl; cases hl
    | some l =>
      rw [h] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      exact ⟨l, base, vs, j, rfl, by rw [← lblRenWr π l]; exact hw, hv, ha⟩
  · rintro ⟨l, base, vs, j, hl, hw, hv, ha⟩
    exact ⟨lblRen π l, base, vs, j, by rw [hl]; rfl, by rw [lblRenWr]; exact hw, hv, ha⟩

/-- A renamed read footprint is a renamed original one. -/
theorem GraphFetchRetime.lbRdRenInv (π : Nat → Nat) (l : Lbl) (base : Int) (ts' : List Nat)
    (vs : List (BitVec 8)) :
    lbRd (lblRen π l) = some (base, ts', vs) → ∃ ts, lbRd l = some (base, ts, vs) ∧ ts' = ts.map π := by
  cases l with
  | LLoad aq b ts vs0 =>
    simp only [lblRen, lbRd, Option.some.injEq, Prod.mk.injEq]
    rintro ⟨rfl, rfl, rfl⟩
    exact ⟨ts, ⟨rfl, rfl, rfl⟩, rfl⟩
  | LRmw aq rl b ts rvs wvs k =>
    simp only [lblRen, lbRd, Option.some.injEq, Prod.mk.injEq]
    rintro ⟨rfl, rfl, rfl⟩
    exact ⟨ts, ⟨rfl, rfl, rfl⟩, rfl⟩
  | LStore => simp [lblRen, lbRd]
  | LFence => simp [lblRen, lbRd]
  | LIo => simp [lblRen, lbRd]

/-- A read of the re-timed graph reads the renamed tag of an original read. -/
theorem GraphFetchRetime.greadsByteRenInv (π : Nat → Nat) (G G' : Gexec) (r : Geid) (a : Int)
    (t' : Nat) (v : BitVec 8) :
    rowsRel π G G' → greadsByte G' r a t' v → ∃ t, t' = π t ∧ greadsByte G r a t v := by
  rintro hr ⟨l', base, ts', vs, j, hl, hrd, ht, hv, ha⟩
  rw [rowsRelLbl π G G' r hr] at hl
  cases h : gxLbl G r with
  | none => rw [h] at hl; cases hl
  | some l =>
    rw [h] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    obtain ⟨ts, hrd0, rfl⟩ := GraphFetchRetime.lbRdRenInv π l base ts' vs hrd
    rw [List.getElem?_map] at ht
    cases htj : ts[j]? with
    | none => rw [htj] at ht; cases ht
    | some t =>
      rw [htj] at ht
      simp only [Option.map_some, Option.some.injEq] at ht
      exact ⟨t, ht.symm, l, base, ts, vs, j, h, hrd0, htj, hv, ha⟩

theorem GraphFetchRetime.gwixPosMem (G : Gexec) (e : Geid) : 0 < gwix G e → e ∈ gwrites G := by
  intro h
  refine Classical.byContradiction fun hn => ?_
  rw [gwixZero G e hn] at h
  exact Nat.lt_irrefl 0 h

theorem GraphFetchRetime.gwixLeLen (G : Gexec) (e : Geid) :
    e ∈ gwrites G → gwix G e ≤ (gwrites G).length := by
  intro h
  obtain ⟨s, hs, heq⟩ := gwixLookup G e h
  have := lookup_lt_Some hs
  omega

theorem GraphFetchRetime.gwriteAtGmem (G : Gexec) (t : Nat) (x : Geid) :
    gwriteAt G t = some x → gmem G x := by
  intro h
  cases t with
  | zero => cases h
  | succ i => exact WeakRvwmoAcyc.gisWGmem G x (gwritesIsw G x (gwritesLookupElem G i x h))

theorem GraphFetchRetime.gwritesByteGmem (G : Gexec) (y : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G y a v → gmem G y := by
  rintro ⟨l, base, vs, j, hl, hw, -, -⟩
  apply WeakRvwmoAcyc.gisWGmem
  simp only [gisW, hl]
  exact lbWrIsW l _ hw

theorem GraphFetchRetime.contribGmem (G : Gexec) (fi : Nat → Prop) (i k : Nat) (c : Geid) :
    gzContrib G fi i k c → gmem G c := by
  rintro ⟨f, -, -, ⟨-, -, hw⟩ | ⟨r, a, t, v, -, -, -, hat⟩⟩
  · exact WeakRvwmoAcyc.gisWGmem G c hw
  · exact GraphFetchRetime.gwriteAtGmem G t c hat

/-! # 2. The fetch fragment -/

/-- **THE FETCH EDGES** of one fetch item (hart `i`, slot `k`, contributors `C`): E1′ — a fetched
byte's source write → every memory event of hart `i` at or after the slot; E2 — a contributor →
a write to a fetched byte co-after that byte's source; E3 — any fetched byte's source → such a
write.  (`notes/W5dG-spike.md` §3.1, E1 strengthened to E1′ with (Z2).) -/
def GraphFetch.fetchEdge (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (x y : Geid) : Prop :=
  (∃ (j t : Nat) (v : BitVec 8) (k' : Nat), tvs[j]? = some (t, v) ∧ gwriteAt G t = some x ∧ k ≤ k' ∧ gmem G (i, k') ∧
    y = (i, k')) ∨
  (∃ (j t : Nat) (v v' : BitVec 8), tvs[j]? = some (t, v) ∧ gwritesByte G y (base + (j : Int)) v' ∧ t < gwix G y ∧
    C x) ∨
  (∃ (j t : Nat) (v v' : BitVec 8) (l tl : Nat) (vl : BitVec 8), tvs[j]? = some (t, v) ∧ gwritesByte G y (base + (j : Int)) v' ∧
    t < gwix G y ∧ tvs[l]? = some (tl, vl) ∧ gwriteAt G tl = some x)

/-- The fragment of hart `i`'s emission: the fetch edges of its fetch items, at their real slots
with the emission's contributors. -/
def GraphFetch.emFetchEdge (G : Gexec) (i : Nat) (em : Hemission) (x y : Geid) : Prop :=
  ∃ n base tvs, em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) ∧
    GraphFetch.fetchEdge G (GraphFetch.emContrib G em i (GraphFetchSpike.emSlot em.emItems n)) i
      (GraphFetchSpike.emSlot em.emItems n) base tvs x y

/-- **"F_em ⊆ GD.gdFetch"** — the bundle clause (`xv6ConfS`), as `rowDeps ⊆ gdDeps`. -/
def GraphFetch.emFetchIn (GD : Gdexec) (i : Nat) (em : Hemission) : Prop :=
  ∀ x y, GraphFetch.emFetchEdge GD.gdG i em x y → (x, y) ∈ GD.gdFetch

/-- Every fetch edge is gmo-forward — (Z2)/(Z3) verbatim. -/
theorem GraphFetch.fetchEdgeGmo (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    gzFetch G C i k base tvs → ∀ x y, GraphFetch.fetchEdge G C i k base tvs x y → gmoLt G x y := by
  intro hz x y h
  rcases h with ⟨j, t, v, k', hj, hx, hk, hm, rfl⟩ | ⟨j, t, v, v', hj, hy, ht, hc⟩ |
    ⟨j, t, v, v', l, tl, vl, hj, hy, ht, hl, hx⟩
  · exact (hz j t v hj).2.1 x k' hx hk hm
  · exact ((hz j t v hj).2.2 y v' hy ht).1 x hc
  · exact ((hz j t v hj).2.2 y v' hy ht).2 l tl vl x hl hx

/-- Under the fetch clause and `emFetchIn`, the emission's fragment is inside the FETCH ARM. -/
theorem GraphFetch.emFetchGfetchE (GD : Gdexec) (i : Nat) (em : Hemission) :
    GraphFetch.emZif GD.gdG i em → GraphFetch.emFetchIn GD i em →
    ∀ x y, GraphFetch.emFetchEdge GD.gdG i em x y → gfetchE GD x y := by
  intro hz hin x y he
  obtain ⟨n, base, tvs, hn, hfe⟩ := id he
  refine ⟨hin x y he, ?_, ?_, GraphFetch.fetchEdgeGmo _ _ _ _ _ _ (hz n base tvs hn) x y hfe⟩
  · rcases hfe with ⟨_, t, _, _, _, hx, _, _, _⟩ | ⟨_, _, _, _, _, _, _, hc⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, hx⟩
    · exact GraphFetchRetime.gwriteAtGmem _ t x hx
    · exact GraphFetchRetime.contribGmem _ _ _ _ x hc
    · exact GraphFetchRetime.gwriteAtGmem _ _ x hx
  · rcases hfe with ⟨_, _, _, _, _, _, _, hm, rfl⟩ | ⟨_, _, _, _, _, hy, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, hy, _, _, _⟩
    · exact hm
    · exact GraphFetchRetime.gwritesByteGmem _ y _ _ hy
    · exact GraphFetchRetime.gwritesByteGmem _ y _ _ hy

/-! # 3. Contributor invariance -/

theorem GraphFetchRetime.lastCycLRen (π : Nat → Nat) (ls : List Wlabel) :
    GraphFetch.lastCycL (ls.map (wlblRen π)) = (GraphFetch.lastCycL ls).map (wlblRen π) := by
  unfold GraphFetch.lastCycL
  rw [List.filter_map]
  have h : (GraphFetch.lbCyc ∘ wlblRen π) = GraphFetch.lbCyc := by
    funext l
    cases l <;> rfl
  rw [h, List.getLast?_map]

/-- An administrative block of the renamed item list is the renaming of one. -/
theorem GraphFetchRetime.eadmRenInv (π : Nat → Nat) (A : List Eitem) (ls' : List Wlabel) :
    A.map (eitemRen π) = eadm ls' → ∃ ls, A = eadm ls ∧ ls' = ls.map (wlblRen π) := by
  induction A generalizing ls' with
  | nil =>
    intro h
    cases ls' with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons _ _ => simp [eadm] at h
  | cons a A ih =>
    intro h
    cases ls' with
    | nil => simp [eadm] at h
    | cons l ls' =>
      simp only [List.map_cons, eadm] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨ls, rfl, rfl⟩ := ih ls' h2
      obtain ⟨a1, a2⟩ := a
      simp only [eitemRen, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨a1 :: ls, rfl, rfl⟩

/-- The renamed emission's fence.i sites are the original's. -/
theorem GraphFetchRetime.emFenceIRen (π : Nat → Nat) (em : Hemission) (f : Nat) :
    emFenceI (emRen π em) f → emFenceI em f := by
  rintro ⟨pre', ls', rest', he, hpre, hl⟩
  have he' : em.emItems.map (eitemRen π) =
      pre' ++ (eadm ls' ++ (Wlabel.LFence false false false false, some f) :: rest') := by
    rw [← List.append_assoc]
    exact he
  obtain ⟨pre, tl, hsplit, hpre', htl⟩ := List.map_eq_append_iff.1 he'
  obtain ⟨A, B, rfl, hA, hB⟩ := List.map_eq_append_iff.1 htl
  obtain ⟨b, rest, rfl, hb, -⟩ := List.map_eq_cons_iff.1 hB
  obtain ⟨ls, rfl, rfl⟩ := GraphFetchRetime.eadmRenInv π A ls' hA
  obtain ⟨b1, b2⟩ := b
  simp only [eitemRen, Prod.mk.injEq] at hb
  obtain ⟨hb1, rfl⟩ := hb
  have hb1' : b1 = Wlabel.LFence false false false false := by
    cases b1 <;> simp [wlblRen] at hb1 ⊢ <;> exact hb1
  subst hb1'
  refine ⟨pre, ls, rest, by rw [hsplit, List.append_assoc], ?_, ?_⟩
  · intro it hit
    exact hpre (eitemRen π it) (by rw [← hpre', List.getLast?_map, hit]; rfl)
  · rw [GraphFetchRetime.lastCycLRen] at hl
    cases h : GraphFetch.lastCycL ls with
    | none => rw [h] at hl; cases hl
    | some l =>
      rw [h] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      cases l <;> simp [wlblRen] at hl ⊢

/-- **CONTRIBUTOR INVARIANCE**: a contributor of the re-timed emission at the re-timed graph is a
contributor of the original at the original. -/
theorem GraphFetchRetime.emContribRen (π : Nat → Nat) (G G' : Gexec) (em : Hemission) (i k : Nat)
    (c : Geid) :
    rowsRel π G G' → wperm π G G' →
    GraphFetch.emContrib G' (emRen π em) i k c → GraphFetch.emContrib G em i k c := by
  intro hr hw
  rintro ⟨f, hf, hfi, ⟨hc1, hc2, hcw⟩ | ⟨r, a, t', v, hr1, hr2, hrd, hat⟩⟩
  · exact ⟨f, hf, GraphFetchRetime.emFenceIRen π em f hfi,
      Or.inl ⟨hc1, hc2, by rw [← rowsRelGisW π G G' c hr]; exact hcw⟩⟩
  · obtain ⟨t, rfl, hrd0⟩ := GraphFetchRetime.greadsByteRenInv π G G' r a t' v hr hrd
    exact ⟨f, hf, GraphFetchRetime.emFenceIRen π em f hfi,
      Or.inr ⟨r, a, t, v, hr1, hr2, hrd0, by rw [← hw.2.1 t]; exact hat⟩⟩

/-- Slots are blind to the renaming. -/
theorem GraphFetchRetime.emSlotRen (π : Nat → Nat) (its : List Eitem) (n : Nat) :
    GraphFetchSpike.emSlot (its.map (eitemRen π)) n = GraphFetchSpike.emSlot its n := by
  unfold GraphFetchSpike.emSlot
  have h : ∀ l : List Eitem, (l.map (eitemRen π)).filterMap Prod.snd = l.filterMap Prod.snd := by
    intro l
    rw [List.filterMap_map]
    rfl
  rw [← List.map_drop, h, h]

/-! # 4. THE RETIME THEOREM -/

/-- **`retimeZifencei`**: a re-timing (`rowsRel π`, `wperm π`) that keeps the coherence order and
the fetch arm carries the fetch clause of an emission whose fragment is stored to the re-timed
graph, at the renamed emission. -/
theorem GraphFetch.retimeZifencei (GD GD' : Gdexec) (π : Nat → Nat) (i : Nat) (em : Hemission) :
    rowsRel π GD.gdG GD'.gdG → wperm π GD.gdG GD'.gdG →
    GD.gdG.gxGmo.Nodup → GD'.gdG.gxGmo.Nodup →
    (∀ x y, gco GD.gdG x y → gmoLt GD'.gdG x y) →
    (∀ x y, gfetchE GD x y → gmoLt GD'.gdG x y) →
    GraphFetch.emFetchIn GD i em →
    GraphFetch.emZif GD.gdG i em → GraphFetch.emZif GD'.gdG i (emRen π em) := by
  intro hr hw hnd hnd' hco hfe hin hz n base tvs' hn
  have hn0 : (em.emItems.map (eitemRen π))[n]? = some (Wlabel.LIFetch base tvs', none) := hn
  rw [List.getElem?_map] at hn0
  cases hit : em.emItems[n]? with
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
      have hk : GraphFetchSpike.emSlot (emRen π em).emItems n = GraphFetchSpike.emSlot em.emItems n :=
        GraphFetchRetime.emSlotRen π em.emItems n
      rw [hk]
      have hzk := hz n b tvs hit
      intro j t' v hj'
      rw [List.getElem?_map] at hj'
      cases htj : tvs[j]? with
      | none => rw [htj] at hj'; cases hj'
      | some tv =>
        rw [htj] at hj'
        obtain ⟨t, v0⟩ := tv
        simp only [Option.map_some, Option.some.injEq, tvRen, Prod.mk.injEq] at hj'
        obtain ⟨rfl, rfl⟩ := hj'
        obtain ⟨hz1, _, hz3⟩ := hzk j t v0 htj
        refine ⟨?_, ?_, ?_⟩
        · -- (Z1) by the bridge
          rw [GraphFetchRetime.gwlogRen π _ _ hr hw]
          exact hz1
        · -- (Z2) by the kept E1′ edge
          intro w k' hat hkk hm
          have hat0 : gwriteAt GD.gdG t = some w := by rw [← hw.2.1 t]; exact hat
          have hm0 : gmem GD.gdG (i, k') := (rowsRelGmem π _ _ (i, k') hr).1 hm
          exact hfe _ _ (GraphFetch.emFetchGfetchE GD i em hz hin _ _
            ⟨n, b, tvs, hit, Or.inl ⟨j, t, v0, k', htj, hat0, hkk, hm0, rfl⟩⟩)
        · -- (Z3): co-after in the new graph ⇒ co-after in the old one; the E2/E3 edges are kept
          intro w' v' hwb hlt
          have hwb0 := (GraphFetchRetime.gwritesByteRen π _ _ w' _ v' hr).1 hwb
          have hw'm' : w' ∈ gwrites GD'.gdG := GraphFetchRetime.gwixPosMem _ w' (by omega)
          have hle' : gwix GD'.gdG w' ≤ (gwrites GD.gdG).length := by
            rw [← hw.2.2]; exact GraphFetchRetime.gwixLeLen _ w' hw'm'
          obtain ⟨t0, ht0, ht0le, hpt0⟩ :=
            wpermSurj π GD.gdG GD'.gdG (gwix GD'.gdG w') hnd' hw (by omega) hle'
          have hat0 : gwriteAt GD.gdG t0 = some w' := by
            rw [← hw.2.1 t0, hpt0]; exact gwriteAtGwix _ w' hw'm'
          obtain ⟨hw'm, hgw⟩ := gwriteAtInv GD.gdG t0 w' hnd hat0
          have htlt : t < gwix GD.gdG w' := by
            rw [hgw]
            refine Classical.byContradiction fun hge => ?_
            have hge' : t0 ≤ t := by omega
            have htpos : 0 < t := by omega
            -- the source write
            have hbd := logByteBounded _ _ _ _ (by rw [hz1]; rfl)
            have hlenlog : (gwlog GD.gdG).length ≤ (gwrites GD.gdG).length :=
              List.length_filterMap_le _ _
            obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
            obtain ⟨w, hws⟩ := someOfIsSome (lookup_lt_is_Some_2 (show s < (gwrites GD.gdG).length by omega))
            have hatw : gwriteAt GD.gdG (s + 1) = some w := hws
            have hwbw := linLogByteFinalInv GD.gdG (s + 1) w _ v0 hatw hz1
            obtain ⟨hwm, hgww⟩ := gwriteAtInv GD.gdG (s + 1) w hnd hatw
            have hatw' : gwriteAt GD'.gdG (π (s + 1)) = some w := by rw [hw.2.1]; exact hatw
            obtain ⟨hwm', hgww'⟩ := gwriteAtInv GD'.gdG _ w hnd' hatw'
            rcases Nat.lt_or_ge t0 (s + 1) with hlt0 | hge0
            · -- w' co-before the source in the old graph, so gmo-before it in the new one
              have hc : gco GD.gdG w' w := ⟨_, v', v0, hwb0, hwbw, by rw [hgw, hgww]; exact hlt0⟩
              have hmo := hco w' w hc
              have := (gwixGposLt GD'.gdG w' w hnd' hw'm' hwm').2 hmo.2.2
              omega
            · -- the source IS w'
              have heq : t0 = s + 1 := by omega
              subst heq
              rw [hatw] at hat0
              cases hat0
              omega
          obtain ⟨hz3c, hz3l⟩ := hz3 w' v' hwb0 htlt
          refine ⟨fun c hc => ?_, fun l tl' vl wl hl hatl => ?_⟩
          · have hc0 := GraphFetchRetime.emContribRen π _ _ em i _ c hr hw hc
            exact hfe _ _ (GraphFetch.emFetchGfetchE GD i em hz hin _ _
              ⟨n, b, tvs, hit, Or.inr (Or.inl ⟨j, t, v0, v', htj, hwb0, htlt, hc0⟩)⟩)
          · rw [List.getElem?_map] at hl
            cases htl : tvs[l]? with
            | none => rw [htl] at hl; cases hl
            | some tv =>
              rw [htl] at hl
              obtain ⟨tl, vl0⟩ := tv
              simp only [Option.map_some, Option.some.injEq, tvRen, Prod.mk.injEq] at hl
              obtain ⟨rfl, rfl⟩ := hl
              have hatl0 : gwriteAt GD.gdG tl = some wl := by rw [← hw.2.1 tl]; exact hatl
              exact hfe _ _ (GraphFetch.emFetchGfetchE GD i em hz hin _ _
                ⟨n, b, tvs, hit, Or.inr (Or.inr ⟨j, t, v0, v', l, tl, vl0, htj, hwb0, htlt, htl,
                  hatl0⟩)⟩)
    | _ => simp [wlblRen] at hl0

/-! # 5. At the I/O normalization -/

/-- **The fetch clause through the normalization**: a `racyDIO`-acyclic core graph re-times to an
RVWMO⁻ + rule-14 graph (`normalizeOfAcyclicIO`) that keeps the fetch fragment and satisfies the
renamed fetch clause at every hart whose emission satisfies it and stores its fragment. -/
theorem GraphFetch.normalizeOfAcyclicZ (GF : Gfexec) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GF.gfGd.gdG GD'.gdG ∧
      GD'.gdDeps = GF.gfGd.gdDeps ∧
      GD'.gdFetch = GF.gfGd.gdFetch ∧
      wperm pi GF.gfGd.gdG GD'.gdG ∧
      ∀ i em, GraphFetch.emFetchIn GF.gfGd i em → GraphFetch.emZif GF.gfGd.gdG i em →
        GraphFetch.emZif GD'.gdG i (emRen pi em) := by
  intro hcore hacy
  obtain ⟨GD', pi, hc', h14, hrr, hdeps, hw, -, -, -, -, hfe, hfa, hco⟩ :=
    normalizeOfAcyclicIO GF hcore hacy
  refine ⟨GD', pi, hc', h14, hrr, hdeps, hfe, hw, fun i em hin hz => ?_⟩
  exact GraphFetch.retimeZifencei GF.gfGd GD' pi i em hrr hw hcore.1.1 hc'.1.1.1 hco
    (fun x y h => by
      obtain ⟨-, -, -, hmo⟩ := hfa x y h
      exact hmo) hin hz

end Weak
