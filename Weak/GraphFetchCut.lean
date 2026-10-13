/-
Weak: **W5d-G G5 (part 1) — the realizing prefix and the graph cut form** (plan rev 48 §C W5d-G
G5, `notes/W5dG-spike.md` §3.3; D27 RULED (a) [OWN.6], D41 RULED (a) [OWN.16], D42–D43 RULED (a)
[OWN.18]).  Lean-only, no Rocq twin.

The rule-14 linearization `linCand G` (`WeakRvwmoLin`) runs hart `i`'s event `(i, k)` inside the
SEGMENT of its next own write `gnxw G (i, k)`.  So the log the realizing step sees is a PREFIX of
the graph's write log `gwlog G`, cut just below that write -- the spike's `gfcut`.  This file
proves it and moves the trusted-base item `gzFetch` to the cut form there:

* §1 **`linNwCut`** / **`linPrefixLog`**: at `(glinEids G)[K]? = some (i, k)`, the number of
  writes the first `K` trace steps append is `gfcut G i k`, and `cdLog (linCand G) K =
  (gwlog G).take (gfcut G i k)` (ranks below come first, the block's own write is its last
  element, ranks above come after; a hart's tail sits past every write);
* §2 **`GraphFetch.gzFetchRel`**: on an RVWMO⁻ + rule-14 graph, `gzFetch` at the fence.i
  contributors `gzContrib G fi i k` is the RELATIONAL form `fetchRelOk` over `(gwlog G, gfcut G i
  k)` at the contributors' write indices `GraphFetchCut.contribIdx`: (Z1) verbatim; (Z2)'s E1′
  edge to the next own write puts every source at or below the cut; (Z3) gives `c < t'` and
  `tl < t'` for every write `t'` to a fetched byte co-after its source; every contributor is
  below the cut (an own write po-before the slot, or an rf-source of an own read po-before it,
  is gmo-before the next own write by rule 14 and rf's gmo-forwardness);
* §3 **`GraphFetch.gzFetchCutOf`** -- THE GRAPH CUT FORM `gzFetchCut G i k (lmax cs)` with the
  [W2s] per-byte bound (plan §B(4)(iii): "W5d-G's G5 `gzFetchCut` must produce it");
* §4 **`GraphFetch.linFetchCut`** -- at the realizing prefix: for every instruction view `itv`
  at or below the contributors' maximum (the floor bound's conclusion), the cut form on
  `cdLog (linCand G) K` bounded by its length (W5d's M2 clause shape) and the per-byte check
  `ifetchOk … itv` there.

Spec marks.  No new trusted text: `gzFetch` (§B(11), E1′; D41 (a)'s contributor superset) is the
trusted item, `fetchCutOk` is the spike's cut form; this file is proof organisation (FAITHFUL).

Deviation (file placement): plan §C W5d-G G5 puts `linPrefixLog` in `WeakRvwmoLin`; it names
`gfcut`/`gwlog` (`GraphFetchSpike`, which imports `Lin`), so it lives in this NEW leaf (as G4's
`GraphFetchRetime`).  Lean-only helpers are file-qualified (`GraphFetchCut.*`).
-/
import Weak.GraphFetch

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The realizing prefix -/

/-- Trace order bounds rank order from below (the blocks are emitted in rank order). -/
theorem GraphFetchCut.glinRankLe (G : Gexec) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 → k1 ≤ k2 →
    WeakRvwmoLin.grank G e1 ≤ WeakRvwmoLin.grank G e2 := by
  intro h1 h2 hle
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · exact stronglySortedLookupElim _ _ k1 k2 e1 e2
      (rblocksRankSorted (WeakRvwmoLin.grank G) (gevs G) (grankBound G)) h1 h2 hlt
  · rw [h1, Option.some.injEq] at h2
    rw [h2]
    exact Nat.le_refl _

/-- A non-write step appends nothing. -/
theorem GraphFetchCut.linNwSkip (G : Gexec) (j : Nat) :
    (∀ e, (glinEids G)[j]? = some e → gisW G e = false) → linNw G (j + 1) = linNw G j := by
  intro h
  unfold linNw
  rw [List.take_add_one, List.filter_append]
  cases he : (glinEids G)[j]? with
  | none => simp
  | some e => simp [h e he]

/-- No write between two trace indices: the write count is the same at both. -/
theorem GraphFetchCut.linNwStable (G : Gexec) (K d : Nat) :
    (∀ j e, K ≤ j → j < K + d → (glinEids G)[j]? = some e → gisW G e = false) →
    linNw G (K + d) = linNw G K := by
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    rw [← Nat.add_assoc, GraphFetchCut.linNwSkip G (K + d)
      (fun e he => h (K + d) e (by omega) (by omega) he)]
    exact ih (fun j e h1 h2 he => h j e h1 (by omega) he)

/-- The writes of the trace split at index `K`. -/
theorem GraphFetchCut.glinWritesSplit (G : Gexec) (hwf : gwf G) (K : Nat) :
    gwrites G = ((glinEids G).take K).filter (gisW G) ++ ((glinEids G).drop K).filter (gisW G) := by
  rw [← glinWrites G hwf, ← List.filter_append, List.take_append_drop]

/-- **The write count at the realizing index IS the cut**: the first `K` steps of `linCand G`
append exactly the writes below `(i, k)`'s next own write (all writes, past the hart's last). -/
theorem linNwCut (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (K i k : Nat) :
    (glinEids G)[K]? = some (i, k) → linNw G K = gfcut G i k := by
  intro hK
  have hnd := linNd G hwf
  have hl := glinLookupLbl G hwf K _ hK
  obtain ⟨hi, hk⟩ := (gxLblBounds G (i, k)).1 hl
  simp only at hi hk
  unfold gfcut
  cases hf : gnxw G (i, k) with
  | some w =>
    obtain ⟨m, rfl, hkm, hm, hwm, -⟩ := gnxwSome G i k w hf
    have hlm := glblSome G i m hi hm
    have hwg : (i, m) ∈ gwrites G := gisWGwrites G (i, m) hwf hlm hwm
    obtain ⟨Kw, hKw⟩ := glinIndex G hwf (i, m) hlm
    have hrk : WeakRvwmoLin.grank G (i, k) = gwix G (i, m) := by
      unfold WeakRvwmoLin.grank
      rw [hf]
    have hKle : K ≤ Kw := by
      rcases Nat.lt_or_eq_of_le hkm with hlt | heq
      · exact Nat.le_of_lt (glinPoLt G hwf h14 K Kw (i, k) (i, m) hK hKw rfl hlt)
      · subst heq
        exact Nat.le_of_eq (NoDup_lookup (glinNodup G) hK hKw)
    have hstab : linNw G (K + (Kw - K)) = linNw G K := by
      apply GraphFetchCut.linNwStable
      intro j e h1 h2 he
      cases hwe : gisW G e with
      | false => rfl
      | true =>
        exfalso
        have hel := glinLookupLbl G hwf j e he
        have heg : e ∈ gwrites G := gisWGwrites G e hwf hel hwe
        have r1 := GraphFetchCut.glinRankLe G K j _ e hK he h1
        have r2 := GraphFetchCut.glinRankLe G j Kw e _ he hKw (by omega)
        rw [hrk] at r1
        rw [grankWrite G hwf e heg, grankWrite G hwf _ hwg] at r2
        rw [grankWrite G hwf e heg] at r1
        have heq : e = (i, m) := gwixInj G e (i, m) hnd heg hwg (by omega)
        subst heq
        have := NoDup_lookup (glinNodup G) he hKw
        omega
    rw [show K + (Kw - K) = Kw by omega] at hstab
    have hsp := linGwritesSplit G hwf Kw (i, m) hKw hwm
    have hix := gwixOfLookup G (linNw G Kw) (i, m) hnd hsp
    dsimp only
    omega
  | none =>
    have hdrop : ((glinEids G).drop K).filter (gisW G) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hwe
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
      rw [List.getElem?_drop] at hj
      have hel := glinLookupLbl G hwf (K + j) e hj
      have heg : e ∈ gwrites G := gisWGwrites G e hwf hel hwe
      have r1 := GraphFetchCut.glinRankLe G K (K + j) _ e hK hj (by omega)
      have hrk : WeakRvwmoLin.grank G (i, k) = (gwrites G).length + 1 + i := by
        unfold WeakRvwmoLin.grank
        rw [hf]
      rw [hrk, grankWrite G hwf e heg] at r1
      have := gwixLe G e heg
      omega
    have hsp := GraphFetchCut.glinWritesSplit G hwf K
    rw [hdrop, List.append_nil] at hsp
    dsimp only
    unfold linNw
    rw [← hsp]

/-- `filterMap` of a function total on the list commutes with `take`. -/
theorem GraphFetchCut.filterMapTake {A B : Type _} (f : A → Option B) :
    ∀ (l : List A) (n : Nat), (∀ x, x ∈ l → (f x).isSome) →
      (l.filterMap f).take n = (l.take n).filterMap f
  | [], n, _ => by simp
  | x :: l, n, h => by
    obtain ⟨y, hy⟩ := someOfIsSome (h x List.mem_cons_self)
    cases n with
    | zero => simp
    | succ n =>
      rw [List.filterMap_cons, hy, List.take_succ_cons, List.take_succ_cons, List.filterMap_cons, hy]
      simp only [List.cons.injEq, true_and]
      exact GraphFetchCut.filterMapTake f l n (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- Every write carries a message, so the realizing log is as long as the write list. -/
theorem GraphFetchCut.gwlogLen (G : Gexec) : (gwlog G).length = (gwrites G).length := by
  unfold gwlog
  rw [omapGmsgLen, List.filter_eq_self.2 (fun e he => gwritesIsw G e he)]

/-- A position inside a hart's row is a labelled event. -/
theorem GraphFetchCut.growLbl (G : Gexec) (i m : Nat) :
    m < (WeakRvwmoLin.grow G i).length → (gxLbl G (i, m)).isSome := by
  intro hm
  have hi : i < G.gxProg.length := by
    refine Classical.byContradiction fun h => ?_
    unfold WeakRvwmoLin.grow at hm
    rw [List.getElem?_eq_none (by omega)] at hm
    simp at hm
  exact glblSome G i m hi hm

/-- The cut is within the log. -/
theorem GraphFetchCut.gfcutLe (G : Gexec) (hwf : gwf G) (i k : Nat) :
    gfcut G i k ≤ (gwlog G).length := by
  rw [GraphFetchCut.gwlogLen]
  unfold gfcut
  cases hf : gnxw G (i, k) with
  | none => exact Nat.le_refl _
  | some w =>
    obtain ⟨m, rfl, -, hm, hwm, -⟩ := gnxwSome G i k w hf
    have := gwixLe G (i, m) (gisWGwrites G (i, m) hwf (GraphFetchCut.growLbl G i m hm) hwm)
    dsimp only
    omega

/-- **`linPrefixLog`** (plan §C W5d-G G5): the log the realizing step of `(i, k)` sees in the
rule-14 linearization is the graph's write log cut below `(i, k)`'s next own write. -/
theorem linPrefixLog (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (K i k : Nat) :
    (glinEids G)[K]? = some (i, k) → cdLog (linCand G) K = (gwlog G).take (gfcut G i k) := by
  intro hK
  rw [← linNwCut G hwf h14 K i k hK, linLogTake, omapGmsgFilter]
  have hpre : ((glinEids G).take K).filter (gisW G) = (gwrites G).take (linNw G K) := by
    rw [GraphFetchCut.glinWritesSplit G hwf K]
    unfold linNw
    rw [List.take_left]
  rw [hpre]
  unfold gwlog
  exact (GraphFetchCut.filterMapTake _ _ _
    (fun e he => (gmsgIsW G e).2 (gwritesIsw G e he))).symm

/-! # 2. The relational form at the graph -/

/-- The contributors' write indices (the contributor SET as a list, through `gwrites`). -/
noncomputable def GraphFetchCut.contribIdx (G : Gexec) (C : Geid → Prop) : List Nat :=
  ((gwrites G).filter (fun c => @decide (C c) (Classical.propDecidable _))).map (gwix G)

theorem GraphFetchCut.contribIdxMem (G : Gexec) (C : Geid → Prop) (x : Nat) :
    x ∈ GraphFetchCut.contribIdx G C → ∃ c, c ∈ gwrites G ∧ C c ∧ x = gwix G c := by
  intro hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hcw, hcc⟩ := List.mem_filter.1 hc
  exact ⟨c, hcw, @of_decide_eq_true _ (Classical.propDecidable _) hcc, rfl⟩

/-- A fence.i contributor at slot `k` is a write, gmo-before `(i, k)`'s next own write. -/
theorem GraphFetchCut.contribBelow (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (fi : Nat → Prop) (i k : Nat) (c : Geid) :
    gzContrib G fi i k c →
    c ∈ gwrites G ∧ ∀ m, gnxw G (i, k) = some (i, m) → gmoLt G c (i, m) := by
  obtain ⟨hwf, hppo, hlv, -⟩ := hc
  have hnd := linNd G hwf
  rintro ⟨f, hfk, -, ⟨hc1, hc2, hcw⟩ | ⟨r, a, t, v, hr1, hr2, hrd, hat⟩⟩
  · -- an own write po-before the site
    have hcl : (gxLbl G c).isSome := by
      cases h : gxLbl G c with
      | none => simp [gisW, h] at hcw
      | some _ => rfl
    refine ⟨gisWGwrites G c hwf hcl hcw, fun m hm => ?_⟩
    obtain ⟨m', hmm, hkm, hmlen, hwm, -⟩ := gnxwSome G i k _ hm
    simp only [Prod.mk.injEq, true_and] at hmm
    subst hmm
    obtain ⟨hi, -⟩ := (gxLblBounds G c).1 hcl
    have hlm : (gxLbl G (i, m)).isSome := glblSome G i m (by rw [← hc1]; exact hi) hmlen
    exact h14 c (i, m) ⟨hc1, by simp only; omega, hcl, hlm⟩
      (WeakRvwmoLin.gisWGmem G c hcl hcw) (WeakRvwmoLin.gisWGlblIs G _ hlm hwm)
  · -- an rf-source of an own read po-before the site
    obtain ⟨hcw, -⟩ := gwriteAtInv G t c hnd hat
    refine ⟨hcw, fun m hm => ?_⟩
    obtain ⟨m', hmm, hkm, hmlen, hwm, -⟩ := gnxwSome G i k _ hm
    simp only [Prod.mk.injEq, true_and] at hmm
    subst hmm
    cases t with
    | zero => simp [gwriteAt] at hat
    | succ s =>
      have hcr : gmoLt G c r := WeakRvwmoLin.grfGmo G hppo hlv r a s v c hrd hat
      have hrl := greadsByteLbl G r a (s + 1) v hrd
      obtain ⟨hi, -⟩ := (gxLblBounds G r).1 hrl
      have hlm : (gxLbl G (i, m)).isSome := glblSome G i m (by rw [← hr1]; exact hi) hmlen
      have hrm : gmoLt G r (i, m) :=
        h14 r (i, m) ⟨hr1, by simp only; omega, hrl, hlm⟩
          (gwfGmoMem G r hwf (greadsByteMem G hwf r a _ v hrd))
          (WeakRvwmoLin.gisWGlblIs G _ hlm hwm)
      exact gmoLtTrans G c r (i, m) hcr hrm

/-- Every contributor index is at or below the cut. -/
theorem GraphFetchCut.contribLeCut (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (fi : Nat → Prop) (i k : Nat) :
    ∀ x, x ∈ GraphFetchCut.contribIdx G (gzContrib G fi i k) → x ≤ gfcut G i k := by
  intro x hx
  have hnd := linNd G hc.1
  obtain ⟨c, hcw, hcc, rfl⟩ := GraphFetchCut.contribIdxMem G _ x hx
  obtain ⟨-, hbel⟩ := GraphFetchCut.contribBelow G hc h14 fi i k c hcc
  unfold gfcut
  cases hf : gnxw G (i, k) with
  | none => exact gwixLe G c hcw
  | some w =>
    obtain ⟨m, rfl, -, hm, hwm, -⟩ := gnxwSome G i k w hf
    have hmo := hbel m hf
    have hwg : (i, m) ∈ gwrites G :=
      gisWGwrites G (i, m) hc.1 (GraphFetchCut.growLbl G i m hm) hwm
    have := (gwixGposLt G c (i, m) hnd hcw hwg).2 hmo.2.2
    dsimp only
    omega

/-- A tag the realizing log answers is a write index (or the image). -/
theorem GraphFetchCut.gwlogWriteAt (G : Gexec) (t : Nat) (a : Int) :
    0 < t → (logByte G.gxImg (gwlog G) t a).isSome → ∃ w, gwriteAt G t = some w := by
  intro ht hs
  have hb := logByteBounded _ _ _ _ hs
  rw [GraphFetchCut.gwlogLen] at hb
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact someOfIsSome (lookup_lt_is_Some_2 (show s < (gwrites G).length by omega))

/-- **`gzFetch` IS THE RELATIONAL FORM at the cut**: on an RVWMO⁻ + rule-14 graph, the
trusted-base item at the fence.i contributors of slot `k` gives `fetchRelOk` over the realizing
log, bounded by `gfcut G i k`, at the contributors' write indices. -/
theorem GraphFetch.gzFetchRel (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (fi : Nat → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    gzFetch G (gzContrib G fi i k) i k base tvs →
    fetchRelOk G.gxImg (gwlog G) (gfcut G i k)
      (GraphFetchCut.contribIdx G (gzContrib G fi i k)) base tvs := by
  intro hz
  have hwf := hc.1
  have hnd := linNd G hwf
  refine ⟨GraphFetchCut.contribLeCut G hc h14 fi i k, fun j t v hj => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ := hz j t v hj
  refine ⟨hz1, ?_, fun t' htt' hs' => ?_⟩
  · -- (Z2): the source is at or below the cut
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact Nat.zero_le _
    obtain ⟨w, hw⟩ := GraphFetchCut.gwlogWriteAt G t _ htpos (by rw [hz1]; rfl)
    obtain ⟨hwg, hwix⟩ := gwriteAtInv G t w hnd hw
    unfold gfcut
    cases hf : gnxw G (i, k) with
    | none => rw [← hwix]; exact gwixLe G w hwg
    | some w0 =>
      obtain ⟨m, rfl, hkm, hm, hwm, -⟩ := gnxwSome G i k w0 hf
      have hlm := GraphFetchCut.growLbl G i m hm
      have hmo := hz2 w m hw hkm (WeakRvwmoLin.gisWGmem G _ hlm hwm)
      have := (gwixGposLt G w (i, m) hnd hwg (gisWGwrites G (i, m) hwf hlm hwm)).2 hmo.2.2
      dsimp only
      omega
  · -- (Z3): a write to the byte co-after the source
    obtain ⟨w', hw'⟩ := GraphFetchCut.gwlogWriteAt G t' _ (by omega) hs'
    obtain ⟨hw'g, hw'ix⟩ := gwriteAtInv G t' w' hnd hw'
    obtain ⟨v', hv'⟩ := someOfIsSome hs'
    have hwb : gwritesByte G w' (base + (j : Int)) v' := linLogByteFinalInv G t' w' _ v' hw' hv'
    obtain ⟨hzc, hzl⟩ := hz3 w' v' hwb (by rw [hw'ix]; exact htt')
    refine ⟨fun x hx => ?_, fun l tl vl hl => ?_⟩
    · obtain ⟨c, hcw, hcc, rfl⟩ := GraphFetchCut.contribIdxMem G _ x hx
      have := (gwixGposLt G c w' hnd hcw hw'g).2 (hzc c hcc).2.2
      omega
    · rcases Nat.eq_zero_or_pos tl with rfl | htlpos
      · omega
      obtain ⟨hl1, -, -⟩ := hz j t v hj
      obtain ⟨hzl1, -, -⟩ := hz l tl vl hl
      obtain ⟨wl, hwl⟩ := GraphFetchCut.gwlogWriteAt G tl _ htlpos (by rw [hzl1]; rfl)
      obtain ⟨hwlg, hwlix⟩ := gwriteAtInv G tl wl hnd hwl
      have := (gwixGposLt G wl w' hnd hwlg hw'g).2 (hzl l tl vl wl hl hwl).2.2
      omega

/-! # 3. The graph cut form -/

/-- **THE GRAPH CUT FORM** (plan §B(4)(iii) [W2s]: "G5's `gzFetchCut` must produce it"): one view
`q` with `lmax cs ≤ q ≤ gfcut`, every byte admissible at `q`, every byte's source at or below
`q`. -/
theorem GraphFetch.gzFetchCutOf (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (fi : Nat → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    gzFetch G (gzContrib G fi i k) i k base tvs →
    gzFetchCut G i k ((GraphFetchCut.contribIdx G (gzContrib G fi i k)).foldr max 0) base tvs :=
  fun hz => fetchRelCut _ _ _ _ _ _ (GraphFetch.gzFetchRel G hc h14 fi i k base tvs hz)

/-! # 4. At the realizing prefix -/

/-- **THE FETCH AT ITS REALIZING STEP**: in the rule-14 linearization, at `(i, k)`'s trace index
`K`, a fetch satisfying `gzFetch` at slot `k` passes the cut form on the prefix log (bounded by
its length -- W5d's M2 clause shape) and the per-byte check, at every instruction view at or
below the contributors' maximum. -/
theorem GraphFetch.linFetchCut (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (fi : Nat → Prop) (K i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (itv : Nat) :
    (glinEids G)[K]? = some (i, k) →
    gzFetch G (gzContrib G fi i k) i k base tvs →
    itv ≤ (GraphFetchCut.contribIdx G (gzContrib G fi i k)).foldr max 0 →
    fetchCutOk G.gxImg (cdLog (linCand G) K) (cdLog (linCand G) K).length itv base tvs ∧
      ifetchOk G.gxImg (cdLog (linCand G) K) itv base tvs := by
  intro hK hz hitv
  rw [linPrefixLog G hc.1 h14 K i k hK]
  exact fetchCutPrefix _ _ _ _ _ _ _ (GraphFetchCut.gfcutLe G hc.1 i k) hitv
    (GraphFetch.gzFetchCutOf G hc h14 fi i k base tvs hz)

end Weak
