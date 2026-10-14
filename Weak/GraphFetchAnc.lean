/-
Weak: **W5d-G G6-3b (3) [OWN.75] — G5's cut supply on the ANCHORED trace** (plan
`notes/weak-allocproc-plan.md` rev 52, §C top "W5d-G G6 — LAUNCH PLAN [rev 50]"; the G6-3 report's
open question 3, option (a), FAITHFUL).  Lean-only, no Rocq twin.

G6-3's `topoSupplyZ` supplies M2's cut clause `fcutEM2` on the WRITE-anchored rank trace `linCand`
(G5, `GraphFetch.linFcutEM2`), while `candDiskLat` (`linCandDiskLat`) and the fabric-order guard
`trDevOrdered` (`trDevOrderedOfPtraceIO`) are theorems of the (L)-ANCHORED trace `linCandIO`
(`WeakRvwmoLin2`): the two halves of M2's conjunct spoke of two traces, and G6-3 kept both
`trDevOrdered` and `candDiskLat` as guards.  This file re-proves G5's chain on ANY admissible
anchored trace `linCandA G anc` (`ancOk G anc`; the write instance is G5's), so the cut supply,
`candDiskLat` and `trDevOrdered` all hold of `linCandIO`:

  §1  **`GraphFetchAnc.linPrefixLogA`** — the realizing step of `(i, k)` at trace index `K` sees
      the graph's write log cut at `linNwA G anc K`; `GraphFetchAnc.writeBelow`: a write gmo-before
      `(i, k)`'s NEXT OWN ANCHOR (`gnxa`) is inside that cut (rank order, `glinARankLt`);
  §2  **`GraphFetchAnc.gzFetchRelA`** — `gzFetch` IS the relational form at that cut: (Z2)'s E1′
      edge targets EVERY own memory event at or after the slot, in particular the next own anchor,
      so every source is inside the cut; every fence.i contributor is gmo-before that anchor by
      ANCHOR-14 (`granc14`, `ancOk`'s third clause — for the write anchors it is rule 14);
      `GraphFetchAnc.linFetchCutA` the cut form at the realizing prefix;
  §3  the floor bound's trace half (`ownCountA`, `shadowConeA`, `fencePostConeSrcA`) and
      **`GraphFetchAnc.itvFloorA`** — G5's proofs over the anchored trace's bookkeeping
      (`glinAHart`, `linANwS`, `linAGwritesSplit`);
  §4  **`GraphFetchAnc.linFcutEM2A`** — M2's per-index clause on `linCandA G anc`, and
      **`GraphFetchAnc.normalizeFetchSupplyIO`** — composed with the I/O normalization, on the
      normalized graph's `linCandIO`, with the residue and the disk-read anchors kept.

Spec marks.  No new trusted text: `gzFetch` (§B(11), E1′) is the trusted item; this file is proof
organisation (FAITHFUL).  Lean-only helpers are file-qualified (`GraphFetchAnc.*`).
-/
import Weak.GraphFetchRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The realizing prefix on an anchored trace -/

/-- A write gmo-before `(i, k)`'s next own anchor (any write, past the row's last anchor) is
emitted before `(i, k)`, so its write index is inside the write count there. -/
theorem GraphFetchAnc.writeBelow (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (K i k : Nat) (c : Geid) :
    (glinEidsA G anc)[K]? = some (i, k) → c ∈ gwrites G →
    (∀ a, gnxa G anc (i, k) = some a → gmoLt G c a) →
    gwix G c ≤ linNwA G anc K := by
  intro hK hc hmo
  have hnd := linNd G hwf
  have hcw := gwritesIsw G c hc
  have hca : anc c = true := hok.2.1 c hcw
  have hcl : (gxLbl G c).isSome := ancLbl G anc hok c hca
  obtain ⟨kc, hkc⟩ := glinAIndex G anc hwf hok c hcl
  have hcg : c ∈ gancs G anc := gancsOfAnc G anc hwf hok c hca
  have hlt : kc < K := by
    apply glinARankLt G anc kc K c (i, k) hkc hK
    rw [grankAAnc G anc hok c hca]
    unfold grankA
    cases hf : gnxa G anc (i, k) with
    | none =>
      have := gaixLe G anc c hcg
      simp only
      omega
    | some a =>
      obtain ⟨m, rfl, -, -, ham, -⟩ := gnxaSome G anc i k a hf
      have hag : (i, m) ∈ gancs G anc := gancsOfAnc G anc hwf hok _ ham
      exact (gaixGposLt G anc c (i, m) hnd hcg hag).2 (hmo _ hf).2.2
  have hsp := linAGwritesSplit G anc hwf hok kc c hkc hcw
  have hix := gwixOfLookup G _ c hnd hsp
  have hS := linANwS G anc kc c hkc hcw
  have hm := linANwMono G anc (kc + 1) K (by omega)
  omega

/-- The writes of the anchored trace split at index `K`. -/
theorem GraphFetchAnc.writesSplit (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (K : Nat) :
    gwrites G = ((glinEidsA G anc).take K).filter (gisW G) ++
      ((glinEidsA G anc).drop K).filter (gisW G) := by
  rw [← glinAWrites G anc hwf hok, ← List.filter_append, List.take_append_drop]

/-- **`linPrefixLog` on an anchored trace**: the log the step at index `K` sees is the graph's
write log cut at the write count. -/
theorem GraphFetchAnc.linPrefixLogA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hok : ancOk G anc) (K : Nat) :
    cdLog (linCandA G anc) K = (gwlog G).take (linNwA G anc K) := by
  rw [linALogTake, omapGmsgFilter]
  have hpre : ((glinEidsA G anc).take K).filter (gisW G) = (gwrites G).take (linNwA G anc K) := by
    rw [GraphFetchAnc.writesSplit G anc hwf hok K]
    unfold linNwA
    rw [List.take_left]
  rw [hpre]
  unfold gwlog
  exact (GraphFetchCut.filterMapTake _ _ _
    (fun e he => (gmsgIsW G e).2 (gwritesIsw G e he))).symm

/-- The cut is within the log. -/
theorem GraphFetchAnc.linNwALe (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (K : Nat) : linNwA G anc K ≤ (gwlog G).length := by
  rw [GraphFetchCut.gwlogLen, GraphFetchAnc.writesSplit G anc hwf hok K]
  unfold linNwA
  rw [List.length_append]
  omega

/-! # 2. The relational form at the anchored cut -/

/-- A fence.i contributor at slot `k` is a write, gmo-before `(i, k)`'s next own anchor
(ANCHOR-14). -/
theorem GraphFetchAnc.contribBelowA (G : Gexec) (anc : Geid → Bool) (hc : rvwmoMinusConsistent G)
    (hok : ancOk G anc) (fi : Nat → Prop) (i k : Nat) (c : Geid) :
    gzContrib G fi i k c →
    c ∈ gwrites G ∧ ∀ a, gnxa G anc (i, k) = some a → gmoLt G c a := by
  obtain ⟨hwf, hppo, hlv, -⟩ := hc
  have hnd := linNd G hwf
  rintro ⟨f, hfk, -, ⟨hc1, hc2, hcw⟩ | ⟨r, a, t, v, hr1, hr2, hrd, hat⟩⟩
  · -- an own write po-before the site
    have hcl : (gxLbl G c).isSome := by
      cases h : gxLbl G c with
      | none => simp [gisW, h] at hcw
      | some _ => rfl
    refine ⟨gisWGwrites G c hwf hcl hcw, fun a ha => ?_⟩
    obtain ⟨m, rfl, hkm, -, ham, -⟩ := gnxaSome G anc i k a ha
    have hlm : (gxLbl G (i, m)).isSome := ancLbl G anc hok _ ham
    exact hok.2.2 c (i, m) ⟨hc1, by simp only; omega, hcl, hlm⟩
      (WeakRvwmoLin.gisWGmem G c hcl hcw) ham
  · -- an rf-source of an own read po-before the site
    obtain ⟨hcw, -⟩ := gwriteAtInv G t c hnd hat
    refine ⟨hcw, fun a' ha' => ?_⟩
    obtain ⟨m, rfl, hkm, -, ham, -⟩ := gnxaSome G anc i k a' ha'
    cases t with
    | zero => simp [gwriteAt] at hat
    | succ s =>
      have hcr : gmoLt G c r := WeakRvwmoLin.grfGmo G hppo hlv r a s v c hrd hat
      have hrl := greadsByteLbl G r a (s + 1) v hrd
      have hlm : (gxLbl G (i, m)).isSome := ancLbl G anc hok _ ham
      have hrm : gmoLt G r (i, m) :=
        hok.2.2 r (i, m) ⟨hr1, by simp only; omega, hrl, hlm⟩
          (gwfGmoMem G r hwf (greadsByteMem G hwf r a _ v hrd)) ham
      exact gmoLtTrans G c r (i, m) hcr hrm

/-- **`gzFetch` IS THE RELATIONAL FORM at the anchored cut** (`GraphFetch.gzFetchRel`'s twin). -/
theorem GraphFetchAnc.gzFetchRelA (G : Gexec) (anc : Geid → Bool) (hc : rvwmoMinusConsistent G)
    (hok : ancOk G anc) (fi : Nat → Prop) (K i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    (glinEidsA G anc)[K]? = some (i, k) →
    gzFetch G (gzContrib G fi i k) i k base tvs →
    fetchRelOk G.gxImg (gwlog G) (linNwA G anc K)
      (GraphFetchCut.contribIdx G (gzContrib G fi i k)) base tvs := by
  intro hK hz
  have hwf := hc.1
  have hnd := linNd G hwf
  refine ⟨fun x hx => ?_, fun j t v hj => ?_⟩
  · obtain ⟨c, hcw, hcc, rfl⟩ := GraphFetchCut.contribIdxMem G _ x hx
    obtain ⟨-, hbel⟩ := GraphFetchAnc.contribBelowA G anc hc hok fi i k c hcc
    exact GraphFetchAnc.writeBelow G anc hwf hok K i k c hK hcw hbel
  obtain ⟨hz1, hz2, hz3⟩ := hz j t v hj
  refine ⟨hz1, ?_, fun t' htt' hs' => ?_⟩
  · -- (Z2): the source is gmo-before the next own anchor (E1′), hence inside the cut
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact Nat.zero_le _
    obtain ⟨w, hw⟩ := GraphFetchCut.gwlogWriteAt G t _ htpos (by rw [hz1]; rfl)
    obtain ⟨hwg, hwix⟩ := gwriteAtInv G t w hnd hw
    rw [← hwix]
    refine GraphFetchAnc.writeBelow G anc hwf hok K i k w hK hwg (fun a ha => ?_)
    obtain ⟨m, rfl, hkm, -, ham, -⟩ := gnxaSome G anc i k a ha
    exact hz2 w m hw hkm (hok.1 _ ham)
  · -- (Z3): a write to the byte co-after the source (cut-independent, as in G5)
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
      obtain ⟨hzl1, -, -⟩ := hz l tl vl hl
      obtain ⟨wl, hwl⟩ := GraphFetchCut.gwlogWriteAt G tl _ htlpos (by rw [hzl1]; rfl)
      obtain ⟨hwlg, hwlix⟩ := gwriteAtInv G tl wl hnd hwl
      have := (gwixGposLt G wl w' hnd hwlg hw'g).2 (hzl l tl vl wl hl hwl).2.2
      omega

/-- **THE FETCH AT ITS REALIZING STEP on an anchored trace** (`GraphFetch.linFetchCut`'s twin). -/
theorem GraphFetchAnc.linFetchCutA (G : Gexec) (anc : Geid → Bool) (hc : rvwmoMinusConsistent G)
    (hok : ancOk G anc) (fi : Nat → Prop) (K i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (itv : Nat) :
    (glinEidsA G anc)[K]? = some (i, k) →
    gzFetch G (gzContrib G fi i k) i k base tvs →
    itv ≤ (GraphFetchCut.contribIdx G (gzContrib G fi i k)).foldr max 0 →
    fetchCutOk G.gxImg (cdLog (linCandA G anc) K) (cdLog (linCandA G anc) K).length itv base tvs ∧
      ifetchOk G.gxImg (cdLog (linCandA G anc) K) itv base tvs := by
  intro hK hz hitv
  rw [GraphFetchAnc.linPrefixLogA G anc hc.1 hok K]
  exact fetchCutPrefix _ _ _ _ _ _ _ (GraphFetchAnc.linNwALe G anc hc.1 hok K) hitv
    (fetchRelCut _ _ _ _ _ _ (GraphFetchAnc.gzFetchRelA G anc hc hok fi K i k base tvs hK hz))

/-! # 3. The floor bound on an anchored trace -/

/-- The own count at a trace index is the event's row position (`GraphFetchFloor.ownCount`'s
twin). -/
theorem GraphFetchAnc.ownCountA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (K : Nat) (e : Geid) :
    (glinEidsA G anc)[K]? = some e → tcnt e.1 ((linCandA G anc).cdTr.take K) = e.2 := by
  intro hK
  have hsplit : gevsHart G e.1 =
      ((glinEidsA G anc).take K).filter (fun x : Geid => decide (x.1 = e.1)) ++
        e :: ((glinEidsA G anc).drop (K + 1)).filter (fun x : Geid => decide (x.1 = e.1)) := by
    rw [← glinAHart G anc hwf hok e.1]
    conv => lhs; rw [← List.take_append_drop (K + 1) (glinEidsA G anc)]
    rw [take_S_r hK, List.filter_append, List.filter_append]
    simp
  have hc : tcnt e.1 ((linCandA G anc).cdTr.take K) =
      (((glinEidsA G anc).take K).filter (fun x : Geid => decide (x.1 = e.1))).length := by
    unfold tcnt
    show ((((glinEidsA G anc).map (glinStep G)).take K).filter _).length = _
    rw [← List.map_take, filterFmapGlin, List.length_map]
  rw [hc]
  have hlk : (gevsHart G e.1)[(((glinEidsA G anc).take K).filter
      (fun x : Geid => decide (x.1 = e.1))).length]? = some e := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨heq, -⟩ := gevsHartLookupInv G e.1 _ e hlk
  have := congrArg Prod.snd heq
  simp only at this
  exact this.symm

/-- A non-write step appends nothing. -/
theorem GraphFetchAnc.linNwASkip (G : Gexec) (anc : Geid → Bool) (j : Nat) :
    (∀ e, (glinEidsA G anc)[j]? = some e → gisW G e = false) →
    linNwA G anc (j + 1) = linNwA G anc j := by
  intro h
  unfold linNwA
  rw [List.take_add_one, List.filter_append]
  cases he : (glinEidsA G anc)[j]? with
  | none => simp
  | some e => simp [h e he]

/-- **THE SHADOW INVARIANT along an anchored trace** (`GraphFetchFloor.shadowCone`'s twin). -/
theorem GraphFetchAnc.shadowConeA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (stamp : CohStamp)
    (hL : ∀ i coh base srcs tvn a, stamp.load i coh base srcs tvn a ≤ max (coh a) (shForeign i srcs))
    (hS : ∀ coh base n a, stamp.store coh base n a ≤ coh a) (i : Nat) :
    ∀ K, K ≤ (glinEidsA G anc).length →
      GraphFetchFloor.shBound G i (tcnt i ((linCandA G anc).cdTr.take K)) (linNwA G anc K)
        (shadowRun stamp i ((linCandA G anc).cdTr.take K)) := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨rfl, ?_, Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _⟩
    show MachCSL.ownPub i [] ≤ _
    simp [MachCSL.ownPub, MachCSL.ownPubAux]
  | succ K ih =>
    intro hK
    have hKl : K < (glinEidsA G anc).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (glinEidsA G anc)[K]? = some e :=
      someOfIsSome (lookup_lt_is_Some_2 hKl)
    have hs : (linCandA G anc).cdTr[K]? = some (glinStep G e) := linTrALookup G anc K e he
    have htake : (linCandA G anc).cdTr.take (K + 1) =
        (linCandA G anc).cdTr.take K ++ [glinStep G e] := by
      rw [List.take_add_one, hs]
      rfl
    have hl := linALbl G anc hwf hok K e he
    have hwl : lbIsW (glbl G e) = gisW G e := by simp [gisW, hl]
    have hnw : linNwA G anc (K + 1) = linNwA G anc K + if lbIsW (glbl G e) then 1 else 0 := by
      rw [hwl]
      cases hw : gisW G e with
      | true => rw [linANwS G anc K e he hw]; rfl
      | false =>
        rw [GraphFetchAnc.linNwASkip G anc K (fun e' he' => by
          rw [he, Option.some.injEq] at he'; subst he'; exact hw)]
        rfl
    rw [htake, shadowRunSnoc, hnw]
    have ih' := ih (by omega)
    by_cases hag : e.1 = i
    · have hst := tcntStepEq i _ K _ hs hag
      rw [htake] at hst
      have hcnt := GraphFetchAnc.ownCountA G anc hwf hok K e he
      obtain ⟨ei, ek⟩ := e
      simp only at hag hcnt
      subst hag
      rw [hst, hcnt]
      rw [hcnt] at ih'
      exact GraphFetchFloor.stepOwn G stamp hL hS ei ek (linNwA G anc K) _ _ hl ih'
        (fun hw => gwixOfLookup G (linNwA G anc K) _ (linNd G hwf)
          (linAGwritesSplit G anc hwf hok K _ he hw))
    · have hne : tcnt i ((linCandA G anc).cdTr.take (K + 1)) =
          tcnt i ((linCandA G anc).cdTr.take K) :=
        tcntStepNe i _ K _ hs hag
      rw [htake] at hne
      rw [hne]
      exact GraphFetchFloor.stepOther G stamp i _ _ e.1 (glbl G e) _ hag ih'

/-- **THE FLOOR BOUND at a fence**, on an anchored trace, at M2's stamp `cohSrc`. -/
theorem GraphFetchAnc.fencePostConeSrcA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G)
    (hok : ancOk G anc) (K i f : Nat) :
    (glinEidsA G anc)[K]? = some (i, f) →
    MachCSL.fencePost true false (shadowRun cohSrc i ((linCandA G anc).cdTr.take K)).2.tv
      (shadowRun cohSrc i ((linCandA G anc).cdTr.take K)).2.rv
      (MachCSL.ownPub i (shadowRun cohSrc i ((linCandA G anc).cdTr.take K)).1) ≤
      GraphFetchFloor.cone G i f := by
  intro hK
  have hKl : K ≤ (glinEidsA G anc).length := Nat.le_of_lt (lookup_lt_Some hK)
  obtain ⟨-, hpub, htv, hrv, -⟩ := GraphFetchAnc.shadowConeA G anc hwf hok cohSrc
    GraphFetchFloor.cohSrcLoad GraphFetchFloor.cohSrcStore i K hKl
  have hcnt := GraphFetchAnc.ownCountA G anc hwf hok K (i, f) hK
  simp only at hcnt
  rw [hcnt] at hpub htv hrv
  exact MachCSL.fencePost_le _ _ _ _ _ _ htv hrv hpub

/-- **THE FLOOR BOUND for `itvOfL` on an anchored trace** (`GraphFetchSupply.itvFloor`'s twin). -/
theorem GraphFetchAnc.itvFloorA (G : Gexec) (anc : Geid → Bool) (hc : rvwmoMinusConsistent G)
    (hok : ancOk G anc) (em : Nat → Hemission) (lsOf : Nat → List Wlabel)
    (hblk : ∀ K i k, (glinEidsA G anc)[K]? = some (i, k) →
      GraphFetch.emBlockF G (em i) i k (lsOf K)) :
    ∀ K, K ≤ (glinEidsA G anc).length → ∀ i,
      GraphFetchSupply.itvOfL cohSrc (candExec (linCandA G anc)) lsOf K i ≤
        (GraphFetchCut.contribIdx G
          (gzContrib G (emFenceI (em i)) i (tcnt i ((linCandA G anc).cdTr.take K)))).foldr max 0 := by
  have hwf := hc.1
  intro K
  induction K with
  | zero => intro _ i; exact Nat.zero_le _
  | succ K ih =>
    intro hK i
    have hKl : K < (glinEidsA G anc).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (glinEidsA G anc)[K]? = some e :=
      someOfIsSome (lookup_lt_is_Some_2 hKl)
    have hs : (linCandA G anc).cdTr[K]? = some (glinStep G e) := linTrALookup G anc K e he
    have hsE : (candExec (linCandA G anc)).exTr[K]? = some (glinStep G e) := hs
    have ih' := ih (by omega) i
    by_cases hag : e.1 = i
    · have hst := tcntStepEq i _ K _ hs hag
      have hcnt := GraphFetchAnc.ownCountA G anc hwf hok K e he
      obtain ⟨ei, f⟩ := e
      simp only at hag hcnt
      subst hag
      rw [hst, hcnt]
      rw [hcnt] at ih'
      have hmono := GraphFetchSupply.contribSlotMono G (emFenceI (em ei)) ei f (f + 1) (by omega)
      simp only [GraphFetchSupply.itvOfL, hsE, glinStep, ↓reduceIte]
      show PfRunUnpinned.itvStep cohSrc (candExec (linCandA G anc)) K ei _ _ ≤ _
      unfold PfRunUnpinned.itvStep
      rw [hsE]
      simp only
      split
      · rename_i hraise
        rw [Bool.and_eq_true] at hraise
        obtain ⟨hfz, harm⟩ := hraise
        have hglbl : glbl G (ei, f) = Lbl.LFence false false false false := by
          have : PfRunUnpinned.lbFenceZeroL (glbl G (ei, f)) = true := hfz
          revert this
          unfold PfRunUnpinned.lbFenceZeroL
          split <;> simp_all
        obtain ⟨l, hb, hfen⟩ := hblk K ei f he
        obtain ⟨rfl, hcyc⟩ := hfen hglbl
        have hsite : emFenceI (em ei) f := by
          refine GraphFetchSupply.emFenceIOfBlock _ f (lsOf K) hb ?_
          rw [GraphFetchSupply.fiFoldEq, GraphFetch.fiFoldLast] at harm
          cases hlc : GraphFetch.lastCycL (lsOf K) with
          | none => exact absurd hlc hcyc
          | some lc =>
            rw [hlc] at harm
            cases lc <;> simp_all [GraphFetch.isInstr]
        have hfp := GraphFetchAnc.fencePostConeSrcA G anc hwf hok K ei f he
        have hcone := GraphFetchFloor.coneLeContrib G hc (emFenceI (em ei)) ei f (f + 1) hsite
          (by omega)
        rw [candExTr] at *
        omega
      · omega
    · have hne := tcntStepNe i _ K _ hs hag
      rw [hne]
      have : GraphFetchSupply.itvOfL cohSrc (candExec (linCandA G anc)) lsOf (K + 1) i =
          GraphFetchSupply.itvOfL cohSrc (candExec (linCandA G anc)) lsOf K i := by
        simp only [GraphFetchSupply.itvOfL, hsE]
        simp only [glinStep, hag, if_false]
      rw [this]
      exact ih'

/-! # 4. THE SUPPLY on an anchored trace -/

/-- **M2'S CUT CLAUSE, SUPPLIED ON AN ANCHORED TRACE** (`GraphFetch.linFcutEM2`'s twin). -/
theorem GraphFetchAnc.linFcutEM2A (G : Gexec) (anc : Geid → Bool) (hc : rvwmoMinusConsistent G)
    (hok : ancOk G anc) (em : Nat → Hemission) (lsOf : Nat → List Wlabel)
    (hz : ∀ i, GraphFetch.emZif G i (em i))
    (hblk : ∀ K i k, (glinEidsA G anc)[K]? = some (i, k) →
      GraphFetch.emBlockF G (em i) i k (lsOf K)) :
    (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCandA G anc)) lsOf 0 i = 0) ∧
    (∀ i, GraphFetchSupply.fiOfL (candExec (linCandA G anc)).exTr lsOf 0 i = false) ∧
    ∀ K s, (candExec (linCandA G anc)).exTr[K]? = some s →
      PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandA G anc))
        (GraphFetchSupply.itvOfL cohSrc (candExec (linCandA G anc)) lsOf)
        (GraphFetchSupply.fiOfL (candExec (linCandA G anc)).exTr lsOf) K s.esAg (lsOf K)
        (stt (candExec (linCandA G anc)) K) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun K s hs => ?_⟩
  obtain ⟨hr1, hr2, hr3⟩ := GraphFetchSupply.recOk cohSrc (candExec (linCandA G anc)) lsOf K s hs
  refine ⟨fun base tvs hm => ?_, hr1, hr2, hr3⟩
  have hs' : (linCandA G anc).cdTr[K]? = some s := hs
  obtain ⟨e, he, rfl⟩ := linTrALookupInv G anc K s hs'
  obtain ⟨i, k⟩ := e
  have hKl : K ≤ (linCandA G anc).cdTr.length := by have := lookup_lt_Some hs'; omega
  obtain ⟨l, hb, -⟩ := hblk K i k he
  obtain ⟨n, hn, hslot⟩ := GraphFetchSupply.emBlockFetch (em i) k (lsOf K) l base tvs hb hm
  have hzf := hz i n base tvs hn
  rw [hslot] at hzf
  have hcnt := GraphFetchAnc.ownCountA G anc hc.1 hok K (i, k) he
  have hfl := GraphFetchAnc.itvFloorA G anc hc hok em lsOf hblk K
    (by rw [linTrALen] at hKl; exact hKl) i
  simp only at hcnt
  rw [hcnt] at hfl
  have hcut := (GraphFetchAnc.linFetchCutA G anc hc hok (emFenceI (em i)) K i k base tvs _ he hzf
    hfl).1
  have hlog : (stt (candExec (linCandA G anc)) K).msLog = cdLog (linCandA G anc) K :=
    candElog _ K hKl
  have himg : (stt (candExec (linCandA G anc)) K).msImg = G.gxImg := candEimg _ K hKl
  rw [hlog, himg]
  exact GraphFetchSupply.fcutM2OfCut _ _ _ _ _ _ hcut

/-- **THE M2 CLAUSE THROUGH THE I/O NORMALIZATION, ON `linCandIO`** (`normalizeFetchSupply`'s
twin): the normalized graph keeps the residue and the disk-read anchors (`normalizeOfAcyclicIO`),
so its (L) anchor class is admissible (`ancOkIO`) and its `linCandIO` carries M2's per-index
clause at the renamed emissions' blocks. -/
theorem GraphFetchAnc.normalizeFetchSupplyIO (GF : Gfexec) (em : Nat → Hemission) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    (∀ i, GraphFetch.emFetchIn GF.gfGd i (em i)) →
    (∀ i, GraphFetch.emZif GF.gfGd.gdG i (em i)) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GF.gfGd.gdG GD'.gdG ∧
      GD'.gdDeps = GF.gfGd.gdDeps ∧
      GD'.gdFetch = GF.gfGd.gdFetch ∧
      wperm pi GF.gfGd.gdG GD'.gdG ∧
      ioResidueGmo ⟨GD', GF.gfDev⟩ ∧
      gdiskRead14 GD'.gdG ∧
      ∀ lsOf : Nat → List Wlabel,
        (∀ K i k, (glinEidsIO GD'.gdG)[K]? = some (i, k) →
          GraphFetch.emBlockF GD'.gdG (emRen pi (em i)) i k (lsOf K)) →
        (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCandIO GD'.gdG)) lsOf 0 i = 0) ∧
        (∀ i, GraphFetchSupply.fiOfL (candExec (linCandIO GD'.gdG)).exTr lsOf 0 i = false) ∧
        ∀ K s, (candExec (linCandIO GD'.gdG)).exTr[K]? = some s →
          PfRunUnpinned.fcutEM2 cohSrc (candExec (linCandIO GD'.gdG))
            (GraphFetchSupply.itvOfL cohSrc (candExec (linCandIO GD'.gdG)) lsOf)
            (GraphFetchSupply.fiOfL (candExec (linCandIO GD'.gdG)).exTr lsOf) K s.esAg (lsOf K)
            (stt (candExec (linCandIO GD'.gdG)) K) := by
  intro hcore hacy hin hz
  obtain ⟨GD', pi, hc', h14, hrr, hdeps, hw, -, hres, hdr, -, hfe, hfa, hco⟩ :=
    normalizeOfAcyclicIO GF hcore hacy
  have hzren : ∀ i, GraphFetch.emZif GD'.gdG i (emRen pi (em i)) := fun i =>
    GraphFetch.retimeZifencei GF.gfGd GD' pi i (em i) hrr hw hcore.1.1 hc'.1.1.1 hco
      (fun x y h => by
        obtain ⟨-, -, -, hmo⟩ := hfa x y h
        exact hmo) (hin i) (hz i)
  have hok : ancOk GD'.gdG (gisAnc GD'.gdG) := ancOkIO ⟨GD', GF.gfDev⟩ h14 hres hdr
  refine ⟨GD', pi, hc', h14, hrr, hdeps, hfe, hw, hres, hdr, fun lsOf hblk => ?_⟩
  exact GraphFetchAnc.linFcutEM2A GD'.gdG (gisAnc GD'.gdG) hc'.1 hok (fun i => emRen pi (em i))
    lsOf hzren hblk

end Weak
