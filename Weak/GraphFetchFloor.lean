/-
Weak: **W5d-G G5 (part 2) — the floor bound** (plan rev 48 §C W5d-G G5 "the floor bound",
`notes/W5dG-spike.md` §3.3 "the pf/Ev itv there is ≤ lmax cs"; D41 RULED (a) [OWN.16]).
Lean-only, no Rocq twin.

The M2 fetch clause (`PfRunUnpinned.fcutEM2`) is the cut form at the instruction view `itvOf`,
which rises only at a `fence.i` (`PfRunUnpinned.itvStep`) to MachCSL's value `fencePost true false
tv rv (ownPub i au)` read off the TRACE shadow (`TsoShadow.shadowRun`).  `GraphFetch.linFetchCut`
(`Weak/GraphFetchCut.lean`) passes the cut form at every view at or below the fence.i
contributors' maximum.  This file supplies the bound, in the rule-14 linearization `linCand G`:

* §1 the OWN CONE `GraphFetchFloor.cone G i n`: the largest write index hart `i`'s first `n`
  events can put into a view -- an own write's index, an own read's byte sources;
* §2 **`GraphFetchFloor.coneLeContrib`**: at a fence.i site `f < k`, the cone below `f` is at or
  below the contributors' maximum at slot `k` (D41 (a)'s superset IS this cone: own writes and
  rf-sources of own reads po-before the site); `GraphFetchFloor.contribMono` (more contributors,
  larger maximum);
* §3 **`GraphFetchFloor.shadowCone`**: THE SHADOW INVARIANT -- along `linCand G`, hart `i`'s trace
  shadow has `tv`, `rv`, every coherence floor and `ownPub i au` at or below the cone of its
  events so far, and the author list is as long as the write count, for any coherence stamp that
  stamps only foreign sources and resets on stores (`TsoShadow.cohSrc`,
  `GraphFetchFloor.cohSrcLoad` / `cohSrcStore`); hence **`GraphFetchFloor.fencePostCone`**: the
  value a `fence.i` at `(i, f)` raises `itv` to is at or below `cone G i f`.

Spec marks.  No trusted text: proof organisation (FAITHFUL).  The bound is a fact about the
linearized candidate and MachCSL's `fence.i` arm, as the shadow models it.

Lean-only helpers are file-qualified (`GraphFetchFloor.*`).
-/
import Weak.GraphFetchCut
import Weak.TsoShadow

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The own cone -/

/-- What one event can put into a view: its write index (a write) and its byte sources (a read). -/
def GraphFetchFloor.evCone (G : Gexec) (e : Geid) : Nat :=
  max (if gisW G e then gwix G e else 0)
    (match gxLbl G e with
     | some l =>
       match lbRd l with
       | some (_, ts, _) => ts.foldr max 0
       | none => 0
     | none => 0)

/-- The cone of hart `i`'s first `n` events. -/
def GraphFetchFloor.cone (G : Gexec) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (GraphFetchFloor.cone G i n) (GraphFetchFloor.evCone G (i, n))

theorem GraphFetchFloor.coneMono (G : Gexec) (i : Nat) (n m : Nat) :
    n ≤ m → GraphFetchFloor.cone G i n ≤ GraphFetchFloor.cone G i m := by
  intro h
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)
    · exact Nat.le_refl _

theorem GraphFetchFloor.coneLe (G : Gexec) (i n B : Nat) :
    (∀ k, k < n → GraphFetchFloor.evCone G (i, k) ≤ B) → GraphFetchFloor.cone G i n ≤ B := by
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
    intro h
    exact Nat.max_le.2 ⟨ih (fun k hk => h k (by omega)), h n (by omega)⟩

theorem GraphFetchFloor.evConeW (G : Gexec) (e : Geid) :
    gisW G e = true → gwix G e ≤ GraphFetchFloor.evCone G e := by
  intro h
  unfold GraphFetchFloor.evCone
  rw [h]
  exact Nat.le_max_left _ _

theorem GraphFetchFloor.evConeR (G : Gexec) (e : Geid) (l : Lbl) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gxLbl G e = some l → lbRd l = some (base, ts, vs) →
    ts.foldr max 0 ≤ GraphFetchFloor.evCone G e := by
  intro hl hr
  unfold GraphFetchFloor.evCone
  rw [hl]
  simp only [hr]
  exact Nat.le_max_right _ _

/-! # 2. The cone at a site is below the contributors -/

/-- More contributors, larger maximum. -/
theorem GraphFetchFloor.contribMono (G : Gexec) (C C' : Geid → Prop) :
    (∀ c, C c → C' c) →
    (GraphFetchCut.contribIdx G C).foldr max 0 ≤ (GraphFetchCut.contribIdx G C').foldr max 0 := by
  intro h
  apply GraphFetchSpike.foldrMaxLe
  intro x hx
  obtain ⟨c, hcw, hcc, rfl⟩ := GraphFetchCut.contribIdxMem G C x hx
  apply GraphFetchSpike.leFoldrMax
  exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hcw,
    @decide_eq_true _ (Classical.propDecidable _) (h c hcc)⟩, rfl⟩

theorem GraphFetchFloor.contribIdxGe (G : Gexec) (C : Geid → Prop) (c : Geid) :
    c ∈ gwrites G → C c → gwix G c ≤ (GraphFetchCut.contribIdx G C).foldr max 0 := by
  intro hcw hcc
  apply GraphFetchSpike.leFoldrMax
  exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hcw,
    @decide_eq_true _ (Classical.propDecidable _) hcc⟩, rfl⟩

/-- A read label's sources and values have the same length (`gwf`'s shape clause). -/
theorem GraphFetchFloor.rdLen (G : Gexec) (hwf : gwf G) (e : Geid) (l : Lbl) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G e = some l → lbRd l = some (base, ts, vs) → vs.length = ts.length := by
  intro hl hr
  have hs := gwfLblShape G e l hwf hl
  cases l with
  | LLoad aq b ts0 vs0 =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact hs
  | LRmw aq rl b ts0 rvs wvs k =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact hs.2.2
  | LStore => simp [lbRd] at hr
  | LFence => simp [lbRd] at hr
  | LIo => simp [lbRd] at hr

/-- **THE CONE AT A SITE**: at a fence.i site `f < k`, everything hart `i`'s events before `f`
can put into a view is at or below the contributors' maximum at slot `k`. -/
theorem GraphFetchFloor.coneLeContrib (G : Gexec) (hc : rvwmoMinusConsistent G)
    (fi : Nat → Prop) (i f k : Nat) :
    fi f → f < k →
    GraphFetchFloor.cone G i f ≤
      (GraphFetchCut.contribIdx G (gzContrib G fi i k)).foldr max 0 := by
  intro hfi hfk
  obtain ⟨hwf, -, hlv, -⟩ := hc
  have hnd := linNd G hwf
  apply GraphFetchFloor.coneLe
  intro k' hk'
  unfold GraphFetchFloor.evCone
  refine Nat.max_le.2 ⟨?_, ?_⟩
  · cases hw : gisW G (i, k') with
    | false => exact Nat.zero_le _
    | true =>
      have hl : (gxLbl G (i, k')).isSome := by
        cases h : gxLbl G (i, k') with
        | none => simp [gisW, h] at hw
        | some _ => rfl
      exact GraphFetchFloor.contribIdxGe G _ _ (gisWGwrites G _ hwf hl hw)
        ⟨f, hfk, hfi, Or.inl ⟨rfl, hk', hw⟩⟩
  · split
    next l hl =>
      split
      next base ts vs hr =>
        apply GraphFetchSpike.foldrMaxLe
        intro t ht
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
        rcases Nat.eq_zero_or_pos t with rfl | htpos
        · exact Nat.zero_le _
        have hlen := GraphFetchFloor.rdLen G hwf _ l base ts vs hl hr
        obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v :=
          someOfIsSome (lookup_lt_is_Some_2 (by have := lookup_lt_Some hj; omega))
        have hrd : greadsByte G (i, k') (accAddr base j) t v := ⟨l, base, ts, vs, j, hl, hr, hj, hv, rfl⟩
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        obtain ⟨w, hwa, -, -⟩ := (hlv _ _ _ _ hrd).1
        obtain ⟨hwg, hwix⟩ := gwriteAtInv G _ w hnd hwa
        rw [← hwix]
        exact GraphFetchFloor.contribIdxGe G _ w hwg
          ⟨f, hfk, hfi, Or.inr ⟨(i, k'), accAddr base j, s + 1, v, rfl, hk', hrd, hwa⟩⟩
      · exact Nat.zero_le _
    · exact Nat.zero_le _

/-! # 3. The shadow invariant -/

/-- `ownPub` of a log grown by one author. -/
theorem GraphFetchFloor.ownPubAuxSnoc (h a : Nat) : ∀ (l : List Nat) (b : Nat),
    MachCSL.ownPubAux h (l ++ [a]) b =
      if a = h then b + l.length + 1 else MachCSL.ownPubAux h l b
  | [], b => by by_cases ha : a = h <;> simp [MachCSL.ownPubAux, ha]
  | x :: l, b => by
    have ih := GraphFetchFloor.ownPubAuxSnoc h a l (b + 1)
    simp only [List.cons_append, MachCSL.ownPubAux, ih, List.length_cons]
    by_cases ha : a = h
    · simp only [ha, if_true]
      have : b + 1 + l.length + 1 ≠ 0 := by omega
      simp only [ne_eq, this, not_false_eq_true, if_true]
      omega
    · simp only [ha, if_false]

theorem GraphFetchFloor.ownPubSnocSelf (h : Nat) (l : List Nat) :
    MachCSL.ownPub h (l ++ [h]) = l.length + 1 := by
  unfold MachCSL.ownPub
  rw [GraphFetchFloor.ownPubAuxSnoc]
  simp

theorem GraphFetchFloor.ownPubSnocOther (h a : Nat) (l : List Nat) :
    a ≠ h → MachCSL.ownPub h (l ++ [a]) = MachCSL.ownPub h l := by
  intro ha
  unfold MachCSL.ownPub
  rw [GraphFetchFloor.ownPubAuxSnoc]
  simp [ha]

/-- A foreign source's timestamp is at most the footprint's foreign maximum. -/
theorem GraphFetchFloor.shForeignGe (i : Nat) :
    ∀ (srcs : List (Option (Nat × Nat))) (j au t : Nat),
      srcs[j]? = some (some (au, t)) → au ≠ i → t ≤ shForeign i srcs
  | [], j, _, _, h, _ => by simp at h
  | x :: srcs, 0, au, t, h, hne => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [shForeign, hne, if_false]
    exact Nat.le_max_left _ _
  | x :: srcs, j + 1, au, t, h, hne => by
    simp only [List.getElem?_cons_succ] at h
    have ih := GraphFetchFloor.shForeignGe i srcs j au t h hne
    cases x with
    | none => simpa only [shForeign] using ih
    | some p =>
      obtain ⟨a, t'⟩ := p
      simp only [shForeign]
      split
      · exact ih
      · exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- The foreign maximum of a read's sources is at most its largest tag. -/
theorem GraphFetchFloor.shForeignLe (i : Nat) (au : List Nat) :
    ∀ ts : List Nat, shForeign i (ts.map (shSrc au)) ≤ ts.foldr max 0
  | [] => Nat.zero_le _
  | t :: ts => by
    have ih := GraphFetchFloor.shForeignLe i au ts
    have hs : ∀ a t', shSrc au t = some (a, t') → t' ≤ t := by
      intro a t' h
      unfold shSrc at h
      split at h
      · cases h; omega
      · cases hx : au[t - 1]? with
        | none => rw [hx] at h; cases h
        | some b => rw [hx] at h; cases h; exact Nat.le_refl _
    simp only [List.map_cons, List.foldr_cons]
    cases hsrc : shSrc au t with
    | none => simp only [shForeign]; omega
    | some p =>
      obtain ⟨a, t'⟩ := p
      have := hs a t' hsrc
      simp only [shForeign]
      split <;> omega

theorem GraphFetchFloor.cohMaxLe (coh : Int → Nat) (base : Int) (B : Nat) :
    (∀ a, coh a ≤ B) → ∀ n, cohMax coh base n ≤ B := by
  intro h n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.max_le.2 ⟨ih, h _⟩

/-- The minimal load view is below a bound on the floor and the foreign sources. -/
theorem GraphFetchFloor.shTvnLe (i : Nat) (sh : ShSt) (base : Int) (srcs : List (Option (Nat × Nat)))
    (B : Nat) : sh.tv ≤ B → (∀ a, sh.coh a ≤ B) → shTvn i sh base srcs ≤ max B (shForeign i srcs) := by
  intro htv hcoh
  have := GraphFetchFloor.cohMaxLe sh.coh base B hcoh srcs.length
  unfold shTvn shFloor
  omega

/-- `cohSrc` stamps only foreign sources. -/
theorem GraphFetchFloor.cohSrcLoad (i : Nat) (coh : Int → Nat) (base : Int)
    (srcs : List (Option (Nat × Nat))) (tvn : Nat) (a : Int) :
    cohSrc.load i coh base srcs tvn a ≤ max (coh a) (shForeign i srcs) := by
  simp only [cohSrc]
  cases hf : footIdx base srcs.length a with
  | none => exact Nat.le_max_left _ _
  | some j =>
    simp only
    cases hj : srcs[j]? with
    | none => exact Nat.le_max_left _ _
    | some o =>
      cases o with
      | none => exact Nat.le_max_left _ _
      | some p =>
        obtain ⟨au, t⟩ := p
        simp only
        split
        · exact Nat.le_max_left _ _
        · rename_i hne
          exact Nat.max_le.2 ⟨Nat.le_max_left _ _,
            Nat.le_trans (GraphFetchFloor.shForeignGe i srcs j au t hj hne) (Nat.le_max_right _ _)⟩

/-- `cohSrc` resets on stores. -/
theorem GraphFetchFloor.cohSrcStore (coh : Int → Nat) (base : Int) (n : Nat) (a : Int) :
    cohSrc.store coh base n a ≤ coh a := by
  simp only [cohSrc]
  cases footIdx base n a with
  | none => exact Nat.le_refl _
  | some _ => exact Nat.zero_le _

/-- The invariant: the author list has `L` entries, and `ownPub`, `tv`, `rv`, every coherence
floor are at or below the cone of the first `n` own events. -/
def GraphFetchFloor.shBound (G : Gexec) (i n L : Nat) (x : List Nat × ShSt) : Prop :=
  x.1.length = L ∧ MachCSL.ownPub i x.1 ≤ GraphFetchFloor.cone G i n ∧
  x.2.tv ≤ GraphFetchFloor.cone G i n ∧ x.2.rv ≤ GraphFetchFloor.cone G i n ∧
  ∀ a, x.2.coh a ≤ GraphFetchFloor.cone G i n

/-- One own step keeps the invariant at the next cone. -/
theorem GraphFetchFloor.stepOwn (G : Gexec) (stamp : CohStamp)
    (hL : ∀ i coh base srcs tvn a, stamp.load i coh base srcs tvn a ≤ max (coh a) (shForeign i srcs))
    (hS : ∀ coh base n a, stamp.store coh base n a ≤ coh a)
    (i n L : Nat) (l : Lbl) (x : List Nat × ShSt) :
    gxLbl G (i, n) = some l →
    GraphFetchFloor.shBound G i n L x →
    (gisW G (i, n) = true → gwix G (i, n) = L + 1) →
    GraphFetchFloor.shBound G i (n + 1) (L + if lbIsW l then 1 else 0) (shActL stamp i x ⟨i, l⟩) := by
  obtain ⟨au, sh⟩ := x
  rintro hl ⟨hlen, hpub, htv, hrv, hcoh⟩ hix
  simp only at hlen hpub htv hrv hcoh
  have hcm : GraphFetchFloor.cone G i n ≤ GraphFetchFloor.cone G i (n + 1) :=
    GraphFetchFloor.coneMono G i n (n + 1) (by omega)
  have hev : GraphFetchFloor.evCone G (i, n) ≤ GraphFetchFloor.cone G i (n + 1) :=
    Nat.le_max_right _ _
  have hwl : gisW G (i, n) = lbIsW l := by simp [gisW, hl]
  -- the write index of an own write
  have hwix : lbIsW l = true → au.length + 1 ≤ GraphFetchFloor.cone G i (n + 1) := by
    intro hw
    rw [← hwl] at hw
    have := GraphFetchFloor.evConeW G _ hw
    rw [hix hw] at this
    omega
  simp only [GraphFetchFloor.shBound, shActL, if_true]
  cases l with
  | LLoad aq base ts vs =>
    have hts := GraphFetchFloor.evConeR G _ _ base ts vs hl rfl
    have hfor := GraphFetchFloor.shForeignLe i au ts
    simp only [lbIsW, Bool.false_eq_true, if_false, Nat.add_zero, shStepL, ShSt.load]
    refine ⟨hlen, by omega, by omega, Nat.max_le.2 ⟨by omega, ?_⟩, fun a => ?_⟩
    · refine Nat.le_trans (GraphFetchFloor.shTvnLe i sh base _ _ htv hcoh) ?_
      omega
    · refine Nat.le_trans (hL _ _ _ _ _ _) ?_
      have := hcoh a
      omega
  | LStore rl base vs k =>
    simp only [lbIsW, shStepL, ShSt.store, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hw := hwix rfl
    refine ⟨by simp [hlen], ?_, by omega, by omega, fun a => ?_⟩
    · rw [GraphFetchFloor.ownPubSnocSelf]; omega
    · have := hS sh.coh base vs.length a
      have := hcoh a
      omega
  | LFence pr pw sr sw =>
    simp only [lbIsW, Bool.false_eq_true, if_false, Nat.add_zero, shStepL, ShSt.fence]
    refine ⟨hlen, by omega, ?_, by omega, fun a => by have := hcoh a; omega⟩
    exact Nat.le_trans (MachCSL.fencePost_le _ _ _ _ _ _ htv hrv hpub) hcm
  | LRmw aq rl base ts rvs wvs k =>
    simp only [lbIsW, if_true, shStepL, ShSt.excl, ShSt.store, Bool.true_and]
    have hw := hwix rfl
    refine ⟨by simp [hlen], ?_, ?_, by omega, fun a => ?_⟩
    · rw [GraphFetchFloor.ownPubSnocSelf]; omega
    · cases aq <;> (try simp only [Bool.false_eq_true, if_false, if_true]) <;> omega
    · have := hS sh.coh base wvs.length a
      have := hcoh a
      omega
  | LIo kd base vs =>
    simp only [lbIsW, Bool.false_eq_true, if_false, Nat.add_zero, shStepL]
    exact ⟨hlen, by omega, by omega, by omega, fun a => by have := hcoh a; omega⟩

/-- Another hart's step keeps the invariant. -/
theorem GraphFetchFloor.stepOther (G : Gexec) (stamp : CohStamp) (i n L j : Nat) (l : Lbl)
    (x : List Nat × ShSt) :
    j ≠ i → GraphFetchFloor.shBound G i n L x →
    GraphFetchFloor.shBound G i n (L + if lbIsW l then 1 else 0) (shActL stamp i x ⟨j, l⟩) := by
  obtain ⟨au, sh⟩ := x
  rintro hj ⟨hlen, hpub, htv, hrv, hcoh⟩
  simp only [GraphFetchFloor.shBound, shActL, hj, if_false]
  simp only at hlen hpub htv hrv hcoh
  cases hw : lbIsW l with
  | false => exact ⟨hlen, hpub, htv, hrv, hcoh⟩
  | true =>
    simp only [if_true]
    exact ⟨by simp [hlen], by rw [GraphFetchFloor.ownPubSnocOther i j au hj]; exact hpub,
      htv, hrv, hcoh⟩

/-- The own count at a trace index is the event's row position. -/
theorem GraphFetchFloor.ownCount (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (K : Nat)
    (e : Geid) :
    (glinEids G)[K]? = some e → tcnt e.1 ((linCand G).cdTr.take K) = e.2 := by
  intro hK
  have hKl : K < (glinEids G).length := lookup_lt_Some hK
  have hsplit : gevsHart G e.1 =
      ((glinEids G).take K).filter (fun x : Geid => decide (x.1 = e.1)) ++
        e :: ((glinEids G).drop (K + 1)).filter (fun x : Geid => decide (x.1 = e.1)) := by
    rw [← glinHart G hwf h14 e.1]
    conv => lhs; rw [← List.take_append_drop (K + 1) (glinEids G)]
    rw [take_S_r hK, List.filter_append, List.filter_append]
    simp
  have hc : tcnt e.1 ((linCand G).cdTr.take K) =
      (((glinEids G).take K).filter (fun x : Geid => decide (x.1 = e.1))).length := by
    unfold tcnt
    show ((((glinEids G).map (glinStep G)).take K).filter _).length = _
    rw [← List.map_take, filterFmapGlin, List.length_map]
  rw [hc]
  have hlk : (gevsHart G e.1)[(((glinEids G).take K).filter
      (fun x : Geid => decide (x.1 = e.1))).length]? = some e := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨heq, -⟩ := gevsHartLookupInv G e.1 _ e hlk
  have := congrArg Prod.snd heq
  simp only at this
  exact this.symm

/-- **THE SHADOW INVARIANT along the linearization.** -/
theorem GraphFetchFloor.shadowCone (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (stamp : CohStamp)
    (hL : ∀ i coh base srcs tvn a, stamp.load i coh base srcs tvn a ≤ max (coh a) (shForeign i srcs))
    (hS : ∀ coh base n a, stamp.store coh base n a ≤ coh a) (i : Nat) :
    ∀ K, K ≤ (glinEids G).length →
      GraphFetchFloor.shBound G i (tcnt i ((linCand G).cdTr.take K)) (linNw G K)
        (shadowRun stamp i ((linCand G).cdTr.take K)) := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨rfl, ?_, Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _⟩
    show MachCSL.ownPub i [] ≤ _
    simp [MachCSL.ownPub, MachCSL.ownPubAux]
  | succ K ih =>
    intro hK
    have hKl : K < (glinEids G).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (glinEids G)[K]? = some e :=
      someOfIsSome (lookup_lt_is_Some_2 hKl)
    have hs : (linCand G).cdTr[K]? = some (glinStep G e) := linTrLookup G K e he
    have htake : (linCand G).cdTr.take (K + 1) = (linCand G).cdTr.take K ++ [glinStep G e] := by
      rw [List.take_add_one, hs]
      rfl
    have hl := linLbl G hwf K e he
    have hwl : lbIsW (glbl G e) = gisW G e := by simp [gisW, hl]
    have hnw : linNw G (K + 1) = linNw G K + if lbIsW (glbl G e) then 1 else 0 := by
      rw [hwl]
      cases hw : gisW G e with
      | true => rw [linNwS G K e he hw]; rfl
      | false =>
        rw [GraphFetchCut.linNwSkip G K (fun e' he' => by
          rw [he, Option.some.injEq] at he'; subst he'; exact hw)]
        rfl
    rw [htake, shadowRunSnoc, hnw]
    have ih' := ih (by omega)
    by_cases hag : e.1 = i
    · have hst := tcntStepEq i _ K _ hs hag
      rw [htake] at hst
      have hcnt := GraphFetchFloor.ownCount G hwf h14 K e he
      obtain ⟨ei, ek⟩ := e
      simp only at hag hcnt
      subst hag
      rw [hst, hcnt]
      rw [hcnt] at ih'
      exact GraphFetchFloor.stepOwn G stamp hL hS ei ek (linNw G K) _ _ hl ih'
        (fun hw => gwixOfLookup G (linNw G K) _ (linNd G hwf) (linGwritesSplit G hwf K _ he hw))
    · have hne : tcnt i ((linCand G).cdTr.take (K + 1)) = tcnt i ((linCand G).cdTr.take K) :=
        tcntStepNe i _ K _ hs hag
      rw [htake] at hne
      rw [hne]
      exact GraphFetchFloor.stepOther G stamp i _ _ e.1 (glbl G e) _ hag ih'

/-- **THE FLOOR BOUND at a fence**: at hart `i`'s event `(i, f)` (trace index `K`), the value
MachCSL's `fence.i` arm raises the instruction view to -- `fencePost true false tv rv (ownPub i
au)` at the trace shadow before the step -- is at or below the cone of the events before `f`. -/
theorem GraphFetchFloor.fencePostCone (G : Gexec) (hwf : gwf G) (h14 : grule14 G)
    (stamp : CohStamp)
    (hL : ∀ i coh base srcs tvn a, stamp.load i coh base srcs tvn a ≤ max (coh a) (shForeign i srcs))
    (hS : ∀ coh base n a, stamp.store coh base n a ≤ coh a) (K i f : Nat) :
    (glinEids G)[K]? = some (i, f) →
    MachCSL.fencePost true false (shadowRun stamp i ((linCand G).cdTr.take K)).2.tv
      (shadowRun stamp i ((linCand G).cdTr.take K)).2.rv
      (MachCSL.ownPub i (shadowRun stamp i ((linCand G).cdTr.take K)).1) ≤
      GraphFetchFloor.cone G i f := by
  intro hK
  have hKl : K ≤ (glinEids G).length := Nat.le_of_lt (lookup_lt_Some hK)
  obtain ⟨-, hpub, htv, hrv, -⟩ := GraphFetchFloor.shadowCone G hwf h14 stamp hL hS i K hKl
  have hcnt := GraphFetchFloor.ownCount G hwf h14 K (i, f) hK
  simp only at hcnt
  rw [hcnt] at hpub htv hrv
  exact MachCSL.fencePost_le _ _ _ _ _ _ htv hrv hpub

/-- The instance at M2's stamp `cohSrc`. -/
theorem GraphFetchFloor.fencePostConeSrc (G : Gexec) (hwf : gwf G) (h14 : grule14 G)
    (K i f : Nat) :
    (glinEids G)[K]? = some (i, f) →
    MachCSL.fencePost true false (shadowRun cohSrc i ((linCand G).cdTr.take K)).2.tv
      (shadowRun cohSrc i ((linCand G).cdTr.take K)).2.rv
      (MachCSL.ownPub i (shadowRun cohSrc i ((linCand G).cdTr.take K)).1) ≤
      GraphFetchFloor.cone G i f :=
  GraphFetchFloor.fencePostCone G hwf h14 cohSrc GraphFetchFloor.cohSrcLoad
    GraphFetchFloor.cohSrcStore K i f

end Weak
