/-
Weak: **`linCandSca` — single-copy atomicity is DERIVED at Stage 2** (allocproc
plan §C W11 (iv), the plain-SCA half "(iv)a"; §B(9) "At Stage 2 `candSca` is
DERIVED", §B(10) "the SCA witness `tvn_sca := #writes gmo-before r`").

Lean-only (no Rocq source).  `PfRunShape.candSca` (clause (iii) of the shaped
replay) asks every plain `LLoad` of a candidate to be explained by ONE view
`tvn ≤ |log|` (`scaOk`, TsoMem's `Hist.read`).  On the linearization
`linCand G` of an RVWMO⁻-consistent rule-14 graph this is a THEOREM, not a
premise: `gloadValue` gives every byte of a load event a gmo-before source that
is co-MAXIMAL among the visible same-byte writes, so the witness

  `tvnSca G r` = the number of writes gmo-before `r`

works for all bytes at once.  The pieces:

  (1) `gwixLeTvnSca` — the gmo-before-`r` writes are a PREFIX of the
      gmo-sorted `gwrites G`, so `gwix w ≤ tvnSca G r ↔ w <gmo r`;
  (2) `tvnScaMono` — `tvnSca` is monotone along gmo;
  (3) the two NAMED linearization facts (W13 (L) re-proves only these):
      `linGmoEmitBefore` (a write gmo-before `r` is emitted before `r`, the
      rank argument of `WeakRvwmoLin.linSourceBefore` generalized) and
      `linLogEmitted` (a write inside `r`'s prefix log is emitted before `r`);
  (4) `linTvnScaLe` — `tvnSca G r ≤ |cdLog (linCand G) k|`;
  (5) `linScaOk` — the per-load `scaOk` with witness `tvnSca G r`;
  (6) `linCandSca` — `rvwmoMinusConsistent G → grule14 G → candSca (linCand G)`.

No exhaustive case split on `Lbl`/`Wlabel` (W13 (E) adds `Lbl.LIo` arms in
parallel): labels are reached through `lbRd`/`lbWr`/`gisW`/`greadsByte`/
`gwritesByte` and equations with a known constructor.  Lean-only helpers are
file-qualified (`RvwmoXv6Sca.*`).
-/
import Weak.WeakRvwmoLin
import Weak.PfRunShape

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! ## The witness -/

/-- Lean-only: `gmoLt` is decidable (a local twin of `WeakRvwmoDec.gmoLtDec`, which this file
does not import). -/
local instance RvwmoXv6Sca.gmoLtDec (G : Gexec) (x y : Geid) : Decidable (gmoLt G x y) := by
  unfold gmoLt; infer_instance

/-- THE SCA WITNESS of a load event `r` (§B(10) `tvn_sca`): the number of writes
gmo-before `r`. -/
def tvnSca (G : Gexec) (r : Geid) : Nat :=
  ((gwrites G).filter (fun w => decide (gmoLt G w r))).length

/-! ## List helpers -/

/-- Lean-only: for a predicate DOWNWARD CLOSED along `l`, the `i`-th element
satisfies it iff `i` is inside the filtered prefix. -/
theorem RvwmoXv6Sca.filterDownLen {A : Type _} (p : A → Bool) (l : List A) (i : Nat) (x : A) :
    List.Pairwise (fun x y => p y = true → p x = true) l → l[i]? = some x →
    (i + 1 ≤ (l.filter p).length ↔ p x = true) := by
  induction l generalizing i with
  | nil => intro _ h; simp at h
  | cons a l ih =>
    intro hpw hi
    rw [List.pairwise_cons] at hpw
    obtain ⟨hhd, htl⟩ := hpw
    cases ha : p a with
    | true =>
      rw [List.filter_cons_of_pos ha, List.length_cons]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp [ha]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        rw [← ih i htl hi]
        constructor <;> intro h <;> omega
    | false =>
      have hnone : l.filter p = [] :=
        List.filter_eq_nil_iff.2 (fun y hy hpy => by rw [hhd y hy hpy] at ha; cases ha)
      rw [List.filter_cons_of_neg (by rw [ha]; simp), hnone]
      have hx : p x = false := by
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; exact ha
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          have hxl := elem_of_list_lookup_2 hi
          cases hpx : p x with
          | false => rfl
          | true => rw [hhd x hxl hpx] at ha; cases ha
      rw [hx]
      simp

/-- Lean-only: filtering by a weaker predicate keeps at least as many elements. -/
theorem RvwmoXv6Sca.filterLenMono {A : Type _} (p q : A → Bool) (l : List A) :
    (∀ x, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length := by
  intro hpq
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (hpq a hp)]
      simp only [List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; simp)]
      cases hq : q a with
      | true => rw [List.filter_cons_of_pos hq]; simp only [List.length_cons]; omega
      | false => rw [List.filter_cons_of_neg (by rw [hq]; simp)]; exact ih

/-! ## (1) `gwix ≤ tvnSca ↔ gmo-before` -/

theorem gwixLeTvnSca (G : Gexec) (r w : Geid) :
    gwf G → w ∈ gwrites G → (gwix G w ≤ tvnSca G r ↔ gmoLt G w r) := by
  intro hwf hw
  obtain ⟨i, hi, hix⟩ := gwixLookup G w hw
  rw [hix]
  have hpw : List.Pairwise
      (fun x y => decide (gmoLt G y r) = true → decide (gmoLt G x r) = true) (gwrites G) := by
    refine List.Pairwise.imp_of_mem ?_ (gwritesSorted G (linNd G hwf))
    intro x y hx _ hxy hy
    have hy' := of_decide_eq_true hy
    exact decide_eq_true ⟨gwritesGmo G x hx, hy'.2.1, by have := hy'.2.2; omega⟩
  unfold tvnSca
  rw [RvwmoXv6Sca.filterDownLen _ _ i w hpw hi]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-! ## (2) Monotone along gmo -/

theorem tvnScaMono (G : Gexec) (x y : Geid) : gmoLt G x y → tvnSca G x ≤ tvnSca G y := by
  intro hxy
  unfold tvnSca
  exact RvwmoXv6Sca.filterLenMono _ _ _
    (fun w h => decide_eq_true (gmoLtTrans G w x y (of_decide_eq_true h) hxy))

/-! ## (3) The two linearization facts -/

/-- A write gmo-before `r` is EMITTED before `r` in the linearization: its rank
is its `gwix`, and `r`'s rank is the `gwix` of its next write (gmo-after the
write by rule 14) or a past-the-end tail slot. -/
theorem linGmoEmitBefore (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k kw : Nat) (r w : Geid) :
    (glinEids G)[k]? = some r → (glinEids G)[kw]? = some w → w ∈ gwrites G →
    gmoLt G w r → kw < k := by
  intro hk hkw hw hmo
  apply glinRankLt G kw k w r hkw hk
  rw [grankWrite G hwf w hw]
  have hrl := glinLookupLbl G hwf k r hk
  obtain ⟨hri, hrk⟩ := (gxLblBounds G r).1 hrl
  obtain ⟨ir, kr⟩ := r
  simp only at hri hrk
  unfold WeakRvwmoLin.grank
  cases hf : gnxw G (ir, kr) with
  | none => have := gwixLe G w hw; dsimp only; omega
  | some w' =>
    obtain ⟨m, rfl, hkm, hm, hwm, _⟩ := gnxwSome G ir kr w' hf
    have hlm := glblSome G ir m hri hm
    have hmo' : gmoLt G w (ir, m) := by
      by_cases hkm' : kr = m
      · subst hkm'; exact hmo
      · apply gmoLtTrans G w (ir, kr) (ir, m) hmo
        exact h14 _ _ ⟨rfl, show kr < m by omega, hrl, hlm⟩
          (gwfGmoMem G (ir, kr) hwf hmo.2.1)
          (WeakRvwmoLin.gisWGlblIs G _ hlm hwm)
    dsimp only
    exact (gwixGposLt G w (ir, m) (linNd G hwf) hw
      (gisWGwrites G (ir, m) hwf hlm hwm)).2 hmo'.2.2

/-- A write named inside `r`'s prefix log is EMITTED before `r`. -/
theorem linLogEmitted (G : Gexec) (hwf : gwf G) (k t' : Nat) (r w' : Geid) :
    (glinEids G)[k]? = some r → gwriteAt G t' = some w' →
    t' ≤ (cdLog (linCand G) k).length →
    ∃ k', k' < k ∧ (glinEids G)[k']? = some w' := by
  intro _ hwa hle
  cases t' with
  | zero => simp [gwriteAt] at hwa
  | succ i =>
    have hi : (gwrites G)[i]? = some w' := hwa
    have hw := gwritesLookupElem G i w' hi
    obtain ⟨kw, hkw⟩ := glinIndex G hwf w' (gwritesLbl G hwf w' hw)
    have hsp := linGwritesSplit G hwf kw w' hkw (gwritesIsw G w' hw)
    have heq : linNw G kw = i := NoDup_lookup (gwritesNodup G (linNd G hwf)) hsp hi
    rw [linLogLen] at hle
    refine ⟨kw, ?_, hkw⟩
    by_cases hlt : kw < k
    · exact hlt
    · have := linNwMono G k kw (by omega)
      omega

/-! ## (4) The witness fits in the prefix log -/

theorem linTvnScaLe (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k : Nat) (r : Geid) :
    (glinEids G)[k]? = some r → tvnSca G r ≤ (cdLog (linCand G) k).length := by
  intro hk
  rw [linLogLen]
  have hlen : tvnSca G r ≤ (gwrites G).length := List.length_filter_le _ _
  cases hn : tvnSca G r with
  | zero => omega
  | succ n =>
    rw [hn] at hlen
    obtain ⟨w, hw⟩ := someOfIsSome (lookup_lt_is_Some_2 (show n < (gwrites G).length by omega))
    have hwm := gwritesLookupElem G n w hw
    have hix := gwixOfLookup G n w (linNd G hwf) hw
    have hmo : gmoLt G w r := (gwixLeTvnSca G r w hwf hwm).1 (by rw [hix, hn]; exact Nat.le_refl _)
    obtain ⟨kw, hkw⟩ := glinIndex G hwf w (gwritesLbl G hwf w hwm)
    have hlt := linGmoEmitBefore G hwf h14 k kw r w hk hkw hwm hmo
    have hsp := linGwritesSplit G hwf kw w hkw (gwritesIsw G w hwm)
    have heq : linNw G kw = n := NoDup_lookup (gwritesNodup G (linNd G hwf)) hsp hw
    have hS := linNwS G kw w hkw (gwritesIsw G w hwm)
    have := linNwMono G (kw + 1) k (by omega)
    omega

/-! ## (5) Per-load single-copy atomicity -/

/-- Lean-only: `r`'s prefix log is a prefix of the final log. -/
theorem RvwmoXv6Sca.linLogPrefix (G : Gexec) (hwf : gwf G) (k : Nat) :
    ∃ rest, (gwrites G).filterMap (WeakRvwmoLin.gmsg G) = cdLog (linCand G) k ++ rest := by
  refine ⟨((glinEids G).drop k).filterMap (WeakRvwmoLin.gmsg G), ?_⟩
  rw [← linFullLog G hwf]
  simp only [linLogTake]
  rw [linTrLen, take_ge (Nat.le_refl _), ← List.filterMap_append, List.take_append_drop]

/-- Lean-only: a graph message is authored by its event's agent. -/
theorem RvwmoXv6Sca.gmsgTid (G : Gexec) (w : Geid) (m : Wmsg) :
    WeakRvwmoLin.gmsg G w = some m → m.wmTid = some w.1 := by
  unfold WeakRvwmoLin.gmsg
  cases gxLbl G w with
  | none => simp
  | some l =>
    dsimp only
    cases lbWr l with
    | none => simp
    | some p =>
      intro h
      simp only [Option.some.injEq] at h
      subst h
      rfl

theorem linScaOk (G : Gexec) (k : Nat) (r : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G → grule14 G → (glinEids G)[k]? = some r →
    gxLbl G r = some (LLoad aq base ts vs) →
    scaOk G.gxImg (cdLog (linCand G) k) r.1 base ts := by
  rintro ⟨hwf, hppo, hlv, _⟩ h14 hk hl
  have hnd := linNd G hwf
  have hsh : vs.length = ts.length := gwfLblShape G r _ hwf hl
  obtain ⟨rest, hfull⟩ := RvwmoXv6Sca.linLogPrefix G hwf k
  have hLB : ∀ t a, t ≤ (cdLog (linCand G) k).length →
      logByte G.gxImg (cdLog (linCand G) k) t a =
        logByte G.gxImg ((gwrites G).filterMap (WeakRvwmoLin.gmsg G)) t a := by
    intro t a ht
    rw [hfull, logByteApp _ _ _ _ _ ht]
  refine ⟨tvnSca G r, linTvnScaLe G hwf h14 k r hk, ?_⟩
  intro j t hj
  obtain ⟨v, hv⟩ := someOfIsSome
    (lookup_lt_is_Some_2 (show j < vs.length by rw [hsh]; exact lookup_lt_Some hj))
  have hrd : greadsByte G r (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
  have htle := linReadTsLe G hwf hppo hlv h14 k r _ t v hk hrd
  refine ⟨?_, ?_, ?_⟩
  · -- the source byte is in the prefix log
    rw [hLB t _ htle]
    cases t with
    | zero => rw [logByte0, (hlv r _ 0 v hrd).1]; rfl
    | succ i =>
      obtain ⟨w, hwa, hwb, _⟩ := (hlv r _ (i + 1) v hrd).1
      rw [linLogByteFinal G (i + 1) w _ v hwa hwb]; rfl
  · -- the source is at or below the witness
    left
    cases t with
    | zero => exact Nat.zero_le _
    | succ i =>
      obtain ⟨w, hwa, _, _⟩ := (hlv r _ (i + 1) v hrd).1
      have hmo := WeakRvwmoLin.grfGmo G hppo hlv r _ i v w hrd hwa
      obtain ⟨hw, hix⟩ := gwriteAtInv G (i + 1) w hnd hwa
      rw [← hix]
      exact (gwixLeTvnSca G r w hwf hw).2 hmo
  · -- no later visible same-byte write
    intro t' htt' hsome hvis
    have ht'le := logByteBounded _ _ _ _ hsome
    cases t' with
    | zero => omega
    | succ i' =>
      have hi'lt : i' < (cdLog (linCand G) k).length := by omega
      obtain ⟨m, hm⟩ := someOfIsSome (lookup_lt_is_Some_2 hi'lt)
      have hmf : ((gwrites G).filterMap (WeakRvwmoLin.gmsg G))[i']? = some m := by
        rw [hfull]; exact lookup_app_l_Some hm
      have hgl : i' < (gwrites G).length :=
        Nat.lt_of_lt_of_le (lookup_lt_Some hmf) (List.length_filterMap_le _ _)
      obtain ⟨w', hw'⟩ := someOfIsSome (lookup_lt_is_Some_2 hgl)
      have hgm : WeakRvwmoLin.gmsg G w' = some m := by
        rw [← linLogFullLookup G i' w' hw', hmf]
      have hw'm := gwritesLookupElem G i' w' hw'
      have hix := gwixOfLookup G i' w' hnd hw'
      rw [logByteS, hm] at hsome
      obtain ⟨v', hv'⟩ := someOfIsSome (show (msgByte m (accAddr base j)).isSome from hsome)
      have hwb := gmsgByteInv G w' m _ v' hgm hv'
      have hvis' : gvisible G w' r := by
        rcases hvis with hle | ⟨_, m0, hm0, htid⟩
        · exact Or.inl ((gwixLeTvnSca G r w' hwf hw'm).1 (by rw [hix]; exact hle))
        · simp only [Nat.add_sub_cancel] at hm0
          rw [hm, Option.some.injEq] at hm0
          subst hm0
          rw [RvwmoXv6Sca.gmsgTid G w' m hgm, Option.some.injEq] at htid
          obtain ⟨k', hk', hk'w⟩ := linLogEmitted G hwf k (i' + 1) r w' hk hw' ht'le
          refine Or.inr ⟨htid, ?_, glinLookupLbl G hwf k' w' hk'w, glinLookupLbl G hwf k r hk⟩
          exact (glinPoIff G hwf h14 k' k w' r hk'w hk htid).1 hk'
      have := gcomax G hlv r _ t v w' v' hrd hwb hvis'
      omega

/-! ## (6) The candidate theorem -/

theorem linCandSca (G : Gexec) : rvwmoMinusConsistent G → grule14 G → candSca (linCand G) := by
  intro hc h14 k s hs aq base ts vs hlb
  have hwf := hc.1
  rw [candExTr] at hs
  have hkle : k ≤ (linCand G).cdTr.length := by have := lookup_lt_Some hs; omega
  obtain ⟨e, he, rfl⟩ := linTrLookupInv G k s hs
  have hl : gxLbl G e = some (LLoad aq base ts vs) := by
    rw [linLbl G hwf k e he]
    exact congrArg some hlb
  show scaOk (eimg (candExec (linCand G)) k) (elog (candExec (linCand G)) k) e.1 base ts
  rw [candEimg _ k hkle, candElog _ k hkle]
  exact linScaOk G k e aq base ts vs hc h14 he hl

end Weak
