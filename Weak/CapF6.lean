/-
Weak: **W11-F [OWN.102] increment 9 — A2's FLOOR EQUATION, candidate side**.  Lean-only, no Rocq twin.

`readAt` (`Weak/RvwmoXv6Adequacy.lean:272`) asks, at a realized read of a foreign message at log
position `p`, that the reader's coherence floor at the byte IS the read's source: `coh pa = p + 1`
(`chainOkAt` names exactly the entry the floor equals).  The load sets the floor to
`max (old floor) t` (`cohSrc`, MachCSL's `HRead.afterLoad`), so the equation needs `old ≤ t`.  That
is coherence (CoRR) of the realized candidate: the old floor is the timestamp of an earlier write of
the byte (or 0), it is at or below the load's view (`scaOkT`'s floor clause), and the load returns
the LATEST visible write (`scaByte`).  This file proves it on the candidate (`Exec`) shadow:

* `CapF6.cohLogged img log coh` — every floor is 0 or the timestamp of a write of the byte;
  `CapF6.cohLoggedLoad`/`…Store`/`…Grow` its step laws; `CapF6.cohLoggedRun` — along every
  `execScaT` execution, at every prefix, for every agent;
* `CapF6.cohLoadEq` — at one load: a foreign-sourced byte's new floor IS its source;
* `CapF6.cohAfterLoad` — THE FLOOR EQUATION at the candidate: after the `k`-th step, a plain load of
  agent `s.esAg` reading byte `j` from the foreign timestamp `t`, the agent's shadow floor at that
  byte is `t`.

Remaining for A2: transport to the realized MachCSL state (`SimRel.view` = `viewRel cohSrc`, the M2
run's shadow per prefix).  Spec: FAITHFUL (a property of the sRVWMO candidate; proof organisation).
Every name is file-qualified (`CapF6.*`).
-/
import Weak.TsoShadow

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-- Every coherence floor is 0 or the timestamp of a (logged or image) write of its byte. -/
def CapF6.cohLogged (img : Image) (log : List Wmsg) (coh : Int → Nat) : Prop :=
  ∀ a, coh a = 0 ∨ (logByte img log (coh a) a).isSome

theorem CapF6.cohLoggedZero (img : Image) (log : List Wmsg) : CapF6.cohLogged img log (fun _ => 0) :=
  fun _ => Or.inl rfl

theorem CapF6.cohLoggedGrow (img : Image) (log l : List Wmsg) (coh : Int → Nat) :
    CapF6.cohLogged img log coh → CapF6.cohLogged img (log ++ l) coh := by
  intro h a
  rcases h a with h | h
  · exact Or.inl h
  · right
    rw [logByteApp img log l _ a (logByteBounded img log _ a h)]
    exact h

theorem CapF6.cohLoggedPrefix (img : Image) (log log' : List Wmsg) (coh : Int → Nat) :
    log <+: log' → CapF6.cohLogged img log coh → CapF6.cohLogged img log' coh := by
  rintro ⟨l, rfl⟩ h
  exact CapF6.cohLoggedGrow img log l coh h

theorem CapF6.cohLoggedStore (img : Image) (log : List Wmsg) (coh : Int → Nat) (base : Int) (n : Nat) :
    CapF6.cohLogged img log coh → CapF6.cohLogged img log (cohSrc.store coh base n) := by
  intro h a
  cases hf : footIdx base n a with
  | some j => left; simp only [cohSrc, hf]
  | none => rw [cohSrcStoreOut coh base n a hf]; exact h a

/-- A source's timestamp is the read timestamp. -/
theorem CapF6.shSrcT (au : List Nat) (t x t1 : Nat) (h : shSrc au t = some (x, t1)) : t1 = t := by
  unfold shSrc at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · cases hq : au[t - 1]? with
    | none => rw [hq] at h; cases h
    | some y =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm

/-- The load's step law: every new floor is an old one or a byte's source. -/
theorem CapF6.cohLoggedLoad (img : Image) (log : List Wmsg) (i : Nat) (au : List Nat) (sh : ShSt)
    (base : Int) (ts : List Nat) (tvn : Nat)
    (hsca : ∀ (j t : Nat), ts[j]? = some t → scaByte img log i tvn (accAddr base j) t) :
    CapF6.cohLogged img log sh.coh →
    CapF6.cohLogged img log (sh.load cohSrc i base (ts.map (shSrc au))).coh := by
  intro h a
  unfold ShSt.load
  dsimp only
  generalize shTvn i sh base (ts.map (shSrc au)) = T
  cases hf : footIdx base (ts.map (shSrc au)).length a with
  | none => rw [cohSrcLoadOut i sh.coh base _ T a hf]; exact h a
  | some j =>
    obtain ⟨hjl, rfl⟩ := (footIdxSome base _ a j).1 hf
    have hjl' : j < ts.length := by simpa using hjl
    obtain ⟨t0, hts⟩ : ∃ t0, ts[j]? = some t0 := ⟨ts[j], List.getElem?_eq_getElem hjl'⟩
    have ht0 := (hsca j t0 hts).1
    cases hsr : shSrc au t0 with
    | none =>
      have hs : (ts.map (shSrc au))[j]? = some none := by rw [List.getElem?_map, hts]; simp [hsr]
      have e : cohSrc.load i sh.coh base (ts.map (shSrc au)) T (accAddr base j) =
          sh.coh (accAddr base j) := by
        simp only [cohSrc, footIdxAcc base _ j hjl, hs]
      rw [e]; exact h _
    | some xt =>
      obtain ⟨x, t1⟩ := xt
      have e1 := CapF6.shSrcT au t0 x t1 hsr
      subst e1
      have hs : (ts.map (shSrc au))[j]? = some (some (x, t1)) := by
        rw [List.getElem?_map, hts]; simp [hsr]
      by_cases hx : x = i
      · subst hx
        rw [cohSrcLoadOwn x sh.coh base _ T j t1 hs]; exact h _
      · rw [cohSrcLoadForeign i sh.coh base _ T j x t1 hs hx]
        rcases Nat.le_total (sh.coh (accAddr base j)) t1 with hle | hle
        · rw [Nat.max_eq_right hle]; exact Or.inr ht0
        · rw [Nat.max_eq_left hle]; exact h _

/-- **THE FLOOR AT ONE LOAD** (header): a foreign-sourced byte's new floor IS its source. -/
theorem CapF6.cohLoadEq (img : Image) (log : List Wmsg) (i : Nat) (au : List Nat) (sh : ShSt)
    (base : Int) (ts : List Nat) (hlog : CapF6.cohLogged img log sh.coh)
    (hsca : scaOkT sh img log i base ts) (j t au' : Nat) (hj : ts[j]? = some t)
    (hsrc : shSrc au t = some (au', t)) (hne : au' ≠ i) :
    (sh.load cohSrc i base (ts.map (shSrc au))).coh (accAddr base j) = t := by
  obtain ⟨tvn, -, hfl, hb⟩ := hsca
  have hjl : j < ts.length := lookup_lt_Some hj
  have hs : (ts.map (shSrc au))[j]? = some (some (au', t)) := by
    rw [List.getElem?_map, hj]; simp [hsrc]
  unfold ShSt.load
  dsimp only
  rw [cohSrcLoadForeign i sh.coh base _ _ j au' t hs hne]
  suffices hle : sh.coh (accAddr base j) ≤ t by omega
  rcases hlog (accAddr base j) with h0 | hw
  · omega
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    have hvis : scaVis log i tvn (sh.coh (accAddr base j)) := by
      left
      exact Nat.le_trans ((shFloorGe sh base ts.length).2 j hjl) hfl
    exact (hb j t hj).2.2 _ hlt hw hvis

/-- The take of a successor index. -/
theorem CapF6.takeSucc {α : Type} (l : List α) (k : Nat) (x : α) (h : l[k]? = some x) :
    l.take (k + 1) = l.take k ++ [x] := by
  rw [List.take_succ, h]; rfl

/-- **THE INVARIANT ALONG THE CANDIDATE** (header). -/
theorem CapF6.cohLoggedRun (E : Exec) (hwf : execWf E) (hsca : execScaT cohSrc E) (i : Nat) :
    ∀ k, k ≤ E.exTr.length →
      CapF6.cohLogged (stt E k).msImg (stt E k).msLog (shadowOf cohSrc (E.exTr.take k) i).coh := by
  intro k
  induction k with
  | zero => intro _; exact CapF6.cohLoggedZero _ _
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ := someOfIsSome (execTrLookup E k (by omega))
    have hI := ih (by omega)
    have himg : (stt E (k + 1)).msImg = (stt E k).msImg := by
      have h1 := execImgConst E (k + 1) hwf hk
      have h2 := execImgConst E k hwf (by omega)
      unfold eimg at h1 h2; rw [h1, h2]
    have hpre : (stt E k).msLog <+: (stt E (k + 1)).msLog :=
      execLogPrefix E k (k + 1) hwf (by omega) hk
    rw [himg]
    refine CapF6.cohLoggedPrefix _ _ _ _ hpre ?_
    unfold shadowOf
    rw [CapF6.takeSucc _ _ _ hs, shadowRunSnoc]
    unfold shActL
    dsimp only
    split
    · rename_i hag
      unfold shStepL
      split
      · rename_i aq base ts vs hl
        obtain ⟨tvn, -, -, hb⟩ := hsca k s hs aq base ts vs hl
        exact CapF6.cohLoggedLoad _ _ _ _ _ base ts tvn (by rw [hag] at hb; exact hb) hI
      · exact CapF6.cohLoggedStore _ _ _ _ _ hI
      · exact hI
      · exact CapF6.cohLoggedStore _ _ _ _ _ hI
      · exact hI
    · exact hI

/-- **THE FLOOR EQUATION AT THE CANDIDATE** (header): after the `k`-th step, a plain load of
`s.esAg` reading byte `j` from a FOREIGN timestamp `t` (its source in the shadow's author list),
the agent's floor at the byte is `t`. -/
theorem CapF6.cohAfterLoad (E : Exec) (hwf : execWf E) (hsca : execScaT cohSrc E) (k : Nat)
    (s : Estep) (hs : E.exTr[k]? = some s) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (hl : s.esLb = .LLoad aq base ts vs) (j t au' : Nat) (hj : ts[j]? = some t)
    (hsrc : shSrc (shadowRun cohSrc s.esAg (E.exTr.take k)).1 t = some (au', t))
    (hne : au' ≠ s.esAg) :
    (shadowOf cohSrc (E.exTr.take (k + 1)) s.esAg).coh (accAddr base j) = t := by
  have hk : k < E.exTr.length := lookup_lt_Some hs
  have hI := CapF6.cohLoggedRun E hwf hsca s.esAg k (by omega)
  unfold shadowOf
  rw [CapF6.takeSucc _ _ _ hs, shadowRunSnoc]
  unfold shActL
  simp only [if_true, hl, shStepL]
  exact CapF6.cohLoadEq _ _ _ _ _ base ts hI (hsca k s hs aq base ts vs hl) j t au' hj hsrc hne

end Weak
