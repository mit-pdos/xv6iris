/-
Weak/Prom: **E-b — track (b)'s adequacy WITHOUT (P2) `fetchBounded`** (G4 deciding experiment E-b, owner ruling
[OWN.P11]; G4-review.md §4(1), §6).

* `nf_simF` — the simulation of NfrFetch.lean's NF runs (`nfStepsF relClass … M`) by the language of OwnLang.lean:
  OwnLang's `nf_sim` for the `prom`/`st`/`rel` groups, and the prophecy-fed fetch `fet` as ONE hart step of the
  language's new constructor `hstepO.fetch` ([E-b], OwnLang.lean: bytes admissible against the prophecy world's `M`).
* `ownAdequacyF` — OwnWp.lean's `ownAdequacy` with the SAME client premises and NO fetch premise: `φ` holds of the
  final value map of EVERY valid run of machine v2 (`D = Unit`), through `Nfr.F.nfRF` and `nf_simF`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrFetch
import Weak.Prom.OwnWp

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Nfr.F
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P V : Type}

/-- ONE NF EVENT GROUP (prophecy-fed fetches included) IS ONE OR TWO LANGUAGE STEPS. -/
theorem nf_simF {w : OW P V} {N : Nat} :
    ∀ {c c' : PCfg P Unit} {es : List PEvt}, nfStepsF relClass w.pstep w.M c es c' → c'.pcLog <+: w.M →
      ∀ (tp : List (OExpr P V)) (σ : OSt V), Sim w N c tp σ →
      ∃ k tp' σ', NSteps k (tp, σ) [] (tp', σ') ∧ Sim w N c' tp' σ' := by
  intro c c' es h
  induction h with
  | refl c => intro _ tp σ hs; exact ⟨0, tp, σ, .refl _, hs⟩
  | prom c c1 i m es c2 hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hag, hprN, hh, hdone⟩ := hs
    cases hst with
    | promise _ ag _ hagi hnt htid =>
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (nfStepsF_prefix hrest) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hagi).1
    have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    let σ' : OSt V := { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }
    have hstep : Step (tp, σ) [] (tp, σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (e := OExpr.agent w) (e' := OExpr.agent w) (i := N) (obs := []) (efs := []) σ σ' hag
        (ostep.ag w σ σ' ⟨i, hnM, by simp [authorAt, hMn, htid], rfl⟩)
      rw [set_of_get hag, List.append_nil] at this
      exact this
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre tp σ' (by
      refine ⟨himg, ?_, hnM, by simp [hlen], htp, hag, fun h hN => ?_, fun h hN => ?_, hdone⟩
      · show c.pcLog ++ [m] = w.M.take (σ.n + 1)
        rw [hlog, take_succ_of hMn]
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · obtain ⟨ag', τ, a1, a2, a3⟩ := hh h hN
        by_cases e : h = i
        · subst e
          rw [hagi] at a1; cases a1
          refine ⟨_, τ, getElem?_set_eq_of hagi, a2, ?_⟩
          simp only [σ', upd_eq, a3, hclen]
        · refine ⟨ag', τ, ?_, a2, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact a1
          · simp only [σ', upd_ne _ _ e]; exact a3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩
  | st c c1 i ag l ots es c2 hag hnr hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, hdone⟩ := hs
    cases hst with
    | state _ ag0 _ _ st' d' ws' prom' hag0 hp hm =>
    rw [hag] at hag0; cases hag0
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    let σ' : OSt V := { σ with pr := upd σ.pr i prom' }
    have hm' : memStep w.img (w.M.take σ.n) i (σ.pr i) ag.paWs l ots ws' prom' := by
      rw [← hlog, a3, ← himg]; exact hm
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws' (τ ++ [(l, ots)])), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (ostep.hst w i ag.paSt ag.paWs τ σ l ots st' ws' σ' (.plain σ _ _ l ots st' ws' prom' hp hm' hnr))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws' (τ ++ [(l, ots)]))) σ' (by
      refine ⟨himg, hlog, hle, by rw [List.length_set]; exact hlen, by rw [List.length_set]; exact htp, ?_,
        fun h hN => ?_, fun h hN => ?_, hdone⟩
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨_, τ ++ [(l, ots)], getElem?_set_eq_of hag, getElem?_set_eq_of a2, ?_⟩
          simp only [σ', upd_eq]
        · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', τ', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', upd_ne _ _ e]; exact b3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩
  | rel c c1 c2 i m ag l r es c3 hpst hag1 hrc hr hst hrest ih =>
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, hdone⟩ := hs
    cases hpst with
    | promise _ ag0 _ hag0 hnt htid =>
    cases hst with
    | state _ ag1 _ _ st' d' ws' prom' hag1' hp hm =>
    rw [hag1] at hag1'; cases hag1'
    simp only at hag1
    rw [getElem?_set_eq_of hag0] at hag1; cases hag1
    have hpre1 : c.pcLog ++ [m] <+: w.M := List.IsPrefix.trans (List.prefix_refl _)
      (List.IsPrefix.trans (nfStepsF_prefix hrest) hpre)
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag0).1
    have hclen : c.pcLog.length = σ.n := by rw [hlog]; exact take_length' hle
    have hMn : w.M[σ.n]? = some m := by
      obtain ⟨t, ht⟩ := hpre1
      rw [← ht, List.getElem?_append_left (by simp [hclen])]
      simp [hclen]
    have hnM : σ.n < w.M.length := (List.getElem?_eq_some_iff.1 hMn).1
    obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
    rw [hag0] at a1; cases a1
    have hr' : r = σ.n + 1 := by rw [hr]; simp [hclen]
    subst hr'
    let σ' : OSt V := { σ with n := σ.n + 1, pr := upd σ.pr i prom' }
    have hm' : memStep w.img (w.M.take (σ.n + 1)) i ({σ.n + 1} ∪ σ.pr i) ag0.paWs l (some (σ.n + 1)) ws' prom' := by
      have hm2 := hm
      simp only at hm2
      rw [hclen] at hm2
      rw [a3, take_succ_of hMn, ← hlog, ← himg]; exact hm2
    have hstep : Step (tp, σ) [] (tp.set i (.hart w i st' ws' (τ ++ [(l, some (σ.n + 1))])), σ') := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ σ' a2
        (ostep.hst w i ag0.paSt ag0.paWs τ σ l (some (σ.n + 1)) st' ws' σ'
          (.rel σ _ _ l st' ws' prom' hnM (by simp [authorAt, hMn, htid]) hrc hp hm'))
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre (tp.set i (.hart w i st' ws' (τ ++ [(l, some (σ.n + 1))]))) σ' (by
      refine ⟨himg, ?_, hnM, by rw [List.length_set, List.length_set]; exact hlen,
        by rw [List.length_set]; exact htp, ?_, fun h hN => ?_, fun h hN => ?_, hdone⟩
      · show c.pcLog ++ [m] = w.M.take (σ.n + 1)
        rw [hlog, take_succ_of hMn]
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · have e : h ≠ i := by omega
        simp only [σ', upd_ne _ _ e]; exact hprN h hN
      · by_cases e : h = i
        · subst e
          refine ⟨⟨st', ws', prom'⟩, τ ++ [(l, some (σ.n + 1))], ?_, getElem?_set_eq_of a2, ?_⟩
          · simp only; rw [List.set_set]; exact getElem?_set_eq_of hag0
          · simp only [σ', upd_eq]
        · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', τ', ?_, ?_, ?_⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e), List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2
          · simp only [σ', upd_ne _ _ e]; exact b3)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩
  | fet c i ag b tvs st' d' es c2 hag hp hok hrest ih =>
    -- [E-b] THE PROPHECY-FED FETCH: one `hstepO.fetch` step, no language-state change
    intro hpre tp σ hs
    obtain ⟨himg, hlog, hle, hlen, htp, hagN, hprN, hh, hdone⟩ := hs
    have hiN : i < N := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    obtain ⟨ag', τ, a1, a2, a3⟩ := hh i hiN
    rw [hag] at a1; cases a1
    have hws : fetchPost c.pcLog i ag.paProm ag.paWs b tvs =
        { ag.paWs with
          wIfr := max ag.paWs.wIfr (bytesMax (fun _ t => t) b tvs)
          wIfv := max ag.paWs.wIfv (fetchView (w.M.take σ.n) i (σ.pr i) b tvs) } := by
      unfold fetchPost; rw [hlog, a3]
    have hf : hstepO w i σ ag.paSt ag.paWs (LIFetch b tvs) none st'
        (fetchPost c.pcLog i ag.paProm ag.paWs b tvs) σ := by
      rw [hws]; exact .fetch σ _ _ b tvs st' hp (himg ▸ hok)
    have hstep : Step (tp, σ) []
        (tp.set i (.hart w i st' (fetchPost c.pcLog i ag.paProm ag.paWs b tvs) (τ ++ [(LIFetch b tvs, none)])), σ) := by
      have := step_update_of_getElem? (Λ := (inferInstance : Language (OExpr P V) (OSt V) Unit V))
        (obs := []) (efs := []) σ σ a2
        (ostep.hst w i ag.paSt ag.paWs τ σ (LIFetch b tvs) none st' _ σ hf)
      rw [List.append_nil] at this
      exact this
    have hiN' : i ≠ N := by omega
    obtain ⟨k, tp', σ'', h1, h2⟩ := ih hpre
      (tp.set i (.hart w i st' (fetchPost c.pcLog i ag.paProm ag.paWs b tvs) (τ ++ [(LIFetch b tvs, none)]))) σ (by
      refine ⟨himg, hlog, hle, by rw [List.length_set]; exact hlen, by rw [List.length_set]; exact htp, ?_,
        hprN, fun h hN => ?_, hdone⟩
      · rw [List.getElem?_set_ne hiN']; exact hagN
      · by_cases e : h = i
        · subst e
          exact ⟨_, τ ++ [(LIFetch b tvs, none)], getElem?_set_eq_of hag, getElem?_set_eq_of a2, a3⟩
        · obtain ⟨ag', τ', b1, b2, b3⟩ := hh h hN
          refine ⟨ag', τ', ?_, ?_, b3⟩
          · simp only; rw [List.getElem?_set_ne (Ne.symm e)]; exact b1
          · rw [List.getElem?_set_ne (Ne.symm e)]; exact b2)
    exact ⟨1 + k, tp', σ'', nsteps_trans (nsteps_one hstep) h1, h2⟩

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- **THE ADEQUACY OF TRACK (b)'s LOGIC WITHOUT (P2)** (E-b): OwnWp.lean's `ownAdequacy` with the same client
premises and no fetch-boundedness premise — `φ` of the final value map of EVERY valid run (`D = Unit`). -/
theorem ownAdequacyF [InvGpreS GF] {w : OW P V} {ps : List P} (φ : (Nat → Option V) → Prop)
    (Hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} |={⊤}=> ∃ X : OSt V → IProp GF,
      X σ0 ∗ □ (∀ σ σ', ⌜agentStep w σ σ'⌝ -∗ X σ -∗ |={⊤}=> X σ') ∗
      ([∗list] e ∈ hartsFrom w 0 ps, wpO X e (fun _ => iprop(True))) ∗
      (∀ σ, ⌜σ.n = w.M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ X σ -∗ |={⊤,∅}=> ⌜φ σ.done⌝))
    {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun w.pstep w.img () ps evs cfg) (hM : cfg.pcLog = w.M) :
    φ (doneOf w ps.length cfg) := by
  obtain ⟨evs', ⟨hnf, hno⟩, _⟩ := nfRF hv
  rw [hM] at hnf
  let N := ps.length
  have hs0 : Sim w N (pmInit w.img () ps) (hartsFrom w 0 ps ++ [OExpr.agent w]) σ0 := by
    refine ⟨rfl, by simp [pmInit, σ0], Nat.zero_le _, by simp [pmInit, N], by simp [hartsFrom_length, N], ?_,
      fun _ _ => rfl, fun h hN => ?_, rfl⟩
    · rw [List.getElem?_append_right (by simp [hartsFrom_length, N])]
      simp [hartsFrom_length, N]
    · have hp : ps[h]? = some ps[h] := List.getElem?_eq_getElem hN
      refine ⟨⟨ps[h], psInit, ∅⟩, [], by simp [pmInit, hp], ?_, rfl⟩
      rw [List.getElem?_append_left (by simp [hartsFrom_length]; exact hN), hartsFrom_get w 0 ps h _ hp]
      simp
  obtain ⟨k, tp1, σ1, hk, hs1⟩ := nf_simF hnf (by rw [hM]; exact List.prefix_refl _) _ _ hs0
  have hno' : ∀ h, h < N → σ1.pr h = ∅ := by
    intro h hN
    obtain ⟨ag, _, a1, _, a3⟩ := hs1.2.2.2.2.2.2.2.1 h hN
    rw [a3]; exact hno h ag a1
  obtain ⟨j, tp2, hj, _, _⟩ := fin_steps hs1 hno' N (Nat.le_refl _)
  have hn1 : σ1.n = w.M.length := by
    have e := hs1.2.1
    rw [hM] at e
    have := congrArg List.length e
    rw [take_length' hs1.2.2.1] at this
    omega
  have hdone : (fun h => if h < N then doneOf w N cfg h else none) = doneOf w N cfg := by
    funext h; by_cases e : h < N <;> simp [e, doneOf]
  rw [hdone] at hj
  have hsteps := nsteps_trans hk hj
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck
    (hartsFrom w 0 ps ++ [OExpr.agent w]) σ0 (k + j) [] tp2 { σ1 with done := doneOf w N cfg }
    (φ (doneOf w N cfg)) (fun _ => 0) ?_ hsteps
  intro Hinv
  have hw := @Hwp Hinv
  dsimp only [wpO] at hw
  iintro
  imod hw with ⟨%X, HX, #Hag, Hharts, Hfin⟩
  imodintro
  iexists (fun σ _ _ _ => X σ), List.replicate (N + 1) (fun _ => iprop(True)),
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  iframe HX
  isplitl [Hharts]
  · have hl : (hartsFrom w 0 ps).length = N := hartsFrom_length w 0 ps
    rw [List.replicate_succ', ← hl]
    iapply (BigSepL2.bigSepL2_append (.inl (by simp))).2
    isplitl [Hharts]
    · iapply BigSepL2.bigSepL2_replicate_right.2
      iexact Hharts
    · iapply BigSepL2.bigSepL2_singleton.2
      ihave Ha := wpO_agent (hlc := hlc) (X := X) (w := w) $$ Hag
      dsimp only [wpO]
      iexact Ha
  iintro %es' %t2' %_ %_ %_ Hσ _ _
  iapply Hfin $$ %({ σ1 with done := doneOf w N cfg } : OSt V) %⟨hn1, fun h => ?_⟩ Hσ
  by_cases hN : h < N
  · exact hno' h hN
  · exact hs1.2.2.2.2.2.2.1 h (by omega)

end Weak.Prom.Own
