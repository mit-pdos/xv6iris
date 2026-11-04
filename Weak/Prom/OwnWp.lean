/-
Weak/Prom: **track (b)'s weakest precondition, lifting lemmas and adequacy** (stage S4b; plan rev 7 §4 "Pull rule",
§7 "Leaf interface": `wpHartP_lift` has the statement shape of `wpHart_lift`, one `▷` and `£ 1` per step).

* `wpO X e Φ` — iris-lean's `WP` of a thread of OwnLang.lean, under the state interpretation `X : OSt V → iProp`
  chosen by the client (the OWNERSHIP STATE INTERPRETATION of a track-(b) proof: points-to, release deposits, pulls);
  one `▷` and `£ 1` per step; `MaybeStuck`.
* `wpO_hart_lift` — THE HART LIFTING LEMMA: from `X σ`, a hart may take any NF_R step (`hstepO`) and must give back
  `X σ'`; at its value (no promise left) it records the value in `σ.done` and gives back `X` of the new state.
* `wpO_agent` — THE PROMISE AGENT'S WP IS THE INVARIANT (plan §4): if every agent step (`agentStep`: `M[n]` appended
  as a promise of its author) preserves `X`, the agent thread is safe.
* `ownAdequacy` — THE ADEQUACY: if the client allocates `X` with `X σ0`, proves the agent obligation, every hart's
  wp, and a final extraction `X σ ⊢ ⌜φ σ.done⌝` at the end of the run, then `φ` holds of the final value map of EVERY
  valid, fetch-bounded run (MachFix-R-b5: no `invalFree`) of machine v2 (`D = Unit`), via the NF_R lemma (NfrRun.lean) and the
  simulation (OwnLang.lean).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLang
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P V : Type} {hlc : HasLC} {GF : BundledGFunctors}

/-- The iris-lean `IrisGS` of the pool under the client's state interpretation `X`. -/
@[reducible] def oIrisGS [InvGS_gen hlc GF] (X : OSt V → IProp GF) : IrisGS_gen hlc (OExpr P V) GF where
  toStateInterp := ⟨fun σ _ _ _ => X σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

/-- **`wpO X e Φ`**: the WP of a thread. -/
def wpO [InvGS_gen hlc GF] (X : OSt V → IProp GF) (e : OExpr P V) (Φ : V → IProp GF) : IProp GF :=
  letI : IrisGS_gen hlc (OExpr P V) GF := oIrisGS X
  WP e @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

section lift

variable [InvGS_gen hlc GF]

theorem oStateI_eq (X : OSt V → IProp GF) (σ : OSt V) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp (OSt V) Unit GF ((oIrisGS (P := P) X).toStateInterp) σ ns obs nt = X σ := rfl

/-- **THE HART LIFTING LEMMA** (plan §7 `wpHartP_lift`). -/
theorem wpO_hart_lift {X : OSt V → IProp GF} {w : OW P V} {h : Nat} {s : P} {ws : PState}
    {τ : List (PLabel × Option Nat)} {Φ : V → IProp GF} :
    ▷ ((∀ v σ, ⌜w.pdone s = some v⌝ -∗ ⌜σ.pr h = ∅⌝ -∗ X σ -∗
          |={⊤}=> X { σ with done := upd σ.done h (some v) } ∗ Φ v) ∧
       (∀ σ l ots s' ws' σ', ⌜hstepO w h σ s ws l ots s' ws' σ'⌝ -∗ X σ -∗ £ 1 -∗
          |={⊤}=> X σ' ∗ wpO X (.hart w h s' ws' (τ ++ [(l, ots)])) Φ))
    ⊢ wpO X (.hart w h s ws τ) Φ := by
  letI : IrisGS_gen hlc (OExpr P V) GF := oIrisGS X
  show _ ⊢ WP (OExpr.hart w h s ws τ) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}
  iintro Hk
  iapply wp_lift_step (rfl : toVal (OExpr.hart w h s ws τ : OExpr P V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [oStateI_eq]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  change ostep _ _ _ at Hstep
  cases Hstep with
  | hst _ _ _ _ _ _ l ots s' ws' σ' hs =>
    icases Hk with ⟨-, Hk⟩
    imod Hclose
    imod Hk $$ %σ₁ %_ %_ %_ %_ %_ %hs Hσ Hcred with ⟨Hσ, Hk⟩
    imodintro
    rw [oStateI_eq]
    iframe Hσ
    isplitl [Hk]
    · dsimp only [wpO]
      iexact Hk
    · exact BigSepL.bigSepL_nil_intro
  | fin _ _ _ _ _ _ v hv hpr =>
    icases Hk with ⟨Hk, -⟩
    imod Hclose
    imod Hk $$ %v %σ₁ %hv %hpr Hσ with ⟨Hσ, Hv⟩
    imodintro
    rw [oStateI_eq]
    iframe Hσ
    isplitl [Hv]
    · iapply (wp_value_fupd' (v := v)).2
      imodintro
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

/-- **THE PROMISE AGENT'S WP IS THE INVARIANT** (plan §4): the agent thread is safe if every promise preserves `X`. -/
theorem wpO_agent {X : OSt V → IProp GF} {w : OW P V} :
    □ (∀ σ σ', ⌜agentStep w σ σ'⌝ -∗ X σ -∗ |={⊤}=> X σ') ⊢ wpO X (.agent w : OExpr P V) (fun _ => iprop(True)) := by
  letI : IrisGS_gen hlc (OExpr P V) GF := oIrisGS X
  show _ ⊢ WP (OExpr.agent w : OExpr P V) @ Stuckness.MaybeStuck; ⊤ {{ fun _ => iprop(True) }}
  iintro #Hag
  iloeb as IH
  iapply wp_lift_step (rfl : toVal (OExpr.agent w : OExpr P V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [oStateI_eq]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  change ostep _ _ _ at Hstep
  cases Hstep with
  | ag _ _ σ' ha =>
    imod Hclose
    imod Hag $$ %σ₁ %_ %ha Hσ with Hσ
    imodintro
    rw [oStateI_eq]
    iframe Hσ
    isplitl
    · iexact IH
    · exact BigSepL.bigSepL_nil_intro

end lift

/-! ## Adequacy -/

theorem bigSepL_hartsFrom_len (w : OW P V) (ps : List P) :
    (hartsFrom w 0 ps ++ [OExpr.agent w]).length = ps.length + 1 := by
  simp [hartsFrom_length]

/-- **THE ADEQUACY OF TRACK (b)'s LOGIC**: a client state interpretation `X`, the agent obligation, the hart wps and a
final extraction give `φ` of the final value map of every valid, fetch-bounded run (MachFix-R-b5: the former
`invalFree` premise is gone). -/
theorem ownAdequacy [InvGpreS GF] {w : OW P V} {ps : List P} (φ : (Nat → Option V) → Prop)
    (Hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} |={⊤}=> ∃ X : OSt V → IProp GF,
      X σ0 ∗ □ (∀ σ σ', ⌜agentStep w σ σ'⌝ -∗ X σ -∗ |={⊤}=> X σ') ∗
      ([∗list] e ∈ hartsFrom w 0 ps, wpO X e (fun _ => iprop(True))) ∗
      (∀ σ, ⌜σ.n = w.M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ X σ -∗ |={⊤,∅}=> ⌜φ σ.done⌝))
    {evs : List PEvt} {cfg : PCfg P Unit} (hv : validRun w.pstep w.img () ps evs cfg) (hM : cfg.pcLog = w.M)
    (hfb : fetchBounded w.pstep w.img ps cfg.pcLog evs) :   -- MachFix-R-b5: no `invalFree` premise
    φ (doneOf w ps.length cfg) := by
  obtain ⟨evs', ⟨hnf, hno⟩, _⟩ := nfR hv hfb
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
  obtain ⟨k, tp1, σ1, hk, hs1⟩ := nf_sim hnf (by rw [hM]; exact List.prefix_refl _) _ _ hs0
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
