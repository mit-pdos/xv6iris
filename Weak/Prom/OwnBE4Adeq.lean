/-
Weak/Prom: **E-b4, B-0 — track (b)'s weakest precondition and A TRACE-PROPERTY ADEQUACY** (stage E-b4; owner ruling
[OWN.P16]; G4-review3.md §5 B-0, §7 item 3: OwnWp/OwnWpF export `φ σ.done` only, which says nothing about harts that
never finish).

RE-TYPINGS of OwnWp.lean / OwnWpF.lean onto OwnBE4Lang.lean's trace-carrying language (each tagged
`-- [retype <Old.name>]`):
* `wpB X e` — `wpO` over `TExpr`/`TSt` (one `▷` and `£ 1` per step, `MaybeStuck`), post `True`;
* `wpB_hart_lift` — `wpO_hart_lift` minus the value branch: a hart step is an `hstepO` step and records its entry
  in the hart's trace;
* `wpB_agent` — `wpO_agent`;
* `ownAdeqT` — `ownAdequacyF`'s premises with the final extraction `∀ h < N, Ψ h (σ.tr h)` in place of
  `φ σ.done`: `Ψ h (memEv (run.trace h))` for EVERY hart of EVERY valid run (`PF.validRun`, `D = Unit`), finished
  or not, through `nfRF` (NfrFetch.lean: same per-hart traces) and `nf_simT`.  The final state has `σ.o.pr h = ∅`
  for every `h`, so a client may refute any pending own read there.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Lang
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Nfr.F
open Weak.Prom.Own (OW OSt hstepO agentStep upd take_length')
open Weak.Prom.PF (memEv Trace PEv PFRun)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P V : Type} {hlc : HasLC} {GF : BundledGFunctors}

@[reducible] def tIrisGS [InvGS_gen hlc GF] (X : TSt V → IProp GF) : IrisGS_gen hlc (TExpr P V) GF where   -- [retype Own.oIrisGS]
  toStateInterp := ⟨fun σ _ _ _ => X σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

/-- **`wpB X e`**: the WP of a thread under the client's state interpretation `X`. -/
def wpB [InvGS_gen hlc GF] (X : TSt V → IProp GF) (e : TExpr P V) : IProp GF :=   -- [retype Own.wpO]
  letI : IrisGS_gen hlc (TExpr P V) GF := tIrisGS X
  WP e @ Stuckness.MaybeStuck; ⊤ {{ fun _ => iprop(True) }}

section lift

variable [InvGS_gen hlc GF]

theorem tStateI_eq (X : TSt V → IProp GF) (σ : TSt V) (ns : Nat) (obs : List Unit) (nt : Nat) :   -- [retype Own.oStateI_eq]
    @stateInterp (TSt V) Unit GF ((tIrisGS (P := P) X).toStateInterp) σ ns obs nt = X σ := rfl

/-- **THE HART LIFTING LEMMA**: a hart step is one NF_R step, recorded in the hart's trace. -/
theorem wpB_hart_lift {X : TSt V → IProp GF} {w : OW P V} {h : Nat} {s : P} {ws : PState} :   -- [retype Own.wpO_hart_lift]
    ▷ (∀ σ l ots s' ws' o', ⌜hstepO w h σ.o s ws l ots s' ws' o'⌝ -∗ X σ -∗ £ 1 -∗
          |={⊤}=> X ⟨o', upd σ.tr h (recE (σ.tr h) (l, ots))⟩ ∗ wpB X (.hart w h s' ws'))
    ⊢ wpB X (.hart w h s ws) := by
  letI : IrisGS_gen hlc (TExpr P V) GF := tIrisGS X
  show _ ⊢ WP (TExpr.hart w h s ws) @ Stuckness.MaybeStuck; ⊤ {{ fun _ => iprop(True) }}
  iintro Hk
  iapply wp_lift_step (rfl : toVal (TExpr.hart w h s ws : TExpr P V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [tStateI_eq]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  change tstep _ _ _ at Hstep
  cases Hstep with
  | hst _ _ _ _ _ l ots s' ws' o' hs =>
    imod Hclose
    imod Hk $$ %σ₁ %_ %_ %_ %_ %_ %hs Hσ Hcred with ⟨Hσ, Hk⟩
    imodintro
    rw [tStateI_eq]
    iframe Hσ
    isplitl [Hk]
    · dsimp only [wpB]
      iexact Hk
    · exact BigSepL.bigSepL_nil_intro

/-- **THE PROMISE AGENT'S WP IS THE INVARIANT**. -/
theorem wpB_agent {X : TSt V → IProp GF} {w : OW P V} :   -- [retype Own.wpO_agent]
    □ (∀ σ o', ⌜agentStep w σ.o o'⌝ -∗ X σ -∗ |={⊤}=> X ⟨o', σ.tr⟩) ⊢ wpB X (.agent w : TExpr P V) := by
  letI : IrisGS_gen hlc (TExpr P V) GF := tIrisGS X
  show _ ⊢ WP (TExpr.agent w : TExpr P V) @ Stuckness.MaybeStuck; ⊤ {{ fun _ => iprop(True) }}
  iintro #Hag
  iloeb as IH
  iapply wp_lift_step (rfl : toVal (TExpr.agent w : TExpr P V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [tStateI_eq]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  change tstep _ _ _ at Hstep
  cases Hstep with
  | ag _ _ o' ha =>
    imod Hclose
    imod Hag $$ %σ₁ %_ %ha Hσ with Hσ
    imodintro
    rw [tStateI_eq]
    iframe Hσ
    isplitl
    · iexact IH
    · exact BigSepL.bigSepL_nil_intro

/-- A fancy update before a hart's step. -/
theorem wpB_fupd {X : TSt V → IProp GF} {e : TExpr P V} : (|={⊤}=> wpB X e) ⊢ wpB X e := by
  letI : IrisGS_gen hlc (TExpr P V) GF := tIrisGS X
  exact fupd_wp

end lift

/-! ## Adequacy -/

/-- **THE TRACE-PROPERTY ADEQUACY OF TRACK (b)'s LOGIC**: a client state interpretation `X` over the trace-carrying
state, the agent obligation, the hart wps and a final extraction of `Ψ` from the traces give `Ψ h` of the
memory-event trace of EVERY hart of every valid run — finished or not. -/
theorem ownAdeqT [InvGpreS GF] {w : OW P V} {ps : List P} (Ψ : Nat → Trace → Prop) (hΨ : ∀ h, Ψ h [])   -- [retype Own.ownAdequacyF]
    (Hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} |={⊤}=> ∃ X : TSt V → IProp GF,
      X σT0 ∗ □ (∀ σ o', ⌜agentStep w σ.o o'⌝ -∗ X σ -∗ |={⊤}=> X ⟨o', σ.tr⟩) ∗
      ([∗list] e ∈ hartsFromT w 0 ps, wpB X e) ∗
      (∀ σ, ⌜σ.o.n = w.M.length ∧ ∀ h, σ.o.pr h = ∅⌝ -∗ X σ -∗ |={⊤,∅}=> ⌜∀ h, h < ps.length → Ψ h (σ.tr h)⌝))
    {run : PFRun P Unit} (hv : PF.validRun w.pstep w.img () ps w.M run) :
    ∀ h, Ψ h (memEv (run.trace h)) := by
  obtain ⟨hvr, hM⟩ := hv
  obtain ⟨evs', ⟨hnf, hno⟩, htr⟩ := nfRF hvr
  rw [hM] at hnf
  let N := ps.length
  intro h
  by_cases hN' : N ≤ h
  · have : run.trace h = [] := PF.validRun_traceNone hvr (List.getElem?_eq_none (by omega))
    rw [this]; exact hΨ h
  have hN : h < N := by omega
  have hs0 : SimT w N (pmInit w.img () ps) (hartsFromT w 0 ps ++ [TExpr.agent w]) σT0 [] := by
    refine ⟨rfl, by simp [pmInit, σT0], Nat.zero_le _, by simp [pmInit, N], by simp [hartsFromT_length, N], ?_,
      fun _ _ => rfl, fun h hN => ?_, fun h => by simp [σT0, traceOf, memEv]⟩
    · rw [List.getElem?_append_right (by simp [hartsFromT_length, N])]
      simp [hartsFromT_length, N]
    · have hp : ps[h]? = some ps[h] := List.getElem?_eq_getElem hN
      refine ⟨⟨ps[h], psInit, ∅⟩, by simp [pmInit, hp], ?_, rfl⟩
      rw [List.getElem?_append_left (by simp [hartsFromT_length]; exact hN), hartsFromT_get w 0 ps h _ hp]
      simp
  obtain ⟨k, tp1, σ1, hk, hs1⟩ := nf_simT hnf (by rw [hM]; exact List.prefix_refl _) _ _ _ hs0
  have hno' : ∀ h, h < N → σ1.o.pr h = ∅ := by
    intro h hN
    obtain ⟨ag, a1, _, a3⟩ := hs1.2.2.2.2.2.2.2.1 h hN
    rw [a3]; exact hno h ag a1
  have hn1 : σ1.o.n = w.M.length := by
    have e := hs1.2.1
    rw [hM] at e
    have := congrArg List.length e
    rw [take_length' hs1.2.2.1] at this
    omega
  have htr1 : σ1.tr h = memEv (run.trace h) := by
    rw [hs1.2.2.2.2.2.2.2.2 h, List.nil_append, htr h]; rfl
  rw [← htr1]
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck
    (hartsFromT w 0 ps ++ [TExpr.agent w]) σT0 k [] tp1 σ1 (Ψ h (σ1.tr h)) (fun _ => 0) ?_ hk
  intro Hinv
  have hw := @Hwp Hinv
  dsimp only [wpB] at hw
  iintro
  imod hw with ⟨%X, HX, #Hag, Hharts, Hfin⟩
  imodintro
  iexists (fun σ _ _ _ => X σ), List.replicate (N + 1) (fun _ => iprop(True)),
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  iframe HX
  isplitl [Hharts]
  · have hl : (hartsFromT w 0 ps).length = N := hartsFromT_length w 0 ps
    rw [List.replicate_succ', ← hl]
    iapply (BigSepL2.bigSepL2_append (.inl (by simp))).2
    isplitl [Hharts]
    · iapply BigSepL2.bigSepL2_replicate_right.2
      iexact Hharts
    · iapply BigSepL2.bigSepL2_singleton.2
      ihave Ha := wpB_agent (hlc := hlc) (X := X) (w := w) $$ Hag
      dsimp only [wpB]
      iexact Ha
  have hpr : ∀ h, σ1.o.pr h = ∅ := fun h => by
    by_cases hN : h < N
    · exact hno' h hN
    · exact hs1.2.2.2.2.2.2.1 h (by omega)
  iintro %es' %t2' %_ %_ %_ Hσ _ _
  imod Hfin $$ %σ1 %⟨hn1, hpr⟩ Hσ with %hf
  ipureintro; exact hf h hN

end Weak.Prom.OB.E4
