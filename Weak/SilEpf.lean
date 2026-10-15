/-
Weak: **(c) [OWN.100], increment 4a — the twin fabric-shared machine and its erasure to the twin
language** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

  §1  **`SilEpf.epfStepS`**: the registered `epfStep`, or a SILENT WRITE of a hart (`SilLang.silentWrite`
      at its current monad node); `epfRunS`;
  §2  the erasure: `SilEpf.eprimLift` (every registered primitive step is a twin one),
      `SilEpf.erasedLift` (a registered pool step is a twin pool step, the threads wrapped),
      `SilEpf.erasedStepOfLookupS`, **`SilEpf.epfStepSErased`** and **`SilEpf.epfRtcErasedS`** (a twin
      fabric-shared run IS a twin thread-pool run of `SilLang.EExprS`).

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilLang

namespace Weak

open Iris Iris.ProgramLogic Iris.Std
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! # 1. The twin fabric-shared machine -/

inductive SilEpf.epfStepS : Nat → Wlabel → (Epool × WGState) → (Epool × WGState) → Prop where
  | old (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) : epfStep i l ρ ρ' → SilEpf.epfStepS i l ρ ρ'
  /-- A hart's SILENT exclusive write. -/
  | silent (c : CPU) (l : Wlabel) (P : Epool) (σ : WGState) (m : SailM Unit) (h' : ehst)
      (σ' : WGState) :
      ethreadLive σ P.epGen → P.epH c = some (m, none) →
      SilLang.silentWrite P.epGen σ c m none (ehexp P.epGen c h') σ' →
      SilEpf.epfStepS c.val l (P, σ) (epHset P c h', σ')

def SilEpf.epfRunS (ρ ρ' : Epool × WGState) : Prop := ∃ i l, SilEpf.epfStepS i l ρ ρ'

/-! # 2. The erasure -/

/-- Every registered primitive step is a twin one. -/
theorem SilEpf.eprimLift (e : EExpr) (σ : WGState) (κ : List Empty) (e' : EExpr) (σ' : WGState)
    (efs : List EExpr) : eprimStep e σ κ e' σ' efs → SilLang.eprimStepS e σ κ e' σ' efs := by
  intro h
  cases e with
  | Sail gen cpu m fn =>
    obtain ⟨h1, h2, h3 | h3⟩ := h
    · exact ⟨h1, h2, .inl ⟨h3.1, .inl h3.2⟩⟩
    · exact ⟨h1, h2, .inr h3⟩
  | EDev => exact h
  | EDisk => exact h
  | EPower => exact h

def SilEpf.wrap (t : List EExpr) : List SilLang.EExprS := t.map SilLang.EExprS.mk

/-- A registered pool step is a twin pool step, the threads wrapped. -/
theorem SilEpf.erasedLift (t t' : List EExpr) (σ σ' : WGState) :
    Language.ErasedStep (Λ := weakEvLang) (t, σ) (t', σ') →
    Language.ErasedStep (Λ := SilLang.langS) (SilEpf.wrap t, σ) (SilEpf.wrap t', σ') := by
  rintro ⟨obs, hs⟩
  cases hs with
  | @atomic e _ _ e' _ eₜ H t₁ t₂ =>
    refine ⟨obs, ?_⟩
    have H' : SilLang.eprimStepS e σ obs e' σ' ((eₜ.map SilLang.EExprS.mk).map SilLang.EExprS.e) := by
      simp only [List.map_map]
      have : (SilLang.EExprS.e ∘ SilLang.EExprS.mk) = id := rfl
      rw [this, List.map_id]
      exact SilEpf.eprimLift e σ obs e' σ' eₜ H
    have := Language.Step.atomic (Λ := SilLang.langS) (e := ⟨e⟩) (σ := σ) (obs := obs) (e' := ⟨e'⟩)
      (σ' := σ') (eₜ := eₜ.map SilLang.EExprS.mk) H' (t₁.map SilLang.EExprS.mk) (t₂.map SilLang.EExprS.mk)
    simpa [SilEpf.wrap, List.map_append] using this

theorem SilEpf.erasedStepOfLookupS (t : List EExpr) (i : Nat) (e e' : EExpr) (σ σ' : WGState) :
    t[i]? = some e → SilLang.eprimStepS e σ [] e' σ' [] →
    Language.ErasedStep (Λ := SilLang.langS) (SilEpf.wrap t, σ) (SilEpf.wrap (t.set i e'), σ') := by
  intro hi hs
  refine ⟨[], ?_⟩
  have hi' : (SilEpf.wrap t)[i]? = some ⟨e⟩ := by
    unfold SilEpf.wrap; rw [List.getElem?_map, hi]; rfl
  have := Language.step_update_of_getElem? (Λ := SilLang.langS) (obs := []) (efs := [])
    (e := ⟨e⟩) (e' := ⟨e'⟩) σ σ' hi' (by exact hs)
  rw [List.append_nil] at this
  unfold SilEpf.wrap at this ⊢
  rw [List.map_set]
  exact this

theorem SilEpf.epfStepSErased (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    SilEpf.epfStepS i l ρ ρ' →
    Language.ErasedStep (Λ := SilLang.langS) (SilEpf.wrap (epoolList ρ.1), ρ.2)
      (SilEpf.wrap (epoolList ρ'.1), ρ'.2) := by
  intro h
  cases h with
  | old i l ρ ρ' h => exact SilEpf.erasedLift _ _ _ _ (epfStepErased i l ρ ρ' h)
  | silent c l P σ m h' σ' hl hh hs =>
    dsimp only
    rw [← epoolListHset P c h']
    refine SilEpf.erasedStepOfLookupS _ _ _ _ _ _ (epoolListHartLookup P c) ?_
    have he : ehexpr P c = ECycle P.epGen c m none := by simp [ehexpr, hh, ehexp]
    rw [he]
    exact ⟨rfl, rfl, Or.inl ⟨hl, Or.inr hs⟩⟩

/-- **A TWIN FABRIC-SHARED RUN IS A TWIN THREAD-POOL RUN.** -/
theorem SilEpf.epfRtcErasedS (ρ ρ' : Epool × WGState) :
    rtc SilEpf.epfRunS ρ ρ' →
    rtc (fun a b : List SilLang.EExprS × WGState => Language.ErasedStep (Λ := SilLang.langS) a b)
      (SilEpf.wrap (epoolList ρ.1), ρ.2) (SilEpf.wrap (epoolList ρ'.1), ρ'.2) := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact rtc_r ih (SilEpf.epfStepSErased i l _ _ hs)

theorem SilEpf.wrapPowerFork (gen : Nat) :
    SilEpf.wrap (epowerFork gen) = SilLang.epowerForkS gen := rfl

/-! # 3. The success criterion at the twin machine -/

open Iris.BI in
/-- The twin `epfViolationFreeHart`. -/
def SilEpf.violationFreeS (ρ0 : Epool × WGState) : Prop :=
  ∀ ρ, rtc SilEpf.epfRunS ρ0 ρ → ¬ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)

section adequacy

open Iris.BI Iris.ProofMode
open Language.Notation PrimStep

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- **`weakEvPfViolationFree`'s twin**: from the twin WP package, no twin fabric-shared run reaches a
violating configuration. -/
theorem SilEpf.pfViolationFreeS [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (g : WGState) (D : CPU → List Register)
    (hD : ∀ c, (D c).Nodup)
    (Hpow : g.wgpow = true) (Hgen0 : g.wggen = 0) (Hlog : g.wglog = [])
    (Hws : ∀ c : CPU, g.wgws c = wsInit)
    (Hwp : ∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] c ∈ cpus, [∗list] r ∈ D c, regPointsTo c r (DFrac.own 1) (g.wgregs c r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) g.wgimg ∗
        ([∗list] c ∈ cpus, hartView c) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (g.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=>
        ([∗list] e ∈ SilLang.epowerForkS gen, SilLang.ewpTrivS (hlc := hlc) (GF := GF) ⊤ e)) :
    SilEpf.violationFreeS (epInit gen, g) := by
  intro ρ2 hrun
  have herased := SilEpf.epfRtcErasedS (epInit gen, g) ρ2 hrun
  rw [show (epInit gen, g).1 = epInit gen from rfl, epoolListInit, SilEpf.wrapPowerFork] at herased
  have hnv := SilLang.adequacyPhiS (hlc := hlc) (GF := GF) gen g D hD Hpow Hgen0 Hlog Hws Hwp
    (SilEpf.wrap (epoolList ρ2.1)) ρ2.2 herased
  exact noViolationViolationHart ρ2.1 ρ2.2 hnv

end adequacy

end Weak
