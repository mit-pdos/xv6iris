import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.ProofMode
import Xv6Iris.Model
import Xv6Iris.RealRegs
import Xv6Iris.RealPtsto

open Iris Iris.BI Iris.ProgramLogic Std
open LeanRV64D.Defs

set_option maxRecDepth 4000000

/-
Whole-machine-state WP engine: a `Nat`-keyed gen_heap holding the entire `MState`
(`machineState σ`), a one-step rule `wp_machine_step`, and `wp_run` — which runs N
real `try_step`s inside the WP driven by a single operational reduction
`runSteps N σ = some σ'` (per-step `exec` facts come from decomposing `runSteps`, so NO
per-instruction reduction lemmas). Memory writes and the privilege transition are
captured automatically since the whole state is one heap cell.
-/
namespace Xv6Iris.Model.KernelMain

/-- N-step runSteps of `riscv_step` (front-composing, so `runSteps (n+1) = exec >>= runSteps n`). -/
noncomputable def runSteps : Nat → MState → Option MState
  | 0, s => some s
  | n+1, s => (exec riscv_step s).bind (fun p => runSteps n p.2)

/-- `runSteps` composes: `a+b` steps = `a` steps then `b` steps. -/
theorem runSteps_add : ∀ (a b : Nat) (σ : MState),
    runSteps (a + b) σ = (runSteps a σ).bind (fun s => runSteps b s)
  | 0, b, σ => by simp [runSteps]
  | a+1, b, σ => by
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e]
      simp only [runSteps, Option.bind_assoc]
      congr 1; funext p; exact runSteps_add a b p.2

/-! ## Whole-machine-state ghost: a `Unit`-keyed heap holding the entire `MState`. -/

abbrev StF : Type → Type := fun V => Std.ExtTreeMap Nat V compare

class MainGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  st : genHeapGS Nat MState GF StF

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : MainGS hlc GF]

/-- The token: "the machine is exactly in state `σ`." -/
def machineState (σ : MState) : IProp GF := pointsTo (G := D.st) (0 : Nat) (.own 1) σ

def stateInterpMain (σ : MState) : IProp GF :=
  iprop(∃ m, genHeapInterp (G := D.st) m ∗ ⌜Std.PartialMap.get? m (0 : Nat) = some σ⌝)

instance (priority := 10000) instStateInterpMain : StateInterp MState Empty GF where
  stateInterp σ _ _ _ := stateInterpMain σ

instance (priority := 10000) instIrisGSMain : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

theorem machine_valid {σ σ₁ : MState} :
    (stateInterpMain σ₁ : IProp GF) ∗ machineState σ ⊢ |==> ⌜σ = σ₁⌝ := by
  unfold stateInterpMain machineState
  iintro ⟨⟨%m, Hi, %Hm⟩, Hp⟩
  imod genHeap_valid_at D.st $$ [$Hi $Hp] with %Hlk
  ipureintro
  rw [Hm] at Hlk; exact (Option.some.inj Hlk).symm

theorem machine_update {σ σ' : MState} :
    (stateInterpMain σ : IProp GF) ∗ machineState σ ⊢ |==> (stateInterpMain σ' ∗ machineState σ') := by
  unfold stateInterpMain machineState
  iintro ⟨⟨%m, Hi, %Hm⟩, Hp⟩
  imod genHeap_update_at D.st (v₂ := σ') $$ [$Hi $Hp] with ⟨Hi, Hp⟩
  imodintro
  iframe Hp
  iexists (Std.PartialMap.insert m (0 : Nat) σ')
  iframe Hi
  ipureintro
  rw [Std.LawfulPartialMap.get?_insert]; simp

/-! ## One step + N-step runSteps as WP rules -/

theorem wp_machine_step {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {σ σ' : MState} (Hexec : exec riscv_step σ = some ((), σ')) :
    machineState σ -∗ ▷ (machineState σ' -∗ WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro Hm Hk
  iapply wp_lift_step (e₁ := RiscvExpr.Loop) rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  ihave %Heq : ⌜σ = σ₁⌝ $$ [Hσ Hm]
  · ihave >%H := machine_valid $$ [$Hσ $Hm]; ipureintro; exact H
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    have Hstep : PrimStep.primStep (RiscvExpr.Loop, σ) ([] : List Empty)
        (RiscvExpr.Loop, σ', []) := ⟨rfl, rfl, rfl, rfl, (), Hexec⟩
    cases s <;> first | exact ⟨_, _, _, _, Hstep⟩ | trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨_, rfl, rfl, rfl, _, Hex'⟩ := Hstep
  have Hσ₂ : σ₂ = σ' := congrArg Prod.snd (Option.some.inj (Hex'.symm.trans Hexec))
  subst σ₂
  imod Hclose
  imod machine_update (σ' := σ') $$ [$Hσ $Hm] with ⟨Hσ, Hm⟩
  imodintro
  iframe Hσ
  isplitl [Hk Hm]
  · iapply Hk $$ Hm
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

/-- **Run `N` real steps inside the WP**, driven by a single operational reduction
`runSteps N σ = some σ'`. The per-step `exec` facts are obtained by decomposing `runSteps`;
no per-instruction lemmas. -/
theorem wp_run {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    ∀ (N : Nat) (σ σ' : MState), runSteps N σ = some σ' →
      (machineState σ : IProp GF) ⊢
        (▷^[N] (machineState σ' -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
          WP RiscvExpr.Loop @ s; E {{ Φ }}
  | 0, σ, σ', h => by
      simp only [runSteps, Option.some.injEq] at h; subst h
      show (machineState σ : IProp GF) ⊢
        (machineState σ -∗ WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗ WP RiscvExpr.Loop @ s; E {{ Φ }}
      iintro Hm Hk
      iapply Hk $$ Hm
  | N+1, σ, σ', h => by
      simp only [runSteps] at h
      obtain ⟨⟨u, σ1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases u
      iintro Hm Hk
      iapply (wp_machine_step h1) $$ Hm
      inext
      iintro Hm1
      iapply (wp_run N σ1 σ' h2) $$ Hm1
      iexact Hk

end
end Xv6Iris.Model.KernelMain
