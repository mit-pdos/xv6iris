/-
The program-logic layer — ghost state, points-to, state interpretation, and the
one-step WP rule — the analog of Rocq's `RiscvPtsto.v` + `RiscvExec.wp_exec_step`.

The demo `step` (`PC := PC+4`) touches only registers, so this uses a single
register `gen_heap` (`DemoReg ↦ᵣ BitVec 64`, keyed by `regAddr : DemoReg → Nat`).
A second heap (byte memory) composes identically but must use a *distinct key
type*: `genHeapGS`'s `V` is an `outParam`, so two heaps over the same key type
are ambiguous to instance resolution — distinct key types disambiguate.

`stateInterp` bridges the authoritative `gen_heap` map to the (function-based)
machine state via an agreement invariant — Rocq's
`reg_interp := ∃ m, gen_heap_interp m ∗ ⌜reg_agree m rs⌝` pattern. Generic over
the GS bundle `[DemoGS hlc GF]`, exactly as iris-lean's lifting lemmas are.
-/
module

public import Xv6Iris.Lang
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Lifting
public import Iris.BI.Lib.GenHeap
public import Iris.ProofMode

@[expose] public section

namespace Xv6Iris.Demo

open Iris Iris.BI Iris.ProgramLogic Xv6Iris.Sail Std

/-- Registers live at `Nat` "register addresses" so the heap reuses the `Nat`-keyed
finite-map machinery (which has the required `LawfulFiniteMap` instance).
`regAddr` is injective, so distinct registers never alias. -/
def regAddr : DemoReg → Nat
  | .PC => 0
  | .nextPC => 1

theorem regAddr_injective : Function.Injective regAddr := by
  intro a b h; cases a <;> cases b <;> simp_all [regAddr]

/-- Finite-map functor for the register heap. -/
abbrev RegF : Type → Type := fun V => Std.ExtTreeMap Nat V compare

/-- The ghost-state bundle: invariants + the register `gen_heap`. -/
class DemoGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  reg : genHeapGS Nat (BitVec 64) GF RegF

attribute [reducible, instance] DemoGS.reg

section
variable {GF : BundledGFunctors} {hlc : HasLC} [DemoGS hlc GF]

/-! ## Points-to -/

/-- Register points-to (keyed by `regAddr r`). -/
def regPt (r : DemoReg) (dq : DFrac) (v : BitVec 64) : IProp GF := pointsTo (regAddr r) dq v

notation:50 r " ↦ᵣ{" dq "} " v:50 => regPt r dq v
notation:50 r " ↦ᵣ " v:50 => regPt r (DFrac.own 1) v

/-! ## State interpretation (agreement bridge) -/

/-- The owned `gen_heap` map agrees with the machine state's register function. -/
def regAgree (rm : RegF (BitVec 64)) (rf : DemoReg → Option (BitVec 64)) : Prop :=
  ∀ r, Std.PartialMap.get? (M := RegF) rm (regAddr r) = rf r

def stateInterpDef (σ : DState) : IProp GF :=
  iprop(∃ rm, genHeapInterp rm ∗ ⌜regAgree rm σ.regs⌝)

instance instStateInterp : StateInterp DState Empty GF where
  stateInterp σ _ _ _ := stateInterpDef σ

instance instIrisGS : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

/-! ## Bridge lemmas (the analog of Rocq `reg_valid` / `reg_update`) -/

/-- Owning `r ↦ᵣ v` against the state interpretation forces `σ.regs r = some v`. -/
theorem reg_valid {σ : DState} {r : DemoReg} {dq v} :
    (stateInterpDef σ : IProp GF) ∗ regPt r dq v ⊢ |==> ⌜σ.regs r = some v⌝ := by
  unfold stateInterpDef regPt
  iintro ⟨⟨%rm, Hi, %Hag⟩, Hr⟩
  imod genHeap_valid $$ [$Hi $Hr] with %Hlk
  ipureintro
  rw [← Hag r]; exact Hlk

/-- Updating `r ↦ᵣ v₁` to `r ↦ᵣ v₂` updates the state interpretation to
`σ.setReg r v₂` — the write bridge (analog of Rocq `reg_update`). -/
theorem reg_update {σ : DState} {r : DemoReg} {v₁ v₂ : BitVec 64} :
    (stateInterpDef σ : IProp GF) ∗ regPt r (.own 1) v₁ ⊢
      |==> (stateInterpDef (σ.setReg r v₂) ∗ regPt r (.own 1) v₂) := by
  unfold stateInterpDef regPt
  iintro ⟨⟨%rm, Hi, %Hag⟩, Hr⟩
  imod genHeap_update (v₂ := v₂) $$ [$Hi $Hr] with ⟨Hi, Hr⟩
  imodintro
  iframe Hr
  iexists _
  iframe Hi
  ipureintro
  intro r'
  rw [Std.LawfulPartialMap.get?_insert (M := RegF)]
  by_cases hrr : r = r'
  · subst hrr; simp [MState.setReg]
  · have h1 : regAddr r ≠ regAddr r' := fun h => hrr (regAddr_injective h)
    rw [if_neg h1]
    simp only [MState.setReg]
    rw [dif_neg (fun h => hrr h.symm)]
    exact Hag r'

/-! ## The one-step WP rule (analog of Rocq `wp_exec_step` + `wp_step_*`) -/

open Iris.ProgramLogic Language.Notation

/-- Owning `PC ↦ᵣ pc`, one `Loop` step advances `PC` to `pc+4` and hands the
updated ownership to the continuation. The first real WP about the demo machine,
built on `wp_lift_step` + the `exec_step` reduction + the `reg_*` bridge. -/
theorem wp_demo_step {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} {pc : BitVec 64} :
    DemoReg.PC ↦ᵣ pc -∗ ▷ (DemoReg.PC ↦ᵣ (pc + 4) -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})
      -∗ WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC Hcont
  iapply wp_lift_step (e₁ := RiscvExpr.Loop) rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  ihave %Hpc : ⌜σ₁.regs DemoReg.PC = some pc⌝ $$ [Hσ HPC]
  · ihave >%H := reg_valid $$ [$Hσ $HPC]
    itrivial
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    have Hstep : PrimStep.primStep (RiscvExpr.Loop, σ₁) ([] : List Empty)
        (RiscvExpr.Loop, σ₁.setReg DemoReg.PC (pc + 4), []) :=
      ⟨rfl, rfl, rfl, rfl, (), exec_step Hpc⟩
    cases s <;> first
      | exact ⟨_, _, _, _, Hstep⟩
      | trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨_, rfl, rfl, rfl, r, Hex⟩ := Hstep
  have Hσ₂ : σ₂ = σ₁.setReg DemoReg.PC (pc + 4) :=
    congrArg Prod.snd (Option.some.inj (Hex.symm.trans (exec_step (σ := σ₁) Hpc)))
  subst Hσ₂
  imod Hclose
  imod reg_update (v₂ := pc + 4) $$ [$Hσ $HPC] with ⟨Hσ', HPC'⟩
  imodintro
  iframe Hσ'
  isplitl [Hcont HPC']
  · iapply Hcont $$ HPC'
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

end

end Xv6Iris.Demo
