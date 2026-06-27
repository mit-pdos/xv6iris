/-
The program-logic layer — ghost state, points-to, state interpretation, the
bridge lemmas, and the one-step WP rule. Analog of Rocq's `RiscvPtsto.v` +
`RiscvExec.wp_exec_step`.

Two `gen_heap`s: registers and byte memory. iris-lean's `genHeapGS L V GF H` has
*all four* parameters as `outParam`s, so two ambient heap instances cannot be told
apart by key/value type — instance resolution just picks one. `genHeapInterp` /
`pointsTo` take a *named* `(G := …)` instance binder (so we pin the heap there),
but the `genHeap_valid` / `genHeap_update` lemmas use an *anonymous* binder. We
bridge that gap with thin wrapper lemmas (`genHeap_valid_at` / `genHeap_update_at`)
that take the heap as an explicit argument; their *statement* fixes the instance,
so the underlying lemma is pinned by unification rather than resolution.

Registers are keyed by a dedicated `RegLoc` (an `Int` wrapper, mirroring
iris-lean's `Loc`); memory keeps the natural `Nat` byte address. `stateInterp`
bridges both authoritative maps to the function-based machine state via agreement
invariants — Rocq's `reg_interp` / `mem` pattern.
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

/-! ## Wrapper lemmas: `genHeap_valid`/`_update` with the heap as an explicit arg -/

section Wrappers
variable {GF : BundledGFunctors} {L V : Type} {H : Type → Type} [Std.LawfulFiniteMap H L]

theorem genHeap_valid_at (G : genHeapGS L V GF H) {σ : H V} {l : L} {dq : DFrac} {v : V} :
    genHeapInterp (G := G) σ ∗ pointsTo (G := G) l dq v
      ==∗ ⌜Std.PartialMap.get? σ l = some v⌝ :=
  genHeap_valid

theorem genHeap_update_at [DecidableEq L] (G : genHeapGS L V GF H)
    {σ : H V} {l : L} {v₁ v₂ : V} :
    genHeapInterp (G := G) σ ∗ pointsTo (G := G) l (.own 1) v₁
      ==∗ (genHeapInterp (G := G) (Std.PartialMap.insert σ l v₂) ∗
           pointsTo (G := G) l (.own 1) v₂) :=
  genHeap_update
end Wrappers

/-! ## Register key type (`Int` wrapper, mirroring iris-lean `Loc`) -/

@[ext] structure RegLoc where
  mk ::
  n : Int
  deriving DecidableEq

instance instOrdRegLoc : Ord RegLoc where
  compare l₁ l₂ := compare l₁.n l₂.n

instance : Std.TransOrd RegLoc where
  eq_swap := by
    intros l₁ l₂; unfold compare; unfold instOrdRegLoc; simp
    apply Int.instTransOrd.eq_swap
  isLE_trans := by
    intros l₁ l₂ l₃; unfold compare; unfold instOrdRegLoc; simp
    apply Int.instTransOrd.isLE_trans

instance : Std.LawfulEqOrd RegLoc where
  eq_of_compare := by
    intros l₁ l₂; unfold compare; unfold instOrdRegLoc; simp
    intros h; ext; assumption

/-- The register's key. Injective, so distinct registers never alias. -/
def regKey : DemoReg → RegLoc
  | .PC => ⟨0⟩
  | .nextPC => ⟨1⟩

theorem regKey_injective : Function.Injective regKey := by
  intro a b h; cases a <;> cases b <;> simp_all [regKey]

/-! ## The two heaps -/

abbrev RegF : Type → Type := fun V => Std.ExtTreeMap RegLoc V compare
abbrev MemF : Type → Type := fun V => Std.ExtTreeMap Nat V compare

/-- The ghost-state bundle: invariants + the register and memory `gen_heap`s. -/
class DemoGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  reg : genHeapGS RegLoc (BitVec 64) GF RegF
  mem : genHeapGS Nat (BitVec 8) GF MemF

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : DemoGS hlc GF]

/-! ## Points-to (heap instance named explicitly) -/

def regPt (r : DemoReg) (dq : DFrac) (v : BitVec 64) : IProp GF :=
  pointsTo (G := D.reg) (regKey r) dq v
def memPt (a : Nat) (dq : DFrac) (b : BitVec 8) : IProp GF :=
  pointsTo (G := D.mem) a dq b

notation:50 r " ↦ᵣ{" dq "} " v:50 => regPt r dq v
notation:50 r " ↦ᵣ " v:50 => regPt r (DFrac.own 1) v
notation:50 a " ↦ₘ{" dq "} " b:50 => memPt a dq b
notation:50 a " ↦ₘ " b:50 => memPt a (DFrac.own 1) b

/-! ## State interpretation (agreement bridge) -/

def regAgree (rm : RegF (BitVec 64)) (rf : DemoReg → Option (BitVec 64)) : Prop :=
  ∀ r, Std.PartialMap.get? (M := RegF) rm (regKey r) = rf r

def memAgree (mm : MemF (BitVec 8)) (mf : Nat → Option (BitVec 8)) : Prop :=
  ∀ a, Std.PartialMap.get? (M := MemF) mm a = mf a

def stateInterpDef (σ : DState) : IProp GF :=
  iprop(∃ rm mm, genHeapInterp (G := D.reg) rm ∗ genHeapInterp (G := D.mem) mm ∗
    ⌜regAgree rm σ.regs⌝ ∗ ⌜memAgree mm σ.mem⌝)

instance instStateInterp : StateInterp DState Empty GF where
  stateInterp σ _ _ _ := stateInterpDef σ

instance instIrisGS : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

/-! ## Bridge lemmas -/

/-- Owning `r ↦ᵣ v` forces `σ.regs r = some v`. -/
theorem reg_valid {σ : DState} {r : DemoReg} {dq v} :
    (stateInterpDef σ : IProp GF) ∗ regPt r dq v ⊢ |==> ⌜σ.regs r = some v⌝ := by
  unfold stateInterpDef regPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Hr⟩
  imod genHeap_valid_at D.reg $$ [$Hi $Hr] with %Hlk
  ipureintro
  rw [← Hag r]; exact Hlk

/-- Updating `r ↦ᵣ v₁` to `r ↦ᵣ v₂` updates the state interpretation to
`σ.setReg r v₂` — the register write bridge. -/
theorem reg_update {σ : DState} {r : DemoReg} {v₁ v₂ : BitVec 64} :
    (stateInterpDef σ : IProp GF) ∗ regPt r (.own 1) v₁ ⊢
      |==> (stateInterpDef (σ.setReg r v₂) ∗ regPt r (.own 1) v₂) := by
  unfold stateInterpDef regPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Hr⟩
  imod genHeap_update_at D.reg (v₂ := v₂) $$ [$Hi $Hr] with ⟨Hi, Hr⟩
  imodintro
  iframe Hr
  iexists _
  iexists mm
  iframe Hi Hm
  ipureintro
  refine ⟨fun r' => ?_, Hmag⟩
  rw [Std.LawfulPartialMap.get?_insert (M := RegF)]
  by_cases hrr : r = r'
  · subst hrr; simp [MState.setReg]
  · have h1 : regKey r ≠ regKey r' := fun h => hrr (regKey_injective h)
    rw [if_neg h1]
    simp only [MState.setReg]
    rw [dif_neg (fun h => hrr h.symm)]
    exact Hag r'

/-- Owning `a ↦ₘ b` forces `σ.mem a = some b`. -/
theorem mem_valid {σ : DState} {a : Nat} {dq b} :
    (stateInterpDef σ : IProp GF) ∗ memPt a dq b ⊢ |==> ⌜σ.mem a = some b⌝ := by
  unfold stateInterpDef memPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Ha⟩
  imod genHeap_valid_at D.mem $$ [$Hm $Ha] with %Hlk
  ipureintro
  rw [← Hmag a]; exact Hlk

/-- Updating `a ↦ₘ b₁` to `a ↦ₘ b₂` updates the state interpretation to
`σ.setMem a b₂` — the memory write bridge. -/
theorem mem_update {σ : DState} {a : Nat} {b₁ b₂ : BitVec 8} :
    (stateInterpDef σ : IProp GF) ∗ memPt a (.own 1) b₁ ⊢
      |==> (stateInterpDef (σ.setMem a b₂) ∗ memPt a (.own 1) b₂) := by
  unfold stateInterpDef memPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Ha⟩
  imod genHeap_update_at D.mem (v₂ := b₂) $$ [$Hm $Ha] with ⟨Hm, Ha⟩
  imodintro
  iframe Ha
  iexists rm
  iexists _
  iframe Hi Hm
  ipureintro
  refine ⟨Hag, fun a' => ?_⟩
  rw [Std.LawfulPartialMap.get?_insert (M := MemF)]
  by_cases haa : a = a'
  · subst haa; simp [MState.setMem]
  · rw [if_neg haa]
    simp only [MState.setMem]
    rw [if_neg (fun h => haa h.symm)]
    exact Hmag a'

/-! ## The one-step WP rule (analog of Rocq `wp_exec_step` + `wp_step_*`) -/

open Iris.ProgramLogic Language.Notation

/-- Owning `PC ↦ᵣ pc` and the memory cell `0 ↦ₘ b`, one `Loop` step advances `PC`
to `pc+4` and sets `0 ↦ₘ 7`, handing the updated ownership of *both* heaps to the
continuation. Built on `wp_lift_step` + `exec_step` + the `reg_*`/`mem_*` bridges. -/
theorem wp_demo_step {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {pc : BitVec 64} {b : BitVec 8} :
    DemoReg.PC ↦ᵣ pc -∗ (0 : Nat) ↦ₘ b -∗
      ▷ (DemoReg.PC ↦ᵣ (pc + 4) -∗ (0 : Nat) ↦ₘ 7#8 -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})
      -∗ WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HM Hcont
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
        (RiscvExpr.Loop, (σ₁.setReg DemoReg.PC (pc + 4)).setMem 0 7#8, []) :=
      ⟨rfl, rfl, rfl, rfl, (), exec_step Hpc⟩
    cases s <;> first
      | exact ⟨_, _, _, _, Hstep⟩
      | trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨_, rfl, rfl, rfl, r, Hex⟩ := Hstep
  have Hσ₂ : σ₂ = (σ₁.setReg DemoReg.PC (pc + 4)).setMem 0 7#8 :=
    congrArg Prod.snd (Option.some.inj (Hex.symm.trans (exec_step (σ := σ₁) Hpc)))
  subst Hσ₂
  imod Hclose
  imod reg_update (v₂ := pc + 4) $$ [$Hσ $HPC] with ⟨Hσ, HPC'⟩
  imod mem_update (b₂ := 7#8) $$ [$Hσ $HM] with ⟨Hσ, HM'⟩
  imodintro
  iframe Hσ
  isplitl [Hcont HPC' HM']
  · iapply Hcont $$ HPC' HM'
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-- The WP composes: two `Loop` steps advance `PC` by 8 and leave `0 ↦ₘ 7` (the
`wp_kernel_first_two` shape — chaining per-step WPs, threading *both* heaps'
ownership through each `▷`). -/
theorem wp_two_steps {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {pc : BitVec 64} {b : BitVec 8} :
    DemoReg.PC ↦ᵣ pc -∗ (0 : Nat) ↦ₘ b -∗
      ▷ ▷ (DemoReg.PC ↦ᵣ (pc + 4 + 4) -∗ (0 : Nat) ↦ₘ 7#8 -∗
            WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HM Hcont
  iapply wp_demo_step $$ HPC HM
  inext
  iintro HPC4 HM4
  iapply wp_demo_step $$ HPC4 HM4
  inext
  iintro HPC8 HM8
  iapply Hcont $$ HPC8 HM8

end

end Xv6Iris.Demo
