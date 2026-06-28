/-
The program-logic layer over the *real* model: ghost state, points-to, and the
state-interpretation bridge — `RiscvPtsto.v`'s analog, now over the generated
`Register` and the byte memory.

Per the chosen design, the register `gen_heap` cell is a uniform `BitVec 64`
(narrow registers' high bits are irrelevant), bridged to the faithful dependent
`MState.regs` by `encReg` (from `RealRegs.lean`). Two heaps — registers (keyed by
the real `Register`, via the `Ord`/`LawfulFiniteMap` from `RealRegs`) and byte
memory (keyed by `Nat`) — disambiguated by the explicit-instance wrapper-lemma
trick (`genHeap_valid_at`) discovered in the demo `Ptsto.lean`.

Non-module (imports the non-module model).
-/
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.ProofMode
import Xv6Iris.Model
import Xv6Iris.RealRegs

open Iris Iris.BI Iris.ProgramLogic Std
open LeanRV64D.Defs (Register RegisterType)

namespace Xv6Iris.Model

/-! ## Wrapper lemmas: `genHeap_valid`/`_update` with the heap as an explicit arg
(same technique as the demo — `genHeapGS`'s params are all `outParam`s). -/

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

/-! ## The two heaps -/

abbrev RegF : Type → Type := fun V => Std.ExtTreeMap Register V compare
abbrev MemF : Type → Type := fun V => Std.ExtTreeMap Nat V compare

/-- Ghost state: invariants + the register and byte-memory `gen_heap`s. -/
class RiscvGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  reg : genHeapGS Register (BitVec 64) GF RegF
  mem : genHeapGS Nat (BitVec 8) GF MemF

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : RiscvGS hlc GF]

/-- Register points-to: the uniform `BitVec 64` view of register `r`. -/
def regPt (r : Register) (dq : DFrac) (v : BitVec 64) : IProp GF :=
  pointsTo (G := D.reg) r dq v
/-- Memory (byte) points-to. -/
def memPt (a : Nat) (dq : DFrac) (b : BitVec 8) : IProp GF :=
  pointsTo (G := D.mem) a dq b

notation:50 r " ↦ᵣ{" dq "} " v:50 => regPt r dq v
notation:50 r " ↦ᵣ " v:50 => regPt r (DFrac.own 1) v
notation:50 a " ↦ₘ{" dq "} " b:50 => memPt a dq b
notation:50 a " ↦ₘ " b:50 => memPt a (DFrac.own 1) b

/-! ## State interpretation (the `encReg` bridge) -/

/-- The register heap cell holds the `encReg`-encoding of the real register value. -/
def regAgree (rm : RegF (BitVec 64)) (sregs : (r : Register) → Option (RegisterType r)) : Prop :=
  ∀ r, Std.PartialMap.get? (M := RegF) rm r = (sregs r).map (encReg r)

def memAgree (mm : MemF (BitVec 8)) (smem : Nat → Option (BitVec 8)) : Prop :=
  ∀ a, Std.PartialMap.get? (M := MemF) mm a = smem a

def stateInterpDef (σ : MState) : IProp GF :=
  iprop(∃ rm mm, genHeapInterp (G := D.reg) rm ∗ genHeapInterp (G := D.mem) mm ∗
    ⌜regAgree rm σ.regs⌝ ∗ ⌜memAgree mm σ.mem⌝)

instance instStateInterp : StateInterp MState Empty GF where
  stateInterp σ _ _ _ := stateInterpDef σ

instance instIrisGS : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

/-! ## Read bridges -/

/-- Owning `r ↦ᵣ v` forces the register's encoded value to be `v`. For a 64-bit
register (GPR / PC / scalar CSR) `encReg r` is the identity, so this pins the
register's actual value. -/
theorem reg_valid {σ : MState} {r : Register} {dq v} :
    (stateInterpDef σ : IProp GF) ∗ regPt r dq v ⊢ |==> ⌜(σ.regs r).map (encReg r) = some v⌝ := by
  unfold stateInterpDef regPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Hr⟩
  imod genHeap_valid_at D.reg $$ [$Hi $Hr] with %Hlk
  ipureintro
  rw [← Hag r]; exact Hlk

/-- Owning `a ↦ₘ b` forces `σ.mem a = some b`. -/
theorem mem_valid {σ : MState} {a : Nat} {dq b} :
    (stateInterpDef σ : IProp GF) ∗ memPt a dq b ⊢ |==> ⌜σ.mem a = some b⌝ := by
  unfold stateInterpDef memPt
  iintro ⟨⟨%rm, %mm, Hi, Hm, %Hag, %Hmag⟩, Ha⟩
  imod genHeap_valid_at D.mem $$ [$Hm $Ha] with %Hlk
  ipureintro
  rw [← Hmag a]; exact Hlk

/-! ## Write bridges -/

/-- Update `r ↦ᵣ v₁` to `r ↦ᵣ v₂`, writing `decReg r v₂` into the register state.
The round-trip hypothesis `encReg r (decReg r v₂) = v₂` is `rfl` for the 64-bit
registers (where `encReg`/`decReg` are the identity). -/
theorem reg_update {σ : MState} {r : Register} {v₁ v₂ : BitVec 64}
    (hrt : encReg r (decReg r v₂) = v₂) :
    (stateInterpDef σ : IProp GF) ∗ regPt r (.own 1) v₁ ⊢
      |==> (stateInterpDef (σ.setReg r (decReg r v₂)) ∗ regPt r (.own 1) v₂) := by
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
  · subst hrr; simp [MState.setReg, hrt]
  · rw [if_neg hrr]
    simp only [MState.setReg]
    rw [dif_neg (fun h => hrr h.symm)]
    exact Hag r'

/-- Update `a ↦ₘ b₁` to `a ↦ₘ b₂`. -/
theorem mem_update {σ : MState} {a : Nat} {b₁ b₂ : BitVec 8} :
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

end

end Xv6Iris.Model
