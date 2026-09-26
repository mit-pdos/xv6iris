/-
MachCSL: register-node rules for the user tier (Rocq `HartRegNode.v`).

`swp_writeReg_same` (Rocq `swp_write_reg_same`): a write of the value a
register already holds moves nothing, so it needs the cell at ANY fraction,
`□` included.  This is how a hart "writes" a frozen `hw_config` cell (the
`reset_elp` of every trap, USER ruling D52).  `regPointsTo_discard_persistent`
makes Rocq's `↦ᵣ□` cells persistent.

**Namespaced (`MachCSL.URegNode`) on purpose**: the D52 lane's
`MachCSL/HwConfig.lean` (worktree, not yet merged) carries the same two facts
under the root names `swp_writeReg_same` / `regPointsTo_discard_persistent`.
Once it lands, this file is redundant: delete it, import `MachCSL.HwConfig`
in UDispatch/UTrap, and drop the `URegNode.` qualifier (one use, UTrap).
-/
import MachCSL.WpTrap

namespace MachCSL
namespace URegNode

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A discarded register cell is persistent (Rocq's `↦ᵣ□`, the shape of the
frozen `hw_config` cells). -/
instance regPointsTo_discard_persistent (cpu : CPU) (r : Register) (v : RegisterType r) :
    Persistent (PROP := IProp GF) (r ↦ᵣ[cpu]□ v) := by
  unfold regPointsTo regPointsToAt; infer_instance

/-- Writing a register with the value it already holds leaves the state as
it is. -/
theorem MState.setReg_self (σ : MState) (cpu : CPU) (r : Register) :
    σ.setReg cpu r (σ.regs cpu r) = σ := by
  have hf : (σ.regs cpu).set r (σ.regs cpu r) = σ.regs cpu := by
    funext r'
    by_cases h : r' = r
    · subst h; simp
    · rw [RegFile.set_other _ _ _ _ h]
  show { σ with regs := updCpu σ.regs cpu ((σ.regs cpu).set r (σ.regs cpu r)) } = σ
  rw [hf]; exact MState.update_self σ cpu

/-- **Rocq `swp_write_reg_same`**: write a register with the value it
already holds.  Needs the cell at ANY fraction (`□` included), since nothing
moves; this is how a hart "writes" a frozen `hw_config` cell (`reset_elp`
on every trap). -/
theorem swp_writeReg_same (cpu : CPU) (r : Register) (dq : DFrac) (v : RegisterType r)
    (Φ : PUnit → IProp GF) :
    r ↦ᵣ[cpu]{dq} v ∗ ▷ (r ↦ᵣ[cpu]{dq} v -∗ Φ ()) ⊢ swp cpu (writeReg r v) Φ := by
  unfold writeReg PreSail.writeReg PreSail.emit
  iintro ⟨Hr, HΦ⟩
  iapply swp_event cpu (.regWrite r v) (fun v => FreeM.pure v) Φ (fun _ _ h => h)
  iintro %σ Hσ
  icases machInterp_acc_read σ cpu $$ Hσ with ⟨Hregs, Hclose⟩
  ihave %Hv : ⌜σ.regs cpu r = v⌝ $$ [Hregs Hr]
  · icases reg_valid cpu (σ.regs cpu) r dq v $$ [$Hregs $Hr] with %_
    itrivial
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    exact ⟨(), σ.setReg cpu r v, rfl⟩
  inext
  iintro %v' %σ' %Hev
  have hσ : σ' = σ := by rw [Hev, ← Hv, MState.setReg_self]
  subst hσ
  imod Hmask
  imodintro
  isplitl [Hregs Hclose]
  · iapply Hclose $$ Hregs
  · iapply swp_ret
    iapply HΦ $$ Hr

end URegNode
end MachCSL
