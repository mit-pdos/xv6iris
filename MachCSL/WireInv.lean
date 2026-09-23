/-
MachCSL: the interrupt PINS, as one invariant.

`sig_meip`/`sig_seip` are ordinary registers of every hart, but they are
driven by the PLIC's wire step (`DevOp.setPin`, `MachCSL.Lang`), which may
fire at any moment: no hart-side proof may pin their value, and the device
loop never cares what the old value was (it only overwrites).  So the two
cells of every hart live -- with their contents EXISTENTIALLY quantified --
in one invariant (`wireInv`), which is therefore persistent and freely
shared between the CPU-side proofs and the device threads.

The hart side reads them OFF-FRAME: `swp_readReg_any` needs no ownership at
all (the read does not move the state, so the state interpretation goes
straight back), and hands the caller a ∀-bound answer.  That is what lets
the `read_mip` chain quantify over the pending word instead of pinning it.

The Rocq prototype: `WireInv.v` (`wire_inv_body`, `wire_inv_alloc`) and
`WpIntrCore.v:115-175` (`swp_read_reg_any`).
-/
import MachCSL.Wp
import Iris.Instances.Lib.Invariants

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-! ## Off-frame register reads

A register read moves nothing, so the rule needs no cell at all: the state
interpretation is handed back untouched (`machInterp_acc_read` splits one
hart's register interpretation out and puts it straight back), and the
answer is universally quantified. -/

/-- Read a register WITHOUT owning it: the answer is ∀-bound. -/
theorem swp_readReg_any (cpu : CPU) (r : Register) (Φ : RegisterType r → IProp GF) :
    ▷ (∀ v : RegisterType r, Φ v) ⊢ swp cpu (readReg r) Φ := by
  unfold readReg PreSail.readReg PreSail.emit
  iintro HΦ
  iapply swp_event cpu (.regRead r) (fun v => FreeM.pure v) Φ (fun _ _ h => h)
  iintro %σ Hσ
  icases machInterp_acc_read σ cpu $$ Hσ with ⟨Hregs, Hclose⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    exact ⟨σ.regs cpu r, σ, rfl, rfl⟩
  inext
  iintro %v' %σ' %Hev
  obtain ⟨-, rfl⟩ := Hev
  imod Hmask
  imodintro
  isplitl [Hregs Hclose]
  · iapply Hclose $$ Hregs
  · iapply swp_ret
    iapply HΦ $$ %v'

/-- The `>>=` form of `swp_readReg_any`. -/
theorem swp_readReg_any_bind (cpu : CPU) {X : Type} (r : Register)
    (f : RegisterType r → SailM X) (Φ : X → IProp GF) :
    ▷ (∀ v : RegisterType r, swp cpu (f v) Φ) ⊢ swp cpu (readReg r >>= f) Φ := by
  iintro HΦ
  iapply swp_bind
  iapply swp_readReg_any cpu r (fun v => swp cpu (f v) Φ) $$ HΦ

/-! ## The wire invariant -/

def wireN : Namespace := ndot nroot "machcslwire"

/-- Value-agnostic ownership of every hart's two interrupt-pin cells.  The
per-hart values are existentially quantified (as total functions over the
harts), so re-establishing the body after overwriting one hart's pin is
trivial -- which is what makes the invariant shareable. -/
def wireBody : IProp GF := iprop%
  ∃ seip meip : CPU → BitVec 1, [∗list] cpu ∈ cpus,
    (Register.sig_seip ↦ᵣ[cpu] seip cpu ∗ Register.sig_meip ↦ᵣ[cpu] meip cpu)

/-- The pins of every hart, at unspecified levels. -/
def wireInv : IProp GF := inv wireN (wireBody (GF := GF))

instance wireBody_timeless : Timeless (wireBody (GF := GF)) := by
  unfold wireBody regPointsTo regPointsToAt; infer_instance

instance wireInv_persistent : Persistent (wireInv (GF := GF)) := by
  unfold wireInv; infer_instance

/-- Allocate the invariant from the owned pin cells, at any levels. -/
theorem wireInv_alloc (E : CoPset) (seip meip : CPU → BitVec 1) :
    ([∗list] cpu ∈ cpus,
        (Register.sig_seip ↦ᵣ[cpu] seip cpu ∗ Register.sig_meip ↦ᵣ[cpu] meip cpu))
      ⊢@{IProp GF} |={E}=> wireInv := by
  iintro Hcells
  unfold wireInv
  iapply inv_alloc wireN E (wireBody (GF := GF))
  inext
  unfold wireBody
  iexists seip, meip
  iexact Hcells

/-- Take hart `cpu`'s two pin cells out of the body, with a closing wand
that accepts them back at ANY levels. -/
theorem wireBody_take (cpu : CPU) :
    wireBody (GF := GF) ⊢
      ∃ s m : BitVec 1,
        Register.sig_seip ↦ᵣ[cpu] s ∗ Register.sig_meip ↦ᵣ[cpu] m ∗
        ∀ (s' : BitVec 1), ∀ (m' : BitVec 1),
          Register.sig_seip ↦ᵣ[cpu] s' -∗ Register.sig_meip ↦ᵣ[cpu] m' -∗ wireBody := by
  have hget := cpus_get? cpu
  unfold wireBody
  iintro ⟨%seip, %meip, Hlist⟩
  icases BigSepL.bigSepL_lookup_acc_impl
    (Φ := fun _ c => iprop(Register.sig_seip ↦ᵣ[c] seip c ∗ Register.sig_meip ↦ᵣ[c] meip c))
    hget $$ Hlist with ⟨⟨Hs, Hm⟩, Hclose⟩
  iexists seip cpu, meip cpu
  iframe Hs Hm
  iintro %s' %m' Hs' Hm'
  iexists (updCpu seip cpu s'), (updCpu meip cpu m')
  iapply Hclose $$ %(fun _ c => iprop(Register.sig_seip ↦ᵣ[c] updCpu seip cpu s' c ∗
    Register.sig_meip ↦ᵣ[c] updCpu meip cpu m' c))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ cpu := cpus_get?_ne hk cpu hne
    simp only [updCpu, hy, if_false]
    iexact Hy
  · simp only [updCpu, if_true]
    iframe Hs' Hm'

end MachCSL
