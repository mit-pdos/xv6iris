/-
The allocator's ghosts, born: the count at zero, tracked by the client
(Rocq `KallocInv.kalloc_avail_alloc`).  `wp_kinit` no longer mints them
(SpecKinit, "debt (E)"): this is the era-side allocation whose output is
`Xv6.fsKitKalloc`'s count rows, handed to `wp_kinit` at `fsReadyKmem`.
-/
import Xv6.KallocDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- Fresh allocator ghosts: the client tracks a count of `0`, the allocator
holds its half. -/
theorem kmemGhost_alloc : ⊢@{IProp GF} |==> ∃ γk : KmemNames, kallocAvail γk (some 0) ∗ kmemAuth γk 0 := by
  iintro
  imod ghost_var_alloc (0 : Nat) with ⟨%γc, Hc⟩
  imod ghost_var_alloc (() : Unit) with ⟨%γp, Hp⟩
  imodintro
  iexists ⟨γc, γp⟩
  rw [kallocAvail_some]
  unfold kmemAuth
  have hs := ghost_var_split (GF := GF) γc (0 : Nat) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  icases hs $$ Hc with ⟨Hc1, Hc2⟩
  isplitl [Hp Hc1]
  · iframe
  ileft; iexact Hc2

end

end Xv6
