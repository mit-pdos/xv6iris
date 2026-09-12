/-
The kernel's read-only image as `kctx` owns it: the text (`kernelText`)
and the rodata (`kernelData`), one persistent proposition.  A function's
contract states neither; a proof takes them out of the context once.
-/
import MachCSL.KCtx
import Xv6.KernelText
import Xv6.KernelData

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The kernel's read-only image, as `kctx` owns it: the text and the rodata. -/
instance : KernelImage GF := ⟨iprop(kernelText ∗ kernelData), inferInstance⟩

/-- The context's copy of the image, spelled out. -/
theorem kctx_image [CurCtx] [KernelGeom] (cpu : CPU) (k : KCtx) :
    kctx (GF := GF) cpu k ⊢ (kernelText ∗ kernelData) ∗ kctx cpu k :=
  kctx_ro cpu k

/-- The context's copy of the kernel text: a proof takes it out once
(`icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩`) and derives every
instruction fact from it. -/
theorem kctx_kernelText [CurCtx] [KernelGeom] (cpu : CPU) (k : KCtx) :
    kctx (GF := GF) cpu k ⊢ kernelText ∗ kctx cpu k := by
  iintro H
  icases kctx_image _ _ $$ H with ⟨⟨#Htext, _⟩, H⟩
  iframe H
  iexact Htext

/-- The context's copy of the read-only data. -/
theorem kctx_kernelData [CurCtx] [KernelGeom] (cpu : CPU) (k : KCtx) :
    kctx (GF := GF) cpu k ⊢ kernelData ∗ kctx cpu k := by
  iintro H
  icases kctx_image _ _ $$ H with ⟨⟨_, #HD⟩, H⟩
  iframe H
  iexact HD

end Xv6
