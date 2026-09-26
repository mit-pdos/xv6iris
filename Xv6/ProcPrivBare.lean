/-
Xv6: the process block minus its descriptor array -- `procFieldsNoOfile`
and `procPrivBareAt` (Rocq `proc_priv_bare` plus the lazy claim).  Kept
apart from the fd table (`FdTable`) so the callees stated over the bare
block (`EitherDefs`, `fetchstr`, `argstr`) do not wait for it.
-/
import Xv6.ProcDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- `procFieldsNoctx` minus the descriptor array. -/
def procFieldsNoOfile (pa : BitVec 64) (dq : DFrac) (V : ProcPriv) : IProp GF := iprop%
  wordPointsTo (pKstack pa) 8 dq V.kstack ∗
  wordPointsTo (pSz pa) 8 dq V.sz ∗
  wordPointsTo (pPagetable pa) 8 dq V.pagetable ∗
  wordPointsTo (pTrapframe pa) 8 dq V.trapframe ∗
  wordPointsTo (pCwd pa) 8 dq V.cwd ∗
  pnameCells pa dq V.name ∗
  wordPointsTo (pSecc pa) 8 dq V.pvSecc

/-- `procPrivNoctxAt` minus the descriptor array: Rocq `proc_priv_bare` plus
the lazy claim -- the block's cwd-free, fd-free part.  It is what the
sub-file-layer callees that never touch the working directory are stated
over (`fetchstr`, `argstr`), and the first half of the core (`FdTable`). -/
def procPrivBareAt (ξ : CtxId) (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) : IProp GF := iprop%
  ⌜V.sz.toNat ≤ uvmMaxsz ∧ umBelow V.sz V.upt ∧
    V.pagetable = pageAddr V.upt.root ∧ V.trapframe = pageAddr V.upt.tfp⌝ ∗
  @wordPointsTo hlc GF _ ⟨ξ, KTier.kpt⟩ (pPid pa) 4 pidPriv pid ∗
  @procFieldsNoOfile hlc GF _ ⟨ξ, KTier.kpt⟩ pa (DFrac.own 1) V ∗
  @procPtAt hlc GF _ ⟨ξ, KTier.kpt⟩ V.upt M ∗
  @tfPageAt hlc GF _ ⟨ξ, KTier.kpt⟩ V.upt.tfp V.tf ∗
  ⌜V.pvLazy = false → lazyFree V.upt.um V.sz⌝

end Xv6
