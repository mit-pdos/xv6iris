/-
Link `usertrap` (Rocq `LinkUsertrap.v`: `Module Usertrap := UsertrapProof
Syscall PrintkGen Myproc Killed Setkilled Devintr Vmfault Yield
PrepareReturn Kexit Kernelvec`).

Closed with their linked interfaces: printk, myproc, killed, setkilled,
devintr (both contracts: `Devintr`, `DevintrNone`), yield,
prepare_return, and kernelvec over the linked kerneltrap.  Left as
parameters, as their own links leave them: `fileclose` (kexit's,
`LinkKexit`), `vmfault` (its `LinkVmfault` takes its callees), and
`syscall` -- in the kstack-row form `SYSCALLKS` (UsertrapSysSpec; the seal is
W8-E2's) -- and the deposit instance's read reason `UtReadWhy`
(UsertrapParts; W8-K's, at the instance).
-/
import Xv6.ProofUsertrap
import Xv6.LinkPrintk
import Xv6.LinkMyproc
import Xv6.LinkKilled
import Xv6.LinkSetkilled
import Xv6.LinkDevintr
import Xv6.LinkDevintrNone
import Xv6.LinkYield
import Xv6.LinkPrepareReturn
import Xv6.LinkKexit
import Xv6.LinkKernelvec
import Xv6.LinkKerneltrap

namespace Xv6

open Iris MachCSL

/-- The proved `usertrap` interface (at the corrected post `USERTRAPK`),
given `syscall`, `fileclose`, `vmfault` and the read reason. -/
theorem Usertrap (SY : SYSCALLKS) (FC : FILECLOSE) (VF : VMFAULT)
    (hW : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [UexecSG GF],
      UtReadWhy (GF := GF)) : USERTRAPK :=
  usertrap_proof SY Printk Myproc Killed Setkilled Devintr DevintrNone VF Yield PrepareReturn
    (Kexit FC) (Kernelvec (Kerneltrap Yield)) hW

end Xv6
