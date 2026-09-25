/-
Link `usertrap` (Rocq `LinkUsertrap.v`: `Module Usertrap := UsertrapProof
Syscall PrintkGen Myproc Killed Setkilled Devintr Vmfault Yield
PrepareReturn Kexit Kernelvec`).

Closed with their linked interfaces: printk, myproc, killed, setkilled,
devintr, yield,
prepare_return, kernelvec over the linked kerneltrap, and `syscall` by
`LinkSyscall.Syscall` (the contract at the kernel's deposit instance,
`SYSCALL_XV6`).  Left as parameters, as their own links leave them:
`fileclose` (kexit's, `LinkKexit`), `vmfault` (its `LinkVmfault` takes its
callees), `LinkSyscall`'s own parameters (the four lock / allocator leaves
and `[ForkretIs]`), and the deposit instance's read reason `UtReadWhy`
(UsertrapParts; W8-K's, at the instance).
-/
import Xv6.ProofUsertrap
import Xv6.LinkPrintk
import Xv6.LinkMyproc
import Xv6.LinkKilled
import Xv6.LinkSetkilled
import Xv6.LinkDevintr
import Xv6.LinkYield
import Xv6.LinkPrepareReturn
import Xv6.LinkKexit
import Xv6.LinkKernelvec
import Xv6.LinkKerneltrap
import Xv6.LinkSyscall

namespace Xv6

open Iris MachCSL

/-- The proved `usertrap` interface,
given `fileclose`, `vmfault`, `LinkSyscall`'s parameters and the read
reason. -/
theorem Usertrap (RG : RELEASE_GEN) (RR : RELEASE_REFUTE) (RC : RELEASE_CANCEL) (KFF : KFREE_FREE)
    [ForkretIs] (FC : FILECLOSE) (VF : VMFAULT)
    (hW : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [UexecSG GF],
      UtReadWhy (GF := GF)) : USERTRAP :=
  usertrap_proof (Syscall RG RR RC KFF) Printk Myproc Killed Setkilled Devintr VF Yield PrepareReturn
    (Kexit FC) (Kernelvec (Kerneltrap Yield)) hW

end Xv6
