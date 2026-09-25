/-
Link `sys_open` (Rocq `LinkSysOpen.v`: `SysOpenProof Argint Argstr BeginOp
NameiEra Ilock Iunlock Iunlockput EndOp Fileclose Itrunc Filealloc Fdalloc
Create`), the only place sys_open's proof meets its thirteen callees'.

namei enters at the ERA contract (`LinkNameiEra.NameiEra`), create through
`LinkCreate`.  `copyout` / `copyin` stay parameters, as in `LinkNameiEra` /
`LinkCreate`; argstr's `fetchstr` is closed over the linked `copyinstr` /
`strlen`, whose page-table walkers (`walkaddr`, `vmfault`) stay parameters,
as in `LinkSysUnlink`.  fileclose's pipe arm (`pipeclose`) stays a
parameter: `LinkPipeclose` itself still takes its own callees (sys_open's
fileclose only ever closes an UNTYPED file, `filecloseEnv_none`).
-/
import Xv6.ProofSysOpen
import Xv6.LinkMyproc
import Xv6.LinkArgraw
import Xv6.LinkArgint
import Xv6.LinkFetchstr
import Xv6.LinkCopyinstr
import Xv6.LinkStrlen
import Xv6.LinkArgstr
import Xv6.LinkBeginOp
import Xv6.LinkNameiEra
import Xv6.LinkIlock
import Xv6.LinkIunlock
import Xv6.LinkIunlockput
import Xv6.LinkEndOp
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkIput
import Xv6.LinkFileclose
import Xv6.LinkItrunc
import Xv6.LinkFilealloc
import Xv6.LinkFdalloc
import Xv6.LinkCreate

namespace Xv6

/-- The proved `sys_open` interface, given `copyout` / `copyin`, the
page-table walkers `copyinstr` runs over, and `pipeclose`. -/
theorem SysOpen (CO : COPYOUT) (CI : COPYIN) (WA : WALKADDR) (VF : VMFAULT) (PC : PIPECLOSE) :
    SYSOPEN :=
  sys_open_proof (Argint Myproc (Argraw Myproc))
    (Argstr (Argraw Myproc) (Fetchstr Myproc (Copyinstr WA VF) Strlen)) BeginOp (NameiEra CO) Ilock
    Iunlock Iunlockput EndOp (Fileclose Acquire Release PC BeginOp Iput EndOp) Itrunc
    (Filealloc Acquire Release) (Fdalloc Myproc) (Create CO CI)

end Xv6
