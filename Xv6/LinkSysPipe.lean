/-
`sys_pipe` meets its specification, given `myproc`, `argaddr`, `pipealloc`,
`fdalloc`, `copyout` and `fileclose`.
-/
import Xv6.ProofSysPipe

namespace Xv6

theorem SysPipe (MP : MYPROC) (AA : ARGADDR) (PA : PIPEALLOC) (FD : FDALLOC) (CO : COPYOUT) (FC : FILECLOSE) :
    SYSPIPE :=
  sys_pipe_proof MP AA PA FD CO FC

end Xv6
