/-
Link `sys_getpid`: the sealed proof instance clients import.  `sys_getpid`
calls only `myproc`; its proof is closed with the linked `Myproc`.
-/
import Xv6.ProofSysGetpid
import Xv6.LinkMyproc

namespace Xv6

/-- The proved `sys_getpid` interface. -/
theorem SysGetpid : SYSGETPID := sys_getpid_proof Myproc

end Xv6
