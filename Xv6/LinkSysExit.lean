/-
`sys_exit` meets its specification, given `argint` and `kexit`.

`SysExitClosed` is the fully closed form (every parameter at its linked,
closed term).
-/
import Xv6.ProofSysExit
import Xv6.LinkArgraw
import Xv6.LinkArgint
import Xv6.LinkKexit

namespace Xv6

theorem SysExit (AI : ARGINT) (KX : KEXIT) : SYSEXIT := sys_exit_proof AI KX

/-- `sys_exit` CLOSED over the linked `argint` and `KexitClosed`. -/
theorem SysExitClosed : SYSEXIT := SysExit (Argint Myproc (Argraw Myproc)) KexitClosed

end Xv6
