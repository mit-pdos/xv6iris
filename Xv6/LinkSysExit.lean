/-
`sys_exit` meets its specification, given `argint` and `kexit`.
-/
import Xv6.ProofSysExit

namespace Xv6

theorem SysExit (AI : ARGINT) (KX : KEXIT) : SYSEXIT := sys_exit_proof AI KX

end Xv6
