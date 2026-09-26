/-
`sys_seccomp` meets its specification (xv6 7b2c1b1b), given `argaddr` and
`myproc`.
-/
import Xv6.ProofSysSeccomp

namespace Xv6

theorem SysSeccomp (AA : ARGADDR) (MP : MYPROC) : SYSSECCOMP := sys_seccomp_proof AA MP

end Xv6
