/-
`sys_sbrk` meets its specification, given `argint`, `myproc` and `growproc`.
-/
import Xv6.ProofSysSbrk

namespace Xv6

theorem SysSbrk (AI : ARGINT) (MP : MYPROC) (GP : GROWPROC) : SYSSBRK := sys_sbrk_proof AI MP GP

end Xv6
