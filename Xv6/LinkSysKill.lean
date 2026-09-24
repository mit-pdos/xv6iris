/-
`sys_kill` meets its specification, given `argint` and `kkill`.
-/
import Xv6.ProofSysKill

namespace Xv6

theorem SysKill (AI : ARGINT) (KK : KKILL) : SYSKILL := sys_kill_proof AI KK

end Xv6
