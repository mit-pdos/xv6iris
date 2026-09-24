/-
`sys_fork` meets its specification, given `kfork` (whose own link,
`Xv6/LinkKfork.lean`, still takes its callee interfaces as parameters).
-/
import Xv6.ProofSysFork

namespace Xv6

/-- The proved `sys_fork` interface, given `kfork`. -/
theorem SysFork (KF : KFORK) : SYSFORK := sys_fork_proof KF

end Xv6
