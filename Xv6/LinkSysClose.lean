/-
`sys_close` meets its specification, given `argfd`, `myproc` and `fileclose`.

`SysCloseClosed` is the fully closed form (every parameter at its linked,
closed term).
-/
import Xv6.ProofSysClose
import Xv6.LinkArgraw
import Xv6.LinkArgint
import Xv6.LinkArgfd
import Xv6.LinkMyproc
import Xv6.LinkFileclose

namespace Xv6

theorem SysClose (AF : ARGFD) (MP : MYPROC) (FC : FILECLOSE) : SYSCLOSE := sys_close_proof AF MP FC

/-- `sys_close` CLOSED over the linked `argfd` / `myproc` and `FilecloseClosed`. -/
theorem SysCloseClosed : SYSCLOSE :=
  SysClose (Argfd (Argint Myproc (Argraw Myproc)) Myproc) Myproc FilecloseClosed

end Xv6
