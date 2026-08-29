(* LinkSysWriteAU.v -- instantiates sys_write's ATOMIC-UPDATE proof against
   its callees' proofs.  This is where [SpecSysWriteAUEra.SYSWRITE_AU_ERA]
   stops being a module type over an assumed callee and becomes an
   UNCONDITIONAL theorem: [SysWriteAU.wp_sys_write_au_era].

   The four callees are argaddr, argint, argfd and [FILEWRITE_AU], and the
   last of them is [LinkFilewriteAU]'s -- which is why this cone does NOT
   carry [LinkConsolewrite]'s Axiom even though [LinkSysWrite]'s does: the
   AU contract's premise refutes the device arm rather than walking it.

   [LinkSysWriteAUStable] is the corollary's link and lives beside this
   one; it takes THIS module and nothing else. *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFilewriteAU
                ProofSysWriteAU.

Module SysWriteAU := SysWriteAUProof Argaddr Argint Argfd FilewriteAU.
