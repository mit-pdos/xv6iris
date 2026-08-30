(* LinkSysReadAU.v -- instantiates sys_read's ATOMIC-UPDATE proof against its
   callees' proofs.  This is where [SpecSysReadAUAt.SYSREAD_AU_AT] stops being
   a module type over an assumed callee and becomes an UNCONDITIONAL pair of
   theorems: [SysReadAU.wp_sys_read_au_at] and
   [SysReadAU.wp_sys_read_au_at_stable].

   The four callees are argaddr, argint, argfd and [FILEREAD_AU], and the last
   of them is [LinkFilereadAU]'s -- which is why this cone does NOT carry
   [LinkConsoleread]'s Axiom even though [LinkSysRead]'s does: the AU
   contract's premise refutes the device arm rather than walking it.

   BOTH FIELDS COME FROM ONE MODULE, unlike the write lane, where the stable
   corollary had its own module type and therefore its own link.
   [SYSREAD_AU_AT] carries the AU form and the stable corollary side by side,
   so [ProofSysReadAUStable] is the file that seals the pair (it [Include]s
   [ProofSysReadAU]'s walk) and this is its single instantiation. *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFilereadAU
                ProofSysReadAUStable.

Module SysReadAU := SysReadAUProof Argaddr Argint Argfd FilereadAU.
