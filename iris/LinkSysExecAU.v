(* LinkSysExecAU.v -- sys_exec's ATOMIC-UPDATE proof, closed over its callees.

   [LinkSysExec.v]'s seven copy-in / allocator modules, with kexec's AU
   contract ([LinkKexecAU.KexecAU] for [LinkKexec.Kexec]) in the eighth
   slot -- which is the only argument ProofSysExecAU uses on its own; the
   other seven go straight to [SysExecParts], shared with the landed
   composition. *)
Require Import LinkArgaddr LinkArgstr LinkMemsetArray LinkFetchaddr LinkKalloc
        LinkFetchstr LinkKexecAU LinkKfree
        ProofSysExecAU.

Module SysExecAU := SysExecAUProof Argaddr Argstr MemsetArray Fetchaddr Kalloc
                                   Fetchstr Kfree KexecAU.
