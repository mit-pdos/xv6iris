(* LinkSysChdirAU.v -- instantiates sys_chdir's AU proof ([ProofSysChdirAU])
   against its nine callees' proofs, with the era walk ([LinkNameiEra]) in
   place of the SET-form namei.  Sealed, so this is the only place the ten
   meet.  The landed [LinkSysChdir] stays beside it (R10): the AU form is a
   parallel contract, and the dispatcher ([LinkSyscall]) takes this one. *)
Require Import LinkMyproc LinkBeginOp LinkArgstr LinkNameiEra LinkIlock
        LinkIunlock LinkIput LinkIunlockput LinkEndOp ProofSysChdirAU.

Module SysChdirAU := SysChdirAUProof Myproc BeginOp Argstr NameiEra Ilock Iunlock
                                    Iput Iunlockput EndOp.
