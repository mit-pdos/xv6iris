(* LinkSysChdir.v -- instantiates the sys_chdir proof against its nine
   callees' proofs.  Sealed, so this is the only place the ten ever meet.

   sys_chdir is the first consumer of [SpecNamei]'s SET-FORM contract
   ([wp_namei_gen]): the counted one prices an unbounded walk at
   [(L+1) * iput_units] and cannot leave the tail's [iput] its three units.
   See SpecSysChdir.v's header for that ledger. *)
Require Import LinkMyproc LinkBeginOp LinkArgstr LinkNamei LinkIlock
        LinkIunlock LinkIput LinkIunlockput LinkEndOp ProofSysChdir.

Module SysChdir := SysChdirProof Myproc BeginOp Argstr Namei Ilock Iunlock
                                Iput Iunlockput EndOp.
