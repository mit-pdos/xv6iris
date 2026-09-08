(* LinkSysChdir.v -- instantiates the sys_chdir proof against its nine
   callees' proofs, so [SpecSysChdir.SYSCHDIR] is an unconditional theorem
   about the machine.  Sealed, so this is the only place the ten ever meet.

   namei enters at the ERA trace contract ([LinkNameiEra.NameiEra]), which
   is a SET-FORM walk: the COUNTED one prices an unbounded walk at
   [(L+1) * iput_units] and cannot leave the tail's [iput] its three units.
   See SpecSysChdir.v's header for that ledger.  Nothing new enters the
   cone -- [LinkNameiEra]'s own assumption set is the two platform axioms
   plus funext.

   THIS IS THE ONLY LINK: sys_chdir has one contract and one proof, and
   [LinkFsSyscalls] repackages THIS module. *)
Require Import LinkMyproc LinkBeginOp LinkArgstr LinkNameiEra LinkIlock
        LinkIunlock LinkIput LinkIunlockput LinkEndOp ProofSysChdir.

Module SysChdir := SysChdirProof Myproc BeginOp Argstr NameiEra Ilock Iunlock
                                 Iput Iunlockput EndOp.
