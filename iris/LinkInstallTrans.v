(* LinkInstallTrans.v -- instantiates the InstallTrans proof against its
   callees' proofs (bread / bwrite / bunpin / brelse / memmove).  Sealed, so
   this is the only place the six ever meet.

   printk is NOT among them, and that is not an omission: install_trans's
   [recovering] block at +0x46 is dead on every instance stage 2 states
   ([recovering = false \/ n = 0] -- at n = 0 the function returns from the
   pre-frame [blez] having executed nothing, and otherwise s6 = 0 makes both
   [bnez s6] fall through), so the proof never reaches the call. *)
Require Import LinkBread LinkBwrite LinkBunpin LinkBrelse LinkMemmove ProofInstallTrans.

Module InstallTrans := InstallTransProof Bread Bwrite Bunpin Brelse Memmove.
