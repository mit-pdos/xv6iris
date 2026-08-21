(* LinkSysMknod.v -- instantiates the sys_mknod proof against its six
   callees' proofs.  Sealed, so this is the only place the seven ever meet.

   The cone is LinkSysMkdir.v's plus argint (and, under it, argraw), and
   nothing else: the two functions differ in what they put in create's
   argument registers and in nothing that reaches a module.  So this file
   assumes exactly what LinkSysMkdir.v does, and for the same reasons --
   see that header for the two create clauses the composition rests on.

   The one thing that is this function's own is the [ARGINT] argument, and
   it is where the two [int] locals come from: argint writes 4-byte cells
   into frame slot 19 and the [lh]s at +0x32 / +0x36 read the low halfword
   of each.  Nothing about that carving reaches a module boundary --
   [ProofSysMknod.word4_pointsto_split2] / [_join2] are local to the proof.

   panic is NOT a module here.  Every panic sys_mknod can reach is inside a
   callee -- argraw's out-of-range arm included, which is why the index
   premises are [i < NARG] and not a branch; the [kernel_data] / [panic_env]
   the contract takes are threaded down to the callees' own arms.

   So this cone's assumption count is the five platform axioms plus
   funext, and nothing else. *)
Require Import LinkBeginOp LinkArgint LinkArgstr LinkCreate LinkIunlockput
        LinkEndOp ProofSysMknod.

Module SysMknod := SysMknodProof BeginOp Argint Argstr Create Iunlockput EndOp.
