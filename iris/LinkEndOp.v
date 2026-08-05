(* LinkEndOp.v -- instantiates the EndOp proof against its callees' proofs
   (acquire / release / wakeup / bread / bwrite / brelse / memmove, plus the
   two committer-only helpers write_head and install_trans).  Sealed, so this
   is the only place the ten ever meet.

   panic is NOT among them, and that is not an omission: end_op's single
   panic site (+0x6e "log.committing") is DEAD -- an op token in hand forces
   log.outstanding >= 1, and log_res's ⌜cmt = true -> out = 0⌝ then forces
   committing = 0, so the [c.bnez] at +0x24 falls through and the arm is
   never reached.  The [panic_wp_any] end_op threads is its CALLEES'. *)
Require Import LinkAcquire LinkRelease LinkWakeup LinkBread LinkBwrite
               LinkBrelse LinkMemmove LinkWriteHead LinkInstallTrans ProofEndOp.

Module EndOp := EndOpProof Acquire Release Wakeup Bread Bwrite Brelse Memmove
                           WriteHead InstallTrans.
