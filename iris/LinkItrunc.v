(* LinkItrunc.v -- the only file where itrunc's proof meets its callees'.
   All four callees -- bread, bfree, brelse and iupdate -- are PROVEN, so
   itrunc carries no caveat in tools/proof_coverage.py.

   itrunc has no panic of its own: the C never calls panic on any path, and
   the two panics reachable through its callees (bfree's "freeing free
   block" and bread's interior arm) are refuted inside those proofs.  So no
   panic contract is instantiated here.

   THE BUDGET is what made this possible at all.  itrunc calls bfree up to
   NDIRECT + NINDIRECT + 1 = 269 times and then iupdate once; under the
   log's old always-consume accounting that was 270 units against a
   MAXOPBLOCKS of 10, which no caller could supply.  Since FSSIZE = 2000 <
   BPB = 8192 there is exactly ONE bitmap block, so every free after the
   first is ABSORBED by the log and the true cost is 2 -- one bitmap block,
   one inode block.  The credited arms of log_write and bfree, and the
   per-op already-logged set they read, are what let that be stated and
   proven.  See claude-notes/design/fs-log.md's decision record. *)
Require Import LinkBread LinkBfree LinkBrelse LinkIupdate ProofItrunc.

Module Itrunc := ItruncProof Bread Bfree Brelse Iupdate.
