(* LinkIput.v -- instantiates the iput proof against its callees' proofs.

   NO AXIOM, HERE OR ANYWHERE BELOW.  [ProofIput.v] proves
   [SpecIput.wp_iput_sconf_body] -- iput over the real inode cache -- and
   its six callees (acquire, release, acquiresleep, releasesleep, itrunc,
   iupdate) are real proofs too, so the functor line below is the whole
   file and this cone's assumption count is ZERO.

   As of C6b this is also the ONLY iput instantiation in the tree:
   fileclose and kexit (and hence sys_close, sys_exit, sys_pipe and
   pipealloc) consume it directly, and the bridging axiom that used to
   stand between them -- [LinkIputCompat.v] -- is deleted.               *)
Require Import LinkAcquire LinkRelease LinkAcquiresleep LinkReleasesleep
               LinkItrunc LinkIupdate ProofIput.
(* the off-lock tail's three leaves, new at the task-18 splice: the reordered
   free path flushes [ip->type = 0] by hand (bread / sh / log_write / brelse
   at +0xa8) instead of calling iupdate, so iput now instantiates them too.
   All three are real proofs; the assumption count is still ZERO. *)
Require Import LinkBread LinkLogWrite LinkBrelse.

Module Iput := IputProof Acquire Release Acquiresleep Releasesleep Itrunc Iupdate
                         Bread LogWrite Brelse.
