(* LinkIput.v -- THE SLOT ProofIput.v LANDS IN, and deliberately EMPTY.

   This file used to carry iput's contract as an [Axiom] at the frozen
   [emp]-shaped statement ([SpecIput.IPUT]).  That axiom has MOVED, not
   multiplied: it is now [LinkIputCompat.IputCompat.wp_iput_sconf], which
   is what the six old cones (kexit, fileclose, pipealloc, sys_close,
   sys_exit, sys_pipe) consume -- see that file's header for what it
   asserts and why it is not derivable from the real contract.

   Leaving a SECOND copy of it here would put an assumption in the tree
   that nothing consumes and that [tools/proof_coverage.py]'s axiom census
   would have to explain, so the file is emptied rather than kept: there is
   now EXACTLY ONE iput assumption in the tree, and it is the bridging one.

   WHAT GOES HERE NEXT.  [ProofIput.v] proves
   [SpecIput.wp_iput2_sconf_body] -- iput over the real inode cache -- as a
   functor over its callees' interfaces (acquire, release, the NESTED
   acquiresleep, releasesleep, itrunc, iupdate), and this file becomes

       Require Import LinkAcquire LinkRelease LinkAcquiresleep
                      LinkReleasesleep LinkItrunc LinkIupdate ProofIput.
       Module Iput : IPUT2 :=
         IputProof Acquire Release Acquiresleep Releasesleep Itrunc Iupdate.

   with no [Axiom] at any point.  C6b then repoints the six cones back here
   and deletes [LinkIputCompat.v] (its header carries the plan).           *)
Require Import SpecIput.
