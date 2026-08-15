(* LinkForkret.v -- instantiates forkret's proof against its four
   interfaces: myproc, release and prepare_return (all three PROVEN), and
   the CLOSED trap loop [LinkUserretClosed]'s [UserretClosedD], which is
   userret + user execution + uservec + usertrap composed.

   Type-checking this file is what makes forkret's contract a statement
   about the actual kernel: the residue [wp_forkret]'s wand produces is the
   one usertrap's own proof defines, and the machine forkret's [c.jalr]
   lands on is the trap loop's real entry.

   [Print Assumptions Forkret.wp_forkret] is therefore the standing platform
   axioms + functional extensionality + the two U-mode reservation effects +
   whatever the trap loop already carries ([LinkSyscall]'s and
   [LinkPrintk]'s, through usertrap). *)
Require Import LinkMyproc LinkRelease LinkPrepareReturn LinkUserretClosed.
Require Import ProofForkret.

Module Forkret := ForkretProof Myproc Release PrepareReturn UserretClosedD.
