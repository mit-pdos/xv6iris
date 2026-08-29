(* LinkFilewriteCons.v -- filewrite's CONSOLE arm, composed with its one
   callee's proof.

   [LinkFilewrite.v] with SEVEN of the eight arguments gone and the eighth
   swapped: [ProofFilewriteCons]'s premises put the pipe arm, the whole
   FD_INODE loop (ilock, writei, iunlock, begin_op, end_op) and the panic
   arm outside the contract's domain, so the only callee left is the device
   dispatch's -- and it arrives at the LOCATED contract
   ([LinkConsolewriteLoc.ConsolewriteLoc]) rather than the landed one,
   because this arm has to hand its caller the transmitted count's receipt.

   WHAT THIS BUYS.  [LinkFilewrite.v]'s cone assumes consolewrite (its
   header: "the only device xv6 installs, and consolewrite has no proof").
   That is no longer true -- [LinkConsolewriteLoc.v]'s header records that
   the whole device-side chain from the THR store up to consolewrite's
   return value is PROVED -- so [FilewriteCons] is a CLOSED instance of
   [SpecFilewriteCons.FILEWRITE_CONS].

   AUDIT (machine-checked, [Print Assumptions FilewriteCons.wp_filewrite_cons]
   on the EC2 mirror at 523cc4e8): THE STANDING THREE and nothing else --
   [xv6iris_extras.resv_matches], [xv6iris_extras.resv_is_valid],
   [functional_extensionality_dep].  Note what is NOT there: the console
   arm's cone carries no assumption of its own, so the device write is
   proved on the same footing as the rest of the tree. *)
Require Import LinkConsolewriteLoc ProofFilewriteCons.

Module FilewriteCons := FilewriteConsProof ConsolewriteLoc.
