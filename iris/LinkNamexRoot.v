(* LinkNamexRoot.v -- namex's root corner meets its ONE callee.

   The corner calls [iget] and nothing else (see [ProofNamexRoot.v]'s
   header), so this link is a single functor application over
   [LinkIget.Iget] -- itself a real proof over acquire/release on the itable
   spinlock, with no axiom of its own.  The walk's other eight callees
   (myproc, idup, memmove, ilock, iunlock, iunlockput, dirlookup, iput) are
   [LinkNamex.v]'s, and none of them is in this cone. *)
Require Import LinkIget.
Require Import ProofNamexRoot.

Module NamexRoot := NamexRootProof Iget.
