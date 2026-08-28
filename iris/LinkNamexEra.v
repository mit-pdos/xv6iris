(* LinkNamexEra.v -- the ERA trace walk's nine callees, discharged.

   [LinkNamexTr.v] verbatim, one module name changed: the same nine real
   proofs, none assumed, and no panic of namex's own.  Two of the nine are
   carried but never used -- [Iunlock] (the [L_par] arm) and [Iput] (the
   nameiparent tail of [L_done]) -- because this contract, like the frozen
   one, is ruled at the namei side, and the functor keeps them so this file
   is the landed one's shape.

   So this cone's assumption count stays at the five platform axioms plus
   funext. *)
Require Import LinkMyproc LinkIdup LinkIget LinkMemmove.
Require Import LinkIlock LinkIunlock LinkIunlockput LinkDirlookup LinkIput.
Require Import ProofNamexEra.

Module NamexEra := NamexEraProof Myproc Idup Iget Memmove
                                 Ilock Iunlock Iunlockput Dirlookup Iput.
