(* LinkNparEra.v -- the NAMEIPARENT era trace walk's nine callees,
   discharged.

   [LinkNamexEra.v] verbatim, one module name changed: the same nine real
   proofs, none assumed, and no panic of namex's own.  Unlike the namei-side
   link file, ALL NINE are live here except two: [Myproc] and [Idup] are
   carried and never used, because this contract -- like the landed era one
   -- is ruled at absolute paths and the relative start is refuted from
   [pfun 0 = SLASH].  [Iunlock] (the [L_par] arm) and [Iput] (the
   nameiparent tail of [L_done]) are the two the namei-side file carried
   unused and this one actually calls.

   So this cone's assumption count stays at the five platform axioms plus
   funext. *)
Require Import LinkMyproc LinkIdup LinkIget LinkMemmove.
Require Import LinkIlock LinkIunlock LinkIunlockput LinkDirlookup LinkIput.
Require Import ProofNparEra.

Module NparEra := NparEraProof Myproc Idup Iget Memmove
                               Ilock Iunlock Iunlockput Dirlookup Iput.
