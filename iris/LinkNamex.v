(* LinkNamex.v -- the only file where namex's proof meets its nine callees'.
   Every one of them is a real proof and none of them is assumed:

   - myproc arrives through LinkMyproc.v (push_off / pop_off);
   - idup and iget arrive through LinkIdup.v / LinkIget.v (acquire /
     release on the itable spinlock);
   - memmove is LinkMemmove.v, a leaf;
   - ilock arrives through LinkIlock.v (acquiresleep / bread / memmove /
     brelse), iunlock through LinkIunlock.v and iunlockput through
     LinkIunlockput.v, which composes iunlock with iput;
   - dirlookup arrives through LinkDirlookup.v (readi / namecmp / iget),
     whose readi instance is the no-allocation one, so balloc's Axiom does
     NOT reach this cone;
   - iput arrives through LinkIput.v (itrunc / iupdate).

   panic is NOT a module here.  namex has no panic of its own: every panic
   in the cone belongs to a callee (ilock's "ilock: no type", iget's
   "iget: no inodes", dirlookup's "dirlookup not DIR" -- which namex's own
   [lh a5,68(s4)] / [bne a5,s7] test refutes for it -- and dirlookup's
   granularity arm), so the [panic_wp_any] resource the contract takes is
   threaded to the callees and never consumed locally.

   So this cone's assumption count stays at the five platform axioms plus
   funext. *)
Require Import LinkMyproc LinkIdup LinkIget LinkMemmove.
Require Import LinkIlock LinkIunlock LinkIunlockput LinkDirlookup LinkIput.
Require Import ProofNamex.

Module Namex := NamexProof Myproc Idup Iget Memmove
                           Ilock Iunlock Iunlockput Dirlookup Iput.
