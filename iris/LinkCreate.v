(* LinkCreate.v -- the only file where create's proof meets its callees'.

   Eight functor arguments, seven of them real proofs:

   - nameiparent arrives through LinkNameiparent.v (namex, and under it
     dirlookup / iget / iput / ilock / iunlock);
   - ilock arrives through LinkIlock.v (acquiresleep / bread / memmove /
     brelse);
   - iunlockput arrives through LinkIunlockput.v (iunlock / iput), and it
     is create's ONLY route to itrunc -- the fail arm frees the inode it
     just allocated;
   - dirlookup arrives through LinkDirlookup.v (readi / namecmp / iget);
   - ialloc arrives through LinkIalloc.v (bread / log_write / brelse /
     memset / iget);
   - iupdate arrives through LinkIupdate.v (bread / memmove / log_write /
     brelse);
   - dirlink arrives through LinkDirlink.v, whose writei CAN allocate --
     balloc is itself proven (LinkBalloc.v), so nothing new is assumed.

   The eighth is [CreateFreshTy], and it is the one ASSUMPTION in this
   cone: [LinkCreateFreshTy.v]'s [Axiom create_fresh_ty], the four-instruction
   span across create's own [jal ialloc] / [ilock].  Read that file's header
   and [SpecCreateFreshTy.v]'s before this one.

   panic is NOT a module here.  create's own panics are all inside callees
   (ialloc's no-inodes arm printks rather than panics, which is why the
   contract carries [printk_gen_contract] rather than a panic obligation);
   the [kernel_data] / [panic_env] the contract takes are threaded to the
   callees, whose own panic arms are discharged against [Panic].

   So this cone's assumption count is the five platform axioms plus funext,
   plus [create_fresh_ty], plus the TRANSIENT [iput_acquiresleep_order_
   ADMITTED] that iput carries in from upstream. *)
Require Import LinkNameiparent LinkIlock LinkIunlockput LinkDirlookup
        LinkIalloc LinkIupdate LinkDirlink LinkCreateFreshTy
        ProofCreate.

Module Create := CreateProof Nameiparent Ilock Iunlockput Dirlookup
                             Ialloc Iupdate Dirlink CreateFreshTy.
