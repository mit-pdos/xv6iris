(* LinkCreate.v -- the only file where create's proof meets its callees'.

   Seven functor arguments, every one of them a real proof:

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

   The fresh-type span across create's own [jal ialloc] / [ilock] is NOT a
   ninth argument: it is a stretch of create's own body rather than a
   callee, so [ProofCreate] applies [ProofCreateFreshTy.create_fresh_ty]
   directly.  Read that file's header for what the span is.

   panic is NOT a module here.  create's own panics are all inside callees
   (ialloc's no-inodes arm printks rather than panics, which is why the
   contract carries [printk_gen_contract] rather than a panic obligation);
   the [kernel_data] / [panic_env] the contract takes are threaded to the
   callees, whose own panic arms are discharged against [Panic].

   So this cone's assumption count is the five platform axioms plus
   funext, and nothing else. *)
Require Import LinkNameiparent LinkIlock LinkIunlockput LinkDirlookup
        LinkIalloc LinkIupdate LinkDirlink
        ProofCreate.

Module Create := CreateProof Nameiparent Ilock Iunlockput Dirlookup
                             Ialloc Iupdate Dirlink.
