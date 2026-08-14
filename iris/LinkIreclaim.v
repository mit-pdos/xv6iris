(* LinkIreclaim.v -- the only file where ireclaim's proof meets its callees'.
   All eight (bread, brelse, iget, begin_op, ilock, iunlock, iput and end_op)
   are PROVEN, so nothing here is assumed:

   - bread / brelse arrive through their own Link files, the same instances
     ialloc, iupdate and balloc use;
   - iget arrives through LinkIget.v (acquire / release), i.e. the same
     instance dirlookup's tail call and ialloc's claim arm use;
   - begin_op / end_op arrive through LinkBeginOp.v / LinkEndOp.v, the pair
     kexit's cwd release already drives;
   - ilock / iunlock / iput arrive through their own Link files.

   ireclaim's TWO dead arms are refuted inside the proof, so no panic
   contract is instantiated here:

   - the [bgeu a5,a4] at +0x0a -- the empty-region exit, which would return
     through the SECOND [c.jr ra] at +0xc6 with the frame NEVER pushed -- is
     refuted from the contract's [1 < ninodes], exactly as ialloc's +0x12 arm
     and balloc's [beqz a5] at the same offset are;
   - the [beq s3,zero] at +0x50 -- the C source's [if(ip)] -- is refuted from
     iget's POSTCONDITION ([a0 = ientry k] with [k < NINODE], hence
     [IcacheRef.ientry_ne_zero]) and NOT from any premise of this contract.
     That is the one refutation in this cone that a caller cannot see.

   The [panic_wp_any] resource the contract takes is threaded to all eight
   callees and never consumed locally.

   *** READ THIS BEFORE TRUSTING "THE STANDING SIX". ***  ireclaim's orphan
   arm calls printk on its GENERAL path -- and, unlike balloc's and ialloc's
   messages, with a [%d] conversion -- and [PRINTK_GEN]'s only instance is
   [LinkPrintk]'s own [Axiom].  Instantiating that functor -- here or in
   [ProofIreclaim.v] -- would put a SEVENTH entry in [Print Assumptions
   Ireclaim.wp_ireclaim_sconf].  [SpecIreclaim.v] therefore takes printk's
   contract as a PURE HYPOTHESIS ([SpecPrintk.printk_gen_contract]), which
   keeps the count at the standing six -- but that is NOT self-containment:
   ireclaim's six are modulo a THREADED printk obligation that its callers
   (fsinit, and the boot client above it) must eventually discharge, exactly
   the standing that [SpecPanic.panic_wp_any] already has throughout this
   tree.  This is SpecBalloc.v's / LinkIalloc.v's arrangement verbatim; a
   reader who takes the six for "depends on nothing else" is misreading it. *)
Require Import LinkBread LinkBrelse LinkIget LinkBeginOp
                LinkIlock LinkIunlock LinkIput LinkEndOp
                ProofIreclaim.

Module Ireclaim := IreclaimProof Bread Brelse Iget BeginOp
                                 Ilock Iunlock Iput EndOp.
