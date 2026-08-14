(* LinkBalloc.v -- the only file where balloc's proof meets its callees'.
   All four (bread, log_write, brelse, memset -- the last two of which are
   what the INLINED bzero at +0x4c runs) are PROVEN, so nothing here is
   assumed: [ProofBalloc.v] replaced the [Axiom] this file used to carry,
   and it is the single file the bmap cone's one assumption lived in.

   balloc's two dead arms -- the [beqz a5,+0xf6] at +0x12 (refuted from
   [0 < size]) and the second outer iteration at +0x98 (refuted from
   [size <= BPB]) -- are refuted inside the proof, so no panic contract is
   instantiated here either.

   *** READ THIS BEFORE TRUSTING "THE STANDING SIX". ***  balloc's
   out-of-blocks arm IS LIVE and calls printk on its GENERAL path, and
   [PRINTK_GEN]'s only instance is [LinkPrintk]'s own [Axiom].
   Instantiating that functor -- here or in [ProofBalloc.v] -- would put a
   SEVENTH entry in [Print Assumptions Balloc.wp_balloc_sconf] and, through
   the ripple, in bmap's and writei's too.  [SpecBalloc.v] therefore takes
   printk's contract as a PURE HYPOTHESIS ([SpecPrintk.printk_gen_contract]),
   which keeps all three at the standing six -- but that is NOT
   self-containment: balloc's six are modulo a THREADED printk obligation
   that its callers must eventually discharge, exactly the standing that
   [SpecPanic.panic_wp_any] already has throughout this tree.  A reader who
   takes the six for "depends on nothing else" is misreading it.          *)
Require Import LinkBread LinkLogWrite LinkBrelse LinkMemsetArray ProofBalloc.

(* the whole-function memset spec [MEMSET] is [MemsetArray] (LinkMemsetArray),
   not the [MEMSET_PARTS] module [Memset] *)
Module Balloc := BallocProof Bread LogWrite Brelse MemsetArray.
