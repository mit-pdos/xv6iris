(* LinkIalloc.v -- the only file where ialloc's proof meets its callees'.
   All five (bread, log_write, brelse, memset and iget) are PROVEN, so
   nothing here is assumed:

   - bread / log_write / brelse arrive through their own Link files, the
     same instances iupdate and balloc use;
   - memset is the WHOLE-FUNCTION spec [MemsetArray] (LinkMemsetArray),
     not the [MEMSET_PARTS] module [Memset] -- ialloc's [memset(dip,0,64)]
     is an arbitrary 64-byte fill, not a page;
   - iget arrives through LinkIget.v (acquire / release), i.e. the same
     instance dirlookup's tail call uses.

   ialloc's ONE dead arm -- the [bgeu a4,a5] at +0x12, the empty-region
   exit, refuted from the contract's [1 < ninodes] exactly as balloc's
   [beqz a5] at the same offset is refuted from [0 < size] -- is refuted
   inside the proof, so no panic contract is instantiated here.  The
   [panic_wp_any] resource the contract takes is threaded to bread,
   log_write, brelse and iget and never consumed locally.

   *** READ THIS BEFORE TRUSTING "THE STANDING SIX". ***  ialloc's
   no-inodes arm IS LIVE and calls printk on its GENERAL path, and
   [PRINTK_GEN]'s only instance is [LinkPrintkGen]'s own [Axiom].
   Instantiating that functor -- here or in [ProofIalloc.v] -- would put a
   SEVENTH entry in [Print Assumptions Ialloc.wp_ialloc_sconf].
   [SpecIalloc.v] therefore takes printk's contract as a PURE HYPOTHESIS
   ([SpecPrintkGen.printk_gen_contract]), which keeps the count at the
   standing six -- but that is NOT self-containment: ialloc's six are
   modulo a THREADED printk obligation that its callers must eventually
   discharge, exactly the standing that [SpecPanic.panic_wp_any] already
   has throughout this tree.  This is SpecBalloc.v's arrangement verbatim;
   a reader who takes the six for "depends on nothing else" is misreading
   it.                                                                    *)
Require Import LinkBread LinkLogWrite LinkBrelse LinkMemsetArray LinkIget
                ProofIalloc.

Module Ialloc := IallocProof Bread LogWrite Brelse MemsetArray Iget.
