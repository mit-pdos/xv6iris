(* LinkFsinit.v -- the only file where fsinit's proof meets its callees'.
   THE LAST LINK OF fs.c: with this module, all twenty-four of fs.c's
   functions are PROVEN AND LINKED.

   All five callees are proven, so nothing here is assumed:

   - bread / brelse arrive through their own Link files, the same instances
     balloc, ialloc, iupdate and ireclaim use;
   - memmove arrives through LinkMemmove.v -- the same leaf instance ilock,
     iupdate, install_trans, end_op, copyin and copyout drive;
   - initlog arrives through LinkInitlog.v (initlock / bread / brelse /
     install_trans / write_head, sealed inside it);
   - ireclaim arrives through LinkIreclaim.v (bread / brelse / iget /
     begin_op / ilock / iunlock / iput / end_op, sealed inside it).

   fsinit's ONE dead arm is refuted inside the proof, so no panic contract is
   instantiated here:

   - the [bne a4,a5] at +0x40 -- the C source's
     [if(sb.magic != FSMAGIC) panic("invalid file system")], which is a REAL
     panic and not one of the [printk] arms balloc and ialloc have -- is
     refuted from the contract's [bv_unsigned v_magic = FSMAGIC], an IMAGE
     premise about the 32 bytes mkfs wrote into block 1.  That is the whole
     reason SpecFsinit.v states its geometry as claims about [sb_image].

   The [panic_wp_any] resource the contract takes is threaded to all five
   callees and never consumed locally.

   *** READ THIS BEFORE TRUSTING "THE STANDING SIX". ***  ireclaim's orphan
   arm calls printk on its general path (with a [%d]), and [PRINTK_GEN]'s only
   instance is [LinkPrintkGen]'s own [Axiom].  SpecIreclaim.v therefore takes
   printk's contract as a PURE HYPOTHESIS ([SpecPrintkGen.printk_gen_contract])
   and SpecFsinit.v threads that same hypothesis down to it -- so the
   obligation is now TWO deep, and the boot client above fsinit (forkret /
   main) is where it finally has to be discharged, or accepted as
   [SpecPanic.panic_wp_any] already is.  [Print Assumptions
   Fsinit.wp_fsinit_sconf] therefore stays at the standing six -- the five
   platform axioms plus funext -- but the six are MODULO that threaded printk
   obligation and modulo [panic_wp_any].  This is SpecBalloc.v's /
   LinkIalloc.v's / LinkIreclaim.v's arrangement verbatim; a reader who takes
   the six for "depends on nothing else" is misreading it.

   THE BOOT CLIENT'S SIDE OF THE BARGAIN, in one place: fsinit needs
   [bslots bn 35] ((LOGBLOCKS + 2) + 2 + 1), the raw 32 bytes of .bss at
   [&sb], block 1's client half at the mkfs image, initlog's whole raw
   [struct log] bundle and FsBlocks material, the icache's four persistent
   things out of [IcacheBoot.icache_boot], and the image premises SpecFsinit.v
   names.  It gets back the eight typed superblock cells, the log context and
   [bslots bn 3]. *)
Require Import LinkBread LinkMemmove LinkBrelse LinkInitlog LinkIreclaim
                ProofFsinit.

Module Fsinit := FsinitProof Bread Memmove Brelse Initlog Ireclaim.
