(* SpecIget.v -- the public interface of iget(), stated over the REAL inode
   cache and no longer assumed.

     static struct inode* iget(uint dev, uint inum) {
       struct inode *ip, *empty;
       acquire(&itable.lock);
       empty = 0;
       for(ip = &itable.inode[0]; ip < &itable.inode[NINODE]; ip++){
         if(ip->ref > 0 && ip->dev == dev && ip->inum == inum){
           ip->ref++;
           release(&itable.lock);
           return ip;
         }
         if(empty == 0 && ip->ref == 0)
           empty = ip;
       }
       if(empty == 0) panic("iget: no inodes");
       ip = empty;
       ip->dev = dev;  ip->inum = inum;  ip->ref = 1;  ip->valid = 0;
       release(&itable.lock);
       return ip;
     }

   @ KernelSyms.iget, 170 bytes: a 64-byte frame around one acquire, a
   do-while scan of the fifty entries, and TWO exits that each release and
   return the entry -- the cache HIT (+0x56/+0x58, [ref++]) and the RECYCLE
   (+0x6e/+0x72/+0x78/+0x7c, the four identity/ref/valid stores).  The scan
   is the loop [IcacheRef.ientry_step] and [ientry_sentinel] describe: the
   cursor steps by [ISLOTSZ] and stops at [KernelSyms.log], which IS
   [ientry NINODE].

   ---- WHAT IT TAKES, AND WHY THERE IS NO REFERENCE AMONG IT -------------

   iget is the function that MINTS references, so unlike idup / ilock /
   iput it takes none.  What it takes instead is:

   [is_itable2] -- the itable spinlock over the v2 resource.  Everything
   iget touches beyond the [ref] words lives there: the identity cells
   (through [islot2]), the pure slot->inum map [ci] and the uncached POOL.

   [itable_inv] -- where the [ref] WORDS live (design §4).  The scan's
   [c.lw a5,8(s1)] at +0x44 reads one per iteration and the two writes
   (+0x58 and +0x78) open it; holding the lock's half of the authority
   across each read-modify-write is what makes it atomic in the proof.

   [ic_escrows] -- EVERY entry's escrow, not one.  ilock and iunlock are
   handed the slot they are to work on and name its escrow; iget's scan
   walks all fifty and cannot know in advance which it will stop at, so its
   contract takes the whole persistent family.

   ONE [iref_slot], and it is spent on BOTH arms.  The hit arm's [ref++] is
   an unconditional increment and cannot re-establish "the count is still an
   int" on its own ([IrefSlots.v]'s header); the recycle arm's [ref = 1]
   parks the unit that accounts for the reference it mints.  Exactly
   filedup's and idup's discipline: it is the caller's job to bring one.

   NO reference.  [ireg_inv] IS taken, and the "no [ireg_inv]" clause this
   paragraph used to carry is AMENDED (iclaim-ledger.md §3.3's contract-set
   widening, executed in increment IIIe): iget still never READS a dinode
   -- the region open is GHOST-ONLY, on the ledger's [icnt] and freeze
   columns and nothing else.  Two sites need it and both are on the recycle
   arm:

     - the pool peel ([IcacheEscrow.ipool_shape_to_np]) opens the region to
       refute the AWAIT arm's standing freeze from the caller's LICENCE
       (§3.1's A-refuter: the old [ipool_await_refuter] wand into [False] is
       unbuildable out of a fupd, so the refutation moved INSIDE the peel's
       own fupd, where it needs [ireg_inv] and the [iname] this contract
       already takes);
     - the 0 -> 1 count move ([IcacheInv.iref_alloc_store_au]) has to carry
       the peeled [icnt_half] from 0 to 1, and the region owns the other
       half of that column.

   The inum's pool bundle still moves through the recycle arm as an opaque
   the pool row ([IcacheEscrow], §13.3) -- extracted from the pool and
   parked in the entry's escrow for whoever ilocks it next -- and iget never
   looks inside it.  The bundle's payload is untouched here; only its two
   ghost columns move.

   ---- THE ONE PREMISE A READER SHOULD LOOK AT TWICE --------------------

   [bv_unsigned inum < 16 * Z.of_nat nib] is the only constraint on the
   arguments, and it is NOT about the scan: it is what puts the requested
   inum in [IcacheEscrow.region_inums], which is what lets the recycle arm
   take its bundle out of the pool ([ipool_acc]).  The scan's own loop
   invariant -- no slot in the range already scanned carries (dev, inum) --
   is what shows the inum is not among the CACHED ones, and the two together
   are the pool membership fact.

   ...EXCEPT THAT THE SCAN'S INVARIANT IS PAIR-SHAPED AND THE POOL IS NOT
   (§13.11).  xv6's hit test is [ip->dev == dev && ip->inum == inum], and
   the dev compare at +0x4c short-circuits to the loop step BEFORE
   [ip->inum] is ever loaded, so a scan that misses proves only that no live
   slot carries THE PAIR -- while the pool, the region and [dinode_at] are
   keyed on the inum ALONE (one file system).  A live slot at (dev', inum)
   would leave the recycle with no bundle to withdraw, a second [dinode_at]
   for one inum against [InodeRegion.dinode_at_excl], and [ci]-injectivity
   broken.  The two readings coincide exactly when the cache holds ONE
   device, which is now said out loud: [is_itable2] carries the table's
   device and is instantiated HERE at iget's own [dev].  So there is still
   no separate premise on [dev] -- the argument simply IS the table's
   device, the way [dev] is [BioInv.bv_dev V] on the buffer side -- and iget
   writes it into the recycled entry as before, with only ilock's later
   bread caring what it means.

   ---- THE POSTCONDITION IS UNIFORM ACROSS THE TWO ARMS -----------------

   [∃ k q, a0 = ientry k ∧ k < NINODE, and ONE reference to slot k at the
   caller's dev and inum].  A hit mints [q] out of the share the table
   retained ([IcacheInv.iref_incr_store_au], §13.1b -- the incrementer holds
   no token of its own, so [iref_dup_step]'s split cannot serve); a recycle
   mints the first reference of a fresh entry ([iref_alloc_step] at a
   fraction at most 1/2, because the escrow owns the other half of both
   identity cells forever, §13.1e).  Which of the two happened is invisible
   to the caller, and must be: xv6's whole point is that a second [iget] of
   a cached inode is indistinguishable from the first.

   Note the WIDTHS.  The reference is at the 32-bit [dev] / [inum] the
   identity cells hold; the returned register carries the 64-bit entry
   ADDRESS, and [IcacheRef.ientry_inj] is what makes the two views the same
   thing.  The arguments arrive sign-extended, which is forced by the code:
   the scan's compares at +0x4c / +0x52 are 64-bit [bne]s against registers
   holding the [c.lw] of a cell.

   ---- THE "iget: no inodes" PANIC IS LIVE ------------------------------

   The second panic arm in this tree to be taken rather than refuted
   ([SpecIlock.v]'s "ilock: no type" is the first, and its header explains
   the pattern).  A full table is a real state -- fifty entries all with
   [ref > 0] and none of them this inode -- and no premise a caller could
   state would rule it out, because whether the table is full is a fact
   about every OTHER process's open files.  So on that arm iget diverges
   through [SpecPanic]'s own contract and this postcondition speaks only for
   the calls that return.  That is sound in a partial-correctness WP and it
   is the honest statement; the proof file says at which instruction (+0x6a,
   [beq s3,zero]) it is taken.

   ---- THE SIE BOOKKEEPING ----------------------------------------------

   [SpecIdup.v]'s, for the same reason and with the same derivation: iget
   takes no sleeplock and never sleeps, its whole body runs inside one
   fully-nested acquire/release, and [n], [eb] and the SIE index [b]
   therefore come back exactly as they went in.  It is NOT the
   running-process bundle ilock threads -- nothing here can park.

   ---- THE LICENCE (increment C'-lite, fs-fragments.md §7.1) ------------

   iget is where a REFERENCE is minted for an inum that came off a disk
   block, and nothing in the scan can say the inum names a live inode.
   §20.17.5 answered that with a paragraph -- the enumeration of the six
   reasons a caller believes its inum -- and [IgetLic.v] makes it a type:
   one binder [l : ilic] and one premise [iname γi fsc_fs inodestart inum l].  The user's
   invariant ("the kernel will never invoke iget on inode numbers in
   directories in a disconnected subtree") is not statable about the
   machine's traces; it IS statable here, at DELIVERY, and that is why the
   enumeration lives on THIS contract and not on a payload.

   BORROWED AND RETURNED, AT THE SAME [l] (§7.1.2).  The licence comes back
   in the postcondition, unspent and at the SAME constructor.  Both halves
   are load-bearing.  Returning it is what keeps this increment
   caller-side: the borrow lives inside one call, so no syscall-level
   contract sees it and [SpecNamex] / [SpecCreate] / [SpecSysLink] /
   [SpecIalloc] / [SpecIlock] / [SpecIput] / [SpecIupdate] are all
   byte-identical.  Returning it at the SAME [l] -- rather than at a [∃ l']
   -- is what keeps the audit a grep: a [∃ l'] post is equally sound and
   silently permits a licence swap, which would destroy the per-site
   documentation the increment exists for.

   iget SPENDS IT ON NOTHING.  The proof frames it across the whole
   function and hands it back on the two returning arms; the diverging
   panic arm drops it.  That is the honest shape -- iget never reads a
   dinode, so there is nothing here that COULD consume a licence, and
   §7.1.6's death certificate says so: the licence is returned at the iget,
   [iput] holds none, and §20.7's ordering wall is untouched.           *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import LockRank.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IgetLic.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)

(* iget's own frame is 6 slots ([c.addi16sp sp,-48] at +0x00, with ra / s0 /
   s1 / s2 / s3 / s4 pushed at 40 / 32 / 24 / 16 / 8 / 0 and [c.addi4spn
   s0,sp,48] on top); acquire and release want 10 below that, and panic wants
   none.  [K_idup]'s budget for a frame half again as deep. *)
Notation K_iget := (58%nat) (only parsing).
Definition wp_iget_sconf_body
    `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (γi : gname)
    (inodestart : Z) (nib : nat)
    (dev inum : mword 32)
    (l : ilic)                                   (* THE LICENCE, §7.1 *)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iget in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_iget <= K)%nat ->
  (* [+3], not [+1]: iget's own [acquire] is one, and the LIVE panic arm
     fires INSIDE that critical section, where printk takes two more. *)
  (Z.of_nat n + 3 < 2 ^ 31)%Z ->
  (* the requested inum is inside the inode region: [ipool_acc]'s premise on
     the recycle arm, and the ONLY constraint on either argument *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* a0 = dev, a1 = inum, sign-extended -- the scan's 64-bit [bne]s at
     +0x4c / +0x52 compare them against the [c.lw] of a cell *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (sign_extend' 64 dev : mword 64) ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (sign_extend' 64 inum : mword 64) ->
  (* THE FRESHNESS PREMISE: iget acquires and releases [itable.lock]
     internally (balanced -- [lks] is unchanged across the whole call), so
     the caller must already hold only locks BELOW "itable"'s rank. *)
  locks_below lks "itable" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the itable spinlock: the identity cells, [ci] and the uncached pool *)
  is_itable2 γl fsc_ic fsc_fs γi fsc_cov fsc_logst nib dev -∗
  (* the [ref] words *)
  itable_inv -∗
  (* EVERY entry's content -- the scan cannot name its slot in advance *)
  ic_escrows fsc_ic fsc_fs γi fsc_cov fsc_logst -∗
  (* THE INODE REGION, and GHOST-ONLY (header, §3.3): the recycle arm's peel
     refutes a standing freeze from [l] inside it, and its 0 -> 1 count move
     carries the ledger's [icnt] half.  Persistent, so it costs a caller a
     frame and nothing else. *)
  ireg_reg γi fsc_fs inodestart nib -∗
  (* "iget: no inodes" IS REACHABLE -- see the header *)
  (* ...and it is an ORDINARY CALL: [kernel_data] mints the literal and this
     is the console bundle printk needs.  Note the arm fires while iget
     HOLDS itable.lock, which is why "itable" ranks below "pr". *)
  panic_env -∗
  (* THE precondition that makes the mint safe, on both arms *)
  iref_slot -∗
  (* THE LICENCE: borrowed here, returned below at the SAME [l].  It is
     indexed by the region's start because the [BufL] arm carries its own
     block tie (SIMP-1) -- the standalone block equation this contract used
     to state, and the [discriminate] it forced on every non-[BufL] caller,
     are both gone. *)
  iname γi fsc_fs inodestart inum l -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (k : nat) (q : Qp),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr
      /\ (k < NINODE)%nat
      /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ientry k ⌝ -∗
    (* ONE ROW (SIMP-2): the reference AND its provenance unit, packaged.
       The unit is minted here and FLAVOURED by the licence presented --
       ialloc's own [ClaimL] iget mints [runit_claim] into its own claim
       box, every other iget mints [runit_plain] -- and it rides with the
       reference for the reference's whole life, to be surrendered at the
       iput that closes it.  Since it never travels alone, it is no longer
       spelled alone: [inode_refb] is the pair, and it is the shape
       [inode_held] and both rest homes already wanted (ghost-simplification
       §5.1).  A caller that needs the halves gets them in one destruct. *)
    inode_refb (is_claim l) k q dev inum -∗
    (* ...and BACK, unspent and at the SAME [l] *)
    iname γi fsc_fs inodestart inum l -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IGET.
  Parameter wp_iget_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γl : gname) (γi : gname)
      (inodestart : Z) (nib : nat)
      (dev inum : mword 32)
      (l : ilic)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_iget_sconf_body γl γi inodestart nib dev inum l
                         m n eb p K b lks.
End IGET.
