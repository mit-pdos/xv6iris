(* SpecIreclaim.v -- the public interface of ireclaim, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-
   function proof file -- so every function proof can be checked in parallel.

     void ireclaim(int dev) {
       int inum;
       struct buf *bp;
       struct dinode *dip;
       struct inode *ip;

       for(inum = 1; inum < sb.ninodes; inum++){
         bp = bread(dev, IBLOCK(inum, sb));
         dip = (struct dinode * )bp->data + inum % IPB;
         if(dip->type != 0 && dip->nlink == 0){
           printf("ireclaim: orphaned inode %d\n", inum);
           ip = iget(dev, inum);
           brelse(bp);
           begin_op();
           ilock(ip);
           iunlock(ip);
           iput(ip);                  // nlink == 0, so this truncates+frees
           end_op();
         } else
           brelse(bp);
       }
     }

   200 bytes, an EIGHT-slot frame.  Registers, off CodeIreclaim.v:
   [s5 = dev], [s1 = inum], [s4 = &sb], [s6 = the format string],
   [s2 = bp], [s3 = inum sign-extended, then REUSED for ip].

   ---- THREE THINGS THE DECODE DOES THAT NO OTHER fs FUNCTION DOES ------

   (i) TWO RETURN SITES.  [c.jr ra] at +0xc4 (the real epilogue) and again at
   +0xc6.  The second one is reached from the [bgeu a5,a4] at +0x0a -- BEFORE
   the [c.addi16sp sp,-64] at +0x0e -- so it returns with THE FRAME NEVER
   PUSHED.  It is ialloc's +0x12 arm at a different offset and it is DEAD for
   the same reason: [1 < ninodes] refutes it (SpecIalloc.v's header, and
   SpecBalloc's [0 < size] before that).  So this contract has ONE live exit
   and, like ialloc's, a uniform epilogue.

   (ii) THE LOOP IS ENTERED IN THE MIDDLE.  [c.j +70] at +0x36 jumps past the
   STEP block (+0x6e..+0x7a) straight to the loop BODY at +0x7c.  An invariant
   stated at the body's top is therefore arrived at twice with different
   histories, and the first arrival is a special case -- the proof's business,
   but it is why the scan cannot be [ProofIalloc.ia_scan] verbatim.

   (iii) THE BUFFER IS HELD ACROSS iget.  [jal iget] at +0x44 runs while
   bread's reference from +0x8c is still outstanding; [jal brelse] at +0x4c
   only gives it back AFTERWARDS.  The slot accounting has to cover that, and
   [beq s3,zero] at +0x50 -- the C source's [if(ip)] -- is DEAD, refuted by
   iget's POSTCONDITION ([mr !!! a0 = ientry k]) and not by any premise of
   this contract.

   ---- WHAT ireclaim IS, AS A CONTRACT: THE UNION OF ITS CALLEES ---------

   ireclaim allocates no policy of its own.  Everything it does is a call, so
   its precondition is the union of nine proven ones -- bread, brelse, printk,
   iget, begin_op, ilock, iunlock, iput, end_op -- and its postcondition is
   "everything back".  It returns [void] and it is SINGLE-ARMED: both live
   paths through the loop body end at the same +0xc4.

   Three couplings inside that union are worth naming, because they are what
   make the union CLOSE rather than merely large:

   - THE LEDGER UNIT.  [iget] spends exactly one [iref_slot] and [iput]
     returns exactly one, so a single unit rides the whole scan and comes
     back at the end.  This is dirlookup's discipline; here the two halves
     are in the SAME function, which is why the contract is not two-armed.

   - THE LOG RESERVATION IS BORN AND DIES INSIDE.  [begin_op] mints
     [log_op γ MAXOPBLOCKS] and [end_op] retires it, so -- unlike ialloc,
     iupdate and iput -- NO [log_op] crosses this contract's boundary in
     either direction.  [iput_units = 3 <= MAXOPBLOCKS = 10] is what makes
     the reclaim arm affordable, and it is a closed numeric fact rather than
     a premise.

   - THE REFERENCE IS CARVED AND GATHERED.  [iget] pays out
     [inode_ref k q dev inum]; [ilock] wants an [inode_shr], which
     [IcacheRef.inode_ref_shed] carves off; [iunlock] gives the share back
     and [IcacheRef.inode_ref_gather] restores the reference, which [iput]
     then spends.  Nothing about that crosses the boundary either.

   So the only resources that genuinely FLOW are the bitmap (iput frees
   blocks, so [used] shrinks) and the buffer slots (returned).

   ---- THE ENTRY SLEEPLOCKS ARE A FAMILY, NOT A SINGLETON ---------------

   ilock, iunlock and iput each take [is_sleeplock] for THEIR OWN entry, and
   a caller that knows its slot hands over exactly one.  ireclaim does not
   know its slot: [iget] chooses it at run time and the scan cannot name it in
   advance.  So this contract takes [IcacheBoot.ic_sleeplocks cn] -- the fifty
   -fold persistent family, with [IcacheBoot.ic_sleeplocks_acc] to project the
   one the run picks.  That name is deliberate: N5a's ledger and IcacheBoot's
   own header both say new contracts should name THAT copy rather than
   [SpecFileclose.ic_sleeplocks] or [SpecDirlink.ic_sleeplocks], which are
   character-identical earlier copies kept only to spare their consumers a
   recompile.

   ---- THE BOOT MINT FITS THIS CONTRACT UNCHANGED (C7's flag, resolved) --

   fs-icache C7 flagged ireclaim as "the pool's initial-contents authority",
   i.e. the function that would have to say what the mkfs image's inodes
   contain.  Under fs-icache.md §16.5 it does not: the pool's FREE arm is
   just [imark], the boot mint is [IcacheBoot.icache_boot] and it already
   produces exactly the four persistent things this contract takes
   ([is_itable2], [itable_inv], [ic_escrows], plus the sleeplock family) at
   the ALL-EMPTY table.  ireclaim consumes them as premises and mints
   nothing.  The image-wf IOUs ([IcacheBoot.ipool_alloc]'s allocated-inum
   bundles, [InodeLock.inode_ok], [DirView.dir_ok]) stay where they are --
   sealed inside the pool by the boot client -- and this contract neither
   states nor discharges them.  NOTHING HAD TO MOVE.

   ---- WHAT IS *NOT* HERE, AND WHERE IT IS ------------------------------

   The superblock geometry premises ([1 < ninodes], [ninodes <= 16 * nib],
   [ninodes < 2^31], and inodestart's / bmapstart's coverage) are THREADED,
   exactly as SpecIalloc.v threads its three.  Their home is [SpecFsinit]:
   fsinit's [memmove] at +0x26 is where every superblock cell is born, so
   that is the only place they can be about anything.

   ireclaim SLEEPS (bread, and begin_op's two sleeps), so it threads the full
   running-process bundle exactly as SpecIalloc.v / SpecIput.v do, and takes
   the parking premise.  It enters and returns at noff 0.

   THE printk IS LIVE AND IT IS FORMATTED.  [auipc s6,0x4 / addi s6,s6,50] at
   +0x2e/+0x32 off [ireclaim = 0x80003408] puts the format string at
   0x80007470, and +0x38..+0x3c calls it with [a1 = s3 = inum], i.e. with a
   [%d] conversion -- where balloc's and ialloc's messages have none.  As in
   SpecBalloc.v / SpecIalloc.v the contract takes [γpr], the two PERSISTENT
   credentials [kernel_data] and [printk_env], and printk's contract as a
   PURE Prop HYPOTHESIS ([SpecPrintk.printk_gen_contract]) rather than as
   a functor argument.  See SpecBalloc.v's "READ THIS BEFORE TRUSTING THE
   STANDING SIX": carrying it as a hypothesis keeps [Print Assumptions] at the
   standing six, but the six are then modulo a THREADED printk obligation,
   exactly as [SpecPanic.panic_wp_any] is.                                 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* ireclaim's own frame is 64 bytes (8 slots) -- [c.addi16sp sp,-64] at +0x0e,
   with ra/s0/s1/s2/s3/s4/s5/s6 pushed at 56/48/40/32/24/16/8/0.  Its deepest
   callee is iput (60); end_op wants 58, ilock 44, bread 40, iunlock 26,
   begin_op 26, brelse 26, iget 16. *)
Definition K_ireclaim : nat := 68%nat.

Definition wp_ireclaim_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γpr : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z)
    (ninodes : Z) (nib : nat) (size : Z)
    (used : gset Z)
    (dev : mword 32)
    (pidv : mword 32) (dq dqb dqs dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ireclaim in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ireclaim <= K)%nat ->
  (* bread's / the log's block-number arithmetic, and the log's own storage *)
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  (* EVERY inum the region covers lives in a covered HOME block that is not
     log storage: bread's premise, ilock's and iput's.  The scan cannot know
     which inum it stops at, so the premise is the quantified one
     ([InodeInv.ireg_blocks_ok]) -- and it delivers BOTH conjuncts iput
     wants. *)
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ---- itrunc's geometry, threaded through iput verbatim ---- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  cov_below cov size ->
  (* ---- THE THREE GEOMETRY PREMISES -- SpecIalloc.v's, verbatim.
     [1 < ninodes] kills the [bgeu a5,a4] at +0x0a, the empty-region exit
     that returns through the SECOND [c.jr ra] at +0xc6 without ever having
     pushed a frame.  [ninodes <= 16 * nib] is the superblock-to-region tie
     that lets the scan's [sb.ninodes] bound feed iget's and ilock's
     [bv_unsigned inum < 16 * nib].  [ninodes < 2^31] is what makes the
     [lw]-then-[bgeu] comparison at +0x70..+0x78 numeric. ---- *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  (* THE ORPHAN ARM'S FIRST CALLEE, as a hypothesis and not a functor *)
  printk_gen_contract γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dev: the RV64 ABI's sign extension of an [int] *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (sign_extend' 64 dev : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- bread and
     begin_op both sleep *)
  eb = true ->
  (* ireclaim's cone is the union of its callees': bread/brelse ("bcache",
     4), printk ("pr", 14), iget/iput ("itable", 2), begin_op/end_op
     ("log", 3), ilock ("bcache", 4), iunlock ("sleep lock", 6) --
     "itable" is the lowest, so one premise there covers the whole cone
     via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the general printk path's two PERSISTENT credentials *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* end_op's crash seam and era certificate *)
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  (* the three superblock fields, read and handed straight back *)
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  (* THE INODE REGION -- persistent.  ireclaim never claims and never writes
     a dinode, so [DinodeSlot.diblk_slot_acc] is all its scan needs and
     [InodeRegion.ireg_claim_au] never appears. *)
  ireg_inv γi γfs inodestart nib -∗
  (* ---- THE ICACHE, as iget / ilock / iput take it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  (* THE FIFTY ENTRY SLEEPLOCKS, as a family: the scan does not know which
     slot iget will pick.  [IcacheBoot.ic_sleeplocks_acc] projects it. *)
  ic_sleeplocks cn -∗
  (* itrunc's bitmap, through iput *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* the caller's own pid cell (bread's / begin_op's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle and the disk fabric *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units: iput's indirect arm is what forces three.  The scan's
     own bread holds one of them ACROSS iget (+0x8c .. +0x4c), but that
     reference is given back before [begin_op] at +0x54, so the three never
     have to stretch to four. *)
  bslots bn 3 -∗
  (* ONE ledger unit: iget spends it at +0x44 and iput returns it at +0x66,
     every iteration.  It comes back. *)
  iref_slot -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 3 -∗
      iref_slot -∗
      (* THE ONLY THING THAT ACTUALLY MOVED: every orphan iput freed its
         file's blocks, so the bitmap's used set has SHRUNK.  Stated the way
         SpecIput.v states it -- a subset, not a description -- because a
         scan of unknown length cannot name the blocks it freed, and no
         caller needs them named.  fsinit, the only caller, threads it on. *)
      ⌜used' ⊆ used⌝ -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      (* ...and nothing else.  ireclaim returns void, no log reservation
         crosses the boundary (begin_op mints and end_op retires inside),
         and no inode reference survives (iget's is spent by iput). *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IRECLAIM.
  Parameter wp_ireclaim_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (ninodes : Z) (nib : nat) (size : Z)
      (used : gset Z)
      (dev : mword 32)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_ireclaim_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                             cov logstart bmapstart inodestart ninodes nib size
                             used dev pidv dq dqb dqs dqn m K eb b lks.
End IRECLAIM.
