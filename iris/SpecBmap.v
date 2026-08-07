(* SpecBmap.v -- the public interface of bmap, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static uint bmap(struct inode *ip, uint bn) {
       uint addr, *a;
       struct buf *bp;
       if(bn < NDIRECT){
         if((addr = ip->addrs[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[bn] = addr;
         }
         return addr;
       }
       bn -= NDIRECT;
       if(bn < NINDIRECT){
         if((addr = ip->addrs[NDIRECT]) == 0){
           addr = balloc(ip->dev);
           if(addr == 0) return 0;
           ip->addrs[NDIRECT] = addr;
         }
         bp = bread(ip->dev, addr);
         a = (uint * ) bp->data;
         if((addr = a[bn]) == 0){
           addr = balloc(ip->dev);
           if(addr){ a[bn] = addr; log_write(bp); }
         }
         brelse(bp);
         return addr;
       }
       panic("bmap: out of range");
     }

   THE CONTRACT (claude-notes/design/fs-inode.md, "bmap's contract").
   One existential map bm' and the returned block, in two arms:

   - a0 = 0 -- allocation failed, and [blkmap_get bm' bn = 0].  Note that
     bm' is NOT claimed equal to bm: the indirect-path failure can already
     have allocated and installed the INDIRECT block before failing on the
     data block, so "the map is unchanged" would simply be false there.
     What both arms do promise is that bm' agrees with bm at every file
     index except possibly bn.
   - a0 = r <> 0 -- [blkmap_get bm' bn = r].

   Both arms return [inode_map γfs ip bm'] and [blkmap_wf cov logstart bm'].
   The fresh data block is DEPOSITED, not returned: bmap takes the
   caller's [inode_blocks] bundle and gives it back with the freshly
   allocated block in it, so nothing here is asymmetric between the two
   arms (design doc, "Why the fresh block is deposited, not returned").
   The bundles are ALSO what carry the per-block exclusive [blk_own]
   tokens, and those are the only thing that can re-establish
   [blkmap_wf]'s injectivity when balloc's block is installed --
   [fsblock] is a half element, so two at one key are consistent.

   THE BUDGET IS SPEND-AT-MOST, not spend-exactly: [log_op γ n] in with
   (5 <= n), and [log_op γ n'] out with (n - 5 <= n' <= n).  bmap cannot
   promise to have spent five, because it has no way to BURN a surplus --
   [log_op] moves only through the ledger authority inside log.lock, which
   bmap never takes -- and on the direct-hit path it does no balloc and no
   log_write at all.  See the clause itself for why the premise is a lower
   bound on the caller's counter rather than a (5 + u) shape.

   THE PANIC ARM IS DEAD.  bmap's [panic("bmap: out of range")] at +0xb2
   is reached only when bn - NDIRECT >= NINDIRECT, which the premise
   (bn < MAXFILE) rules out -- the same way both of log_write's panics are
   dead.  [panic_wp_any] is still threaded, because the interior
   acquire's own holding-check arm wants a panic contract regardless.

   THE s4 QUIRK.  gcc saves s4 only on the paths that reach bread
   ([c.sdsp s4,0(sp)] at +0x058 / +0x060 / +0x0b2) and restores it once at
   +0x088; the direct path jumps straight to the shared epilogue at +0x08a
   and never touches it.  So [callee_saved] is established per-arm rather
   than once at the epilogue -- the join at +0x08a is reached with s4
   either restored or never written.  That is a fact about bmap's PROOF;
   the contract below just says [callee_saved m mf].

   THE BITMAP RIDES THROUGH, because balloc's does.  bmap takes the two
   superblock cells and [BitmapInv.bitmap_res] and hands them back; the
   returned bitmap is at an EXISTENTIAL [used'] with [used ⊆ used'],
   because bmap may allocate twice (the indirect block and the data block)
   and a caller has no use for the exact set -- only for the fact that the
   allocator never un-marks a block.  Who owns the bitmap between calls is
   deliberately still open (claude-notes/design/fs-bitmap.md, "Who owns
   bitmap_res between calls"); it is passed in and returned updated, as
   [inode_map] is.

   [BMAP_NOALLOC] below is UNCHANGED by this: with all three allocation
   sites dead there is no balloc, hence no bitmap and no superblock cell.

   bmap SLEEPS (bread, and balloc), so it threads the full running-process
   bundle exactly as SpecBread.v does.  It enters and returns at noff 0. *)
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
Require Import SpecPanic.
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
Require Import InodeInv.
Require Import BitmapEnc BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintkGen.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* bmap's own frame is 48 bytes (6 slots) -- [c.addi16sp sp,-48] at +0x00
   (s4 rides in the same frame, at slot 0, on the indirect paths).  Its
   deepest callee is balloc (50); bread wants 40 and log_write 18. *)
Definition K_bmap : nat := 56%nat.

Definition wp_bmap_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
    (used : gset Z) (γpr : gname)
    (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
    (n : nat)
    (pidv : mword 32) (dq dqd dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bmap in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the uint bn argument, as the 32-bit word the ABI passes *)
  let bnw : mword 32 := mword_of_int (Z.of_nat fbn) in
  (K_bmap <= K)%nat ->
  (* enough budget for the worst case: balloc(indirect) 2 + balloc(data) 2
     + bmap's own log_write 1 *)
  (5 <= n)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's
     own storage is covered *)
  log_geom_ok cov logstart ->
  (* the bitmap's geometry, forwarded verbatim to balloc *)
  bitmap_geom_ok cov logstart bmapstart size ->
  (* balloc's out-of-blocks arm calls the GENERAL printk path; its contract
     rides as a hypothesis, never a functor, so that neither balloc nor bmap
     inherits LinkPrintkGen's Axiom.  See SpecBalloc.v's header. *)
  printk_gen_contract γpr γu γd ->
  (* KILLS THE PANIC ARM *)
  (fbn < MAXFILE)%nat ->
  blkmap_wf cov logstart bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip; a1 = bn, sign-extended as the RV64 ABI passes a uint *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bnw ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- everything below
     sleeps, and a parking thread hands the trap CSRs across the crossing
     only with an enabled base.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the two PERSISTENT printk credentials, forwarded to balloc *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* ip->dev, read (never written) on all four balloc/bread call paths --
     a FRACTION, so the caller keeps its own copy *)
  i_dev ip ↦₄{dqd} dev -∗
  (* THE BLOCK MAP, and THE FILE'S DATA BLOCKS.  Both, because balloc hands
     the freshly allocated DATA block's [fsblock] half (and its exclusive
     [blk_own] token) to bmap and there is nowhere else to put them: the
     design doc's "the fresh half is deposited into the bundle" is exactly
     this, and a bmap that returned only [inode_map] would strand the block
     it just allocated.  The tokens inside the two bundles are also what
     re-establish [blkmap_wf]'s injectivity at an insertion
     ([InodeInv.inode_fresh]). *)
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the two superblock fields and the bitmap, all three for balloc's sake *)
  sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* the running-thread bundle *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units: bmap's own bread of the indirect block holds one
     across the interior balloc (which needs two of its own) and across
     log_write; brelse hands it back at the end. *)
  bslots bn 3 -∗
  (* THE RESERVATION, as a SPEND-AT-MOST clause.  bmap costs at most five
     units -- two per balloc x 2, plus its own log_write -- but it cannot
     hand back a surplus: [log_op] moves only through [LogInv.log_spend_step]
     against the ledger authority inside log.lock, and bmap never takes that
     lock.  So the direct-hit path returns the reservation untouched and the
     failure paths return whatever balloc refunded.  Stating a lower bound
     [n - 5 <= n'] rather than an exact [n - 5] is what makes that sound;
     the upper bound [n' <= n] is free and stops the contract from being
     satisfiable by a bmap that MINTS budget.  The premise is a lower bound
     on the caller's own counter rather than a [5 + u] shape, so a writei
     loop can present its counter directly and re-present what comes back. *)
  log_op γ n -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (bm' : blkmap) (n' : nat) (data' : nat -> list (bv 8))
    (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      (* THE ALLOCATOR NEVER UN-MARKS: [used] only grows.  The exact set is
         existential because bmap may allocate twice. *)
      ⌜used ⊆ used'⌝ -∗
      ⌜blkmap_wf cov logstart bm'⌝ -∗
      (* bm' agrees with bm at every file index except possibly bn *)
      ⌜forall i : nat, (i < MAXFILE)%nat -> i <> fbn ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      (* ...and bmap NEVER UN-ALLOCATES: an index that already named a
         block still names the same one.  Together with the zero side
         condition on the deposit below this is what lets a caller carry
         "the blocks I did not write are the blocks that were there" across
         the call -- writei is the first consumer that needs it, and
         without it the contract permits a bmap that drops a mapping. *)
      ⌜forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
         blkmap_get bm' i = blkmap_get bm i⌝ -∗
      (* the two arms, on the returned a0 *)
      ⌜(mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)
        /\ bv_unsigned (blkmap_get bm' fbn) = 0)
       \/ (mf !!! Regidx (mword_of_int 10 : mword 5)
             = sign_extend' 64 (blkmap_get bm' fbn : mword 32)
           /\ bv_unsigned (blkmap_get bm' fbn) <> 0)⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_map γfs ip bm' -∗
      (* THE DEPOSIT.  [data'] is [data] except that a freshly allocated
         data block for [fbn] arrives all-zero.  A caller reads WHETHER an
         allocation happened off the MAP (the arm disjunction above and
         [blkmap_get bm' fbn]), never off [data'] -- which is why one
         disjunction, and not a case split coupled to the arms, is the
         right shape here; [InodeInv.inode_blocks_insert] and
         [inode_blocks_frame] are the two lemmas that produce the two
         disjuncts.

         THE ZERO SIDE CONDITION ON THE SECOND DISJUNCT is what makes this
         clause usable by writei.  Without it the contract permits a bmap
         that OVERWRITES an already-allocated block with zeroes, and then no
         caller can carry "the bytes outside the range I wrote are the bytes
         that were there before" across the call -- which is writei's whole
         postcondition.  It costs nothing: the deposit branch of bmap's proof
         runs exactly where [inode_blocks_insert]'s own
         [bv_unsigned (blkmap_get bm fbn) = 0] premise is already discharged. *)
      ⌜data' = data
       \/ (bv_unsigned (blkmap_get bm fbn) = 0
           /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)⌝ -∗
      inode_blocks γfs bm' data' -∗
      bslots bn 3 -∗
      (* at most five units gone, and none gained *)
      ⌜((n - 5)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BMAP.
  Parameter wp_bmap_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (γpr : gname)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (n : nat)
      (pidv : mword 32) (dq dqd dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_bmap_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart bmapstart size dev used γpr ip bm data fbn n
                         pidv dq dqd dqb dqs m K eb C b.
End BMAP.

(* ===================================================================== *)
(*  bmap FOR A CALLER THAT CANNOT ALLOCATE                                *)
(* ===================================================================== *)

(* readi calls bmap, and bmap allocates when the slot is zero -- which calls
   log_write.  But fileread does NOT wrap readi in a transaction, so an
   allocating read would hit panic("log_write outside of trans").  It never
   happens because every block below a file's size is allocated
   ([InodeInv.bm_covers] is that statement), and under the single premise

       bv_unsigned (blkmap_get bm fbn) <> 0

   ALL THREE of bmap's allocation sites are dead:

   - the direct slot test at +0x26 and the indirect ENTRY test at +0x80 are
     decided by the premise itself;
   - the indirect-BLOCK test at +0x4c is decided by the premise TOO, and
     that is why this contract needs no second hypothesis about bm_ind:
     [blkmap_wf]'s "no indirect block => no entries" conjunct read backwards
     ([InodeInv.blkmap_wf_ind_nz]) turns "the entry at an indirect index is
     nonzero" into "the indirect block exists".

   So the contract drops EVERYTHING the allocation arms needed:

   - no [log_op] and no budget premise -- bmap performs no [log_write], so
     there is no reservation to spend and none to hand back;
   - no [log_ctx], and hence no [γ : log_names] at all;
   - [bslot bn] rather than [bslots bn 3].  The three were bread's one held
     across balloc's two; with balloc dead only bread's own unit remains,
     and brelse returns it.

   ...and the postcondition is correspondingly exact rather than
   existential: the map and the file's data come back UNCHANGED, and a0 is
   [blkmap_get bm fbn].  It is the same 70 instructions and the same proof
   body as [BMAP] -- see ProofBmap.v's [BmapCore], which is parameterised
   by whether the allocation arms are live and is where BOTH contracts come
   from.  Precedent for two contracts over one function: SpecWalk.v's
   [WALK] / [WALK_NOALLOC]. *)
Definition wp_bmap_noalloc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
    (pidv : mword 32) (dq dqd : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bmap in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let bnw : mword 32 := mword_of_int (Z.of_nat fbn) in
  (K_bmap <= K)%nat ->
  log_geom_ok cov logstart ->
  (* KILLS THE PANIC ARM *)
  (fbn < MAXFILE)%nat ->
  blkmap_wf cov logstart bm ->
  (* THE NO-ALLOC PREMISE, and the only one this contract adds *)
  bv_unsigned (blkmap_get bm fbn) <> 0 ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sign_extend' 64 bnw ->
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  i_dev ip ↦₄{dqd} dev -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle: bmap still SLEEPS, in bread *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ONE slot unit: the interior bread's, handed back by brelse *)
  bslot bn -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      (* the block the map already named, and nothing else happened *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
         = sign_extend' 64 (blkmap_get bm fbn : mword 32)⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      inode_map γfs ip bm -∗
      inode_blocks γfs bm data -∗
      bslot bn -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BMAP_NOALLOC.
  Parameter wp_bmap_noalloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (fbn : nat)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_bmap_noalloc_sconf_body Φ γs j γl γu γd γk pd pav pu bn γfs
                                 cov logstart dev ip bm data fbn pidv dq dqd
                                 m K eb C b.
End BMAP_NOALLOC.
