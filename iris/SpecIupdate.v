(* SpecIupdate.v -- the public interface of iupdate, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void iupdate(struct inode *ip) {
       struct buf *bp;
       struct dinode *dip;

       bp = bread(ip->dev, IBLOCK(ip->inum, sb));
       dip = (struct dinode * )bp->data + ip->inum % IPB;
       dip->type  = ip->type;
       dip->major = ip->major;
       dip->minor = ip->minor;
       dip->nlink = ip->nlink;
       dip->size  = ip->size;
       memmove(dip->addrs, ip->addrs, sizeof(ip->addrs));
       log_write(bp);
       brelse(bp);
     }

   126 bytes, 44 instructions, COMPLETELY STRAIGHT-LINE: no branches, no
   arms, no panic of its own.  It is the in-memory-inode -> logged-block
   flush, and its contract is correspondingly a single arm.

   THE CONTRACT (claude-notes/design/fs-inode.md, "iupdate -- the flush").
   Everything goes in and comes back out unchanged EXCEPT the inode block,
   which comes back at

     diblk_bytes (<[islot inum := dn]> ds)

   -- the same sixteen on-disk inodes with slot [inum mod IPB] replaced by
   the in-memory one.  [DinodeEnc.v] keeps the block in the IMAGE of
   [diblk_bytes] exactly so that this is one insert on a list of pure
   records and no byte list ever has to be exhibited.

   THE FIVE SCALARS AND THE THIRTEEN ADDRS COME FROM DIFFERENT RESOURCES.
   [inode_meta ip dn] owns ip->type/major/minor/nlink/size at [dn]'s scalar
   fields; ip->addrs[] is owned by [inode_map γfs ip bm] and NOT a second
   time by [inode_meta], so the premise [di_addrs dn = bm_cells bm] is what
   ties the record's addrs field to the cells memmove actually copies.  See
   the note on [InodeInv.inode_meta] for why the record rather than five
   loose scalars.

   THE BUDGET IS SPEND-EXACTLY: [log_op γ (S u)] in, [log_op γ u] out.
   iupdate is straight-line and ALWAYS executes its one log_write, so unlike
   bmap it can promise this.  bmap's spend-AT-MOST form is forced only where
   a path can skip the spend -- [log_op] has no mover outside the log
   spinlock, so a function that might not spend cannot burn a surplus.

   TWO SLOT UNITS, in and back out.  bread's reference is held across
   log_write, which wants one of its own; brelse returns it.

   NO [blk_own].  iupdate establishes no injectivity -- it installs no block
   number anywhere -- so it needs no exclusive token.  The inode block holds
   SIXTEEN different inodes' dinodes, and who owns it is deferred exactly as
   the bitmap is (design doc, "Who owns an inode block"): iupdate takes the
   whole block's [fsblock] half and hands it back updated at one slot, which
   is correct and does not prejudge the icache sharing design.

   THE SUPERBLOCK FIELD rides as a plain fractional cell, the way
   SpecInitlog.v takes [sb + 20] for logstart -- read once at +0x18 and
   handed straight back.  There is deliberately no superblock abstraction
   for one field.  Unlike initlog, [sb] is not an argument here: iupdate
   reads the GLOBAL, via [auipc a1,0x1d / lw a1,1850(a1)] resolving to
   [KernelSyms.sb + 0x18].

   iupdate SLEEPS (bread), so it threads the full running-process bundle
   exactly as SpecBmap.v / SpecBread.v do.  It enters and returns at
   noff 0. *)
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
Require Import DinodeEnc.
Require Import InodeInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* iupdate's own frame is 32 bytes (4 slots) -- [c.addi sp,sp,-32] at +0x00,
   ra/s0/s1/s2 pushed.  Its deepest callee is bread (40); brelse wants 26,
   log_write 18 and memmove 2. *)
Definition K_iupdate : nat := 44%nat.

(* [sb_inodestart] -- the [sb + 24] cell iupdate reads at +0x18 -- now
   lives in InodeInv.v, where ilock's contract can also name it. *)

Definition wp_iupdate_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (dn : dinode) (bm : blkmap) (ds : list dinode)
    (u : nat)
    (pidv : mword 32) (dq dqd dqn dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iupdate <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's own
     storage is covered *)
  log_geom_ok cov logstart ->
  (* the superblock field is a real block number, so the [addw] that forms
     IBLOCK cannot wrap: with [IBLOCK ... ∈ cov] this bounds the sum by
     2^31 (log_geom_ok's [cov_ok]) *)
  0 <= inodestart ->
  (* the inode's own block is a covered HOME block: bread's premise, and
     log_write's *)
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the block really IS sixteen well-formed dinodes *)
  diblk_wf ds ->
  (* ...and the record whose scalars [inode_meta] owns names exactly the
     thirteen addrs cells [inode_map] owns.  THE tie between the two
     resources; see the header. *)
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- bread sleeps, and a
     parking thread hands the trap CSRs across the crossing only with an
     enabled base.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* ip->dev and ip->inum: read, never written -- FRACTIONS, so the caller
     keeps its own copies *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  (* the five metadata cells, and the thirteen addrs cells *)
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  (* sb.inodestart, read once *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE INODE BLOCK, as sixteen pure dinodes *)
  fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  running_claim j -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE RESERVATION, SPEND-EXACTLY: the one log_write always runs *)
  log_op γ (S u) -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      running_claim j -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH: slot [inum mod IPB] now holds the in-memory inode *)
      fsblock γfs (IBLOCK inum inodestart)
              (diblk_bytes (<[islot inum := dn]> ds)) -∗
      bslots bn 2 -∗
      log_op γ u -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUPDATE.
  Parameter wp_iupdate_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn : dinode) (bm : blkmap) (ds : list dinode)
      (u : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iupdate_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                            cov logstart inodestart dev ip inum dn bm ds u
                            pidv dq dqd dqn dqs m K eb C b.
End IUPDATE.
