(* SpecIlock.v -- the public interface of ilock, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void ilock(struct inode *ip) {
       struct buf *bp;  struct dinode *dip;

       if (ip == 0 || ip->ref < 1) panic("ilock");
       acquiresleep(&ip->lock);
       if (ip->valid == 0) {
         bp  = bread(ip->dev, IBLOCK(ip->inum, sb));
         dip = (struct dinode * )bp->data + ip->inum % IPB;
         ip->type = dip->type;   ip->major = dip->major;
         ip->minor = dip->minor; ip->nlink = dip->nlink;
         ip->size  = dip->size;
         memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));
         brelse(bp);
         ip->valid = 1;
         if (ip->type == 0) panic("ilock: no type");
       }
     }

   174 bytes, 61 instructions.  iupdate is the FLUSH; this is the LOAD --
   same IBLOCK arithmetic, same [DinodeEnc] slot, [memmove] running the
   other way -- with a lock acquisition and a cached/uncached split on top.

   ---- WHAT IT PRODUCES ------------------------------------------------

   [InodeLock.inode_locked] -- exactly what readi, writei and iupdate
   consume: [inode_meta ip dn], [inode_map γfs ip bm], [inode_blocks], and
   the pure [inode_ok] (blkmap_wf, bm_covers at the size, di_addrs = the
   cells, type <> 0).  ilock is the only function that can mint those,
   which is why every fs.c caller is behind it.  ON BOTH ARMS: the cached
   arm hands back what the lock parked, the uncached arm reconstitutes it
   from the on-disk dinode, and the contract does not say which happened.

   ---- THE SEAM, AND THE ONE PREMISE THAT IS CONDITIONAL ---------------

   The icache itself is DEFERRED (claude-notes/design/fs-inode.md); ilock
   is stated over [InodeLock.inode_parked] and the [inode_key] shadow that
   names it.  The caller's half of that shadow is what pins the lock's
   [dn]/[bm] to the ones this contract talks about -- see InodeLock.v for
   why an existential will not do -- and it also carries [v], "has this
   inode ever been loaded".

   That [v] is what makes the on-disk agreement premise honest:

       v = false -> ds !!! islot inum = dn

   -- "if nobody has read this dinode yet, the block you are handing me
   holds it".  Unconditionally it would be FALSE for an inode with
   unflushed in-memory changes, and demanding it would make ilock unusable
   for exactly the inodes iupdate exists for.  It is the deferred inode
   table's obligation, and it is the only thing ilock cannot check.

   ---- BOTH PANICS ARE DEAD --------------------------------------------

   [ip == 0 || ip->ref < 1] by the premises [uint ip <> 0] and
   [0 < bv_unsigned refv < 2^31] -- a real inode with a live reference,
   which is what iget returns; the upper bound is the same in-range claim
   FileInv makes about struct file's count.  [ip->type == 0] by [inode_ok]'s type conjunct,
   carried across the load by the agreement premise above.  Both are
   REFUTED, not proved; precedent: log_write's two dead panics and bmap's
   out-of-range panic.

   ilock SLEEPS (acquiresleep, and bread inside the uncached arm), so it
   threads the full running-process bundle.  It enters and returns at
   noff 0.  ONE [bslot]: bread's reference, which brelse gives back. *)
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
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ilock's own frame is 32 bytes (4 slots) -- [c.addi sp,sp,-32] at +0x00,
   ra/s0/s1 pushed there and s2 pushed on the uncached arm only.  Its
   deepest callee is bread (40); acquiresleep wants 26, brelse 26,
   memmove 2. *)
Definition K_ilock : nat := 44%nat.

Definition wp_ilock_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !inodeG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (gfs : fs_names) (gi : gname)                      (* fs blocks + shadow  *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
    (ip : mword 64) (inum : mword 32) (refv : mword 32)
    (vv : bool) (dn : dinode) (bm : blkmap) (ds : list dinode)
    (pidv : mword 32) (dq dqd dqn dqr dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ilock in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ilock <= K)%nat ->
  (* the covered range's block-number bounds: bread's 2^31 arithmetic
     premise, and 0 is never a client block *)
  log_geom_ok cov logstart ->
  (* the superblock field is a real block number, so the [addw] that forms
     IBLOCK cannot wrap *)
  0 <= inodestart ->
  (* the inode's own block is a covered HOME block: bread's premise *)
  IBLOCK inum inodestart ∈ cov ->
  (* the block really IS sixteen well-formed dinodes *)
  diblk_wf ds ->
  (* THE DEFERRED INODE TABLE'S OBLIGATION, and the only thing ilock cannot
     check: an inode that has never been loaded is the one this block says
     it is.  Conditional on the shadow's [vv]; see the header. *)
  (vv = false -> ds !!! islot inum = dn) ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip, and it is a REAL inode with a LIVE reference: the two halves
     of the first panic's test *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  uint ip <> 0 ->
  0 < bv_unsigned refv < 2 ^ 31 ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- acquiresleep and
     bread both sleep, and a parking thread hands the trap CSRs across the
     crossing only with an enabled base.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  (* THE INODE'S SLEEPLOCK, over the parked resource, and the caller's half
     of the shadow that says which inode it is parking *)
  is_sleeplock gil gisl (i_lock ip) "inode"%string
               (inode_parked gfs gi cov logstart ip) -∗
  inode_key gi vv dn bm -∗
  (* ip->dev, ip->inum and ip->ref: read, never written -- FRACTIONS, so
     the caller (and the inode table, for ref) keep their own copies *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  i_ref ip ↦₄{dqr} refv -∗
  (* sb.inodestart, read once *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE INODE BLOCK, as sixteen pure dinodes.  Read, not written: it comes
     back at [ds].  Who owns it is deferred exactly as it is for iupdate. *)
  fsblock gfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
  (* the caller's own pid cell (acquiresleep records it in the lock) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ONE slot unit: bread's reference, which brelse gives back *)
  bslot bn -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      i_ref ip ↦₄{dqr} refv -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      fsblock gfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
      bslot bn -∗
      (* THE LOCK IS HELD ... *)
      sleeplocked gisl -∗
      sl_pid (i_lock ip) ↦₄ pidv -∗
      (* ... and the inode is LOADED, at the map and record the caller's
         shadow named.  Same conclusion on both arms. *)
      inode_locked gfs gi cov logstart ip dn bm -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ILOCK.
  Parameter wp_ilock_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !inodeG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32) (refv : mword 32)
      (vv : bool) (dn : dinode) (bm : blkmap) (ds : list dinode)
      (pidv : mword 32) (dq dqd dqn dqr dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_ilock_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi gil gisl
                          cov logstart inodestart dev ip inum refv
                          vv dn bm ds pidv dq dqd dqn dqr dqs m K eb C b.
End ILOCK.
