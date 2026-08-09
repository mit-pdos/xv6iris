(* SpecItrunc.v -- the public interface of itrunc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void itrunc(struct inode *ip) {
       int i, j;
       struct buf *bp;
       uint *a;

       for (i = 0; i < NDIRECT; i++) {
         if (ip->addrs[i]) {
           bfree(ip->dev, ip->addrs[i]);
           ip->addrs[i] = 0;
         }
       }

       if (ip->addrs[NDIRECT]) {
         bp = bread(ip->dev, ip->addrs[NDIRECT]);
         a = (uint * )bp->data;
         for (j = 0; j < NINDIRECT; j++) {
           if (a[j])
             bfree(ip->dev, a[j]);
         }
         brelse(bp);
         bfree(ip->dev, ip->addrs[NDIRECT]);
         ip->addrs[NDIRECT] = 0;
       }

       ip->size = 0;
       iupdate(ip);
     }

   148 bytes, 53 instructions.  Two loops -- twelve direct entries, then the
   256 entries of the indirect block, read through a bread/brelse pair --
   followed by the indirect block's own free, [ip->size = 0] and the flush.
   Note the compiler saves s4 CONDITIONALLY: [sd s4,0(sp)] sits at +0x50,
   inside the indirect arm, and is restored at +0x90, so the direct-only
   path never touches it.

   THE CONTRACT.  itrunc empties the inode: [inode_map] comes back at
   [InodeInv.bm_empty], every block the map named goes back to the free pool
   ([bitmap_res] loses exactly [bm_blocks bm]), the size is zeroed and the
   whole thing is flushed by the tail call to iupdate.  The postcondition is
   stated at the CLOSED value [bm_empty] rather than at "some map whose
   slots are all zero" so that iput -- the only caller -- needs no reasoning
   to see the inode names nothing.

   THE BUDGET IS THE INTERESTING PART, and it is why the log ledger had to
   change first.  itrunc calls bfree up to NDIRECT + NINDIRECT + 1 = 269
   times and then iupdate once.  Charging a unit per log_write -- the old
   always-consume accounting -- would demand 270 against a MAXOPBLOCKS of
   10, which no caller could supply.  But [FSSIZE = 2000 < BPB = 8192] means
   there is exactly ONE bitmap block, so all 269 frees hit it and the log
   ABSORBS every one after the first: the true cost is 2, one bitmap block
   and one inode block.  The credited arms of log_write and bfree
   ([LogInv.log_opS], [SpecBfree.wp_bfree_gen]) are what let that be stated.

   [bm_paid] below is the shape the loops carry.  It says "the bitmap
   block's log slot is paid for, and u units remain for everything else",
   as a disjunction over whether the payment has happened yet -- and it is
   IDEMPOTENT under bfree: the unpaid arm spends its spare unit and becomes
   paid, the paid arm presents its credit and absorbs.  So itrunc's loop
   invariant is literally [bm_paid γ bmapstart 1] -- one unit held back for
   iupdate -- unchanged across all 269 calls, with no data-dependent case
   split on which free happened to be the first.

   SPEND-AT-MOST-TWO, AT-LEAST-ONE.  The exit is [∃ u', u <= u' <= S u], the
   same shape bmap uses: iupdate always runs, so one unit is certainly
   spent; the bitmap unit is spent only if the inode named any block at all.

   itrunc SLEEPS (bread, and bfree's own bread), so it threads the full
   running-process bundle exactly as SpecBfree.v / SpecIupdate.v do.  It
   enters and returns at noff 0.

   NOT ITS BUSINESS: ip->lock.  The C comment says "Caller must hold
   ip->lock", and the caller does -- iput takes the sleeplock before
   calling.  itrunc itself performs no locking, so the contract simply takes
   the inode's resources directly, exactly as iupdate's does. *)
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
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* itrunc's own frame is 48 bytes (6 slots) -- [addi sp,sp,-48] at +0x00,
   ra/s0/s1/s2/s3 pushed, and s4 conditionally at +0x50.  Its deepest
   callee is bfree (44); bread wants 40, brelse 26 and iupdate 44. *)
Definition K_itrunc : nat := 50%nat.

(* THE TRUNCATED RECORD: the same inode with its size zeroed and its addrs
   emptied.  [type], [major], [minor] and [nlink] are untouched -- itrunc
   frees blocks, it does not delete the inode; zeroing the type is iput's
   job, one level up.  The addrs field is set to [bm_cells bm_empty] rather
   than left alone because iupdate's premise ties it to the map, and the map
   itrunc hands back is [bm_empty]. *)
Definition di_trunc (d : dinode) : dinode :=
  MkDinode (di_type d) (di_major d) (di_minor d) (di_nlink d)
           (bv_0 32) (bm_cells bm_empty).

Lemma di_trunc_addrs (d : dinode) : di_addrs (di_trunc d) = bm_cells bm_empty.
Proof. reflexivity. Qed.

Lemma di_trunc_wf (d : dinode) : dinode_wf (di_trunc d).
Proof.
  rewrite /dinode_wf /di_trunc /bm_cells /bm_empty. cbn [di_addrs bm_dir bm_ind].
  rewrite length_app length_replicate /=. reflexivity.
Qed.

Section ItruncSpec.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* "THE BITMAP BLOCK'S LOG SLOT IS PAID FOR, and u units remain for
     everything else."

     The left disjunct is the paid state: the op holds a credit for
     [bmapstart] and [S u] units.  The right is the unpaid state: no credit,
     but one extra unit in reserve to buy one.

     IDEMPOTENT UNDER bfree, which is the whole point.  From the unpaid
     state bfree's uncredited arm spends the spare unit, records the bitmap
     block in the op's set, and lands in the paid state; from the paid state
     bfree's credited arm presents the credit, log_write absorbs, and the
     unit comes back -- paid again.  So a loop that frees an unknown number
     of blocks carries this ONE assertion and never case-splits on how many
     it has freed so far. *)
  Definition bm_paid (γ : log_names) (bmapstart : Z) (u : nat) : iProp Σ :=
    ((∃ Sb : gset Z, ⌜bmapstart ∈ Sb⌝ ∗ log_opS γ (S u) Sb)
     ∨ (∃ Sb : gset Z, log_opS γ (S (S u)) Sb))%I.

  (* entering the loops: two units and no credit yet *)
  Lemma bm_paid_intro γ bmapstart u :
    log_op γ (S (S u)) -∗ bm_paid γ bmapstart u.
  Proof.
    iIntros "H". rewrite /log_op. iDestruct "H" as (Sb) "H".
    iRight. iExists Sb. iFrame.
  Qed.

  (* leaving them: at least the [S u] units iupdate still needs *)
  Lemma bm_paid_elim γ bmapstart u :
    bm_paid γ bmapstart u -∗ ∃ n : nat, ⌜(S u <= n <= S (S u))%nat⌝ ∗ log_op γ n.
  Proof.
    iIntros "[H|H]".
    - iDestruct "H" as (Sb) "(_ & H)". iExists (S u).
      iSplitR; [iPureIntro; lia|]. iApply (log_opS_op with "H").
    - iDestruct "H" as (Sb) "H". iExists (S (S u)).
      iSplitR; [iPureIntro; lia|]. iApply (log_opS_op with "H").
  Qed.

End ItruncSpec.

Definition wp_itrunc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (ip : mword 64) (inum : mword 32)
    (dn : dinode) (bm : blkmap) (ds : list dinode)
    (data : nat -> list (bv 8))
    (u : nat)
    (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.itrunc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_itrunc <= K)%nat ->
  log_geom_ok cov logstart ->
  (* ONE BITMAP BLOCK -- the fact that makes the budget work at all *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (* the inode's own block, for the closing iupdate *)
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  diblk_wf ds ->
  (* the map is well-formed: this is what says every block it names is a
     covered home block, and -- via injectivity -- that the 269 frees are
     269 DISTINCT blocks, so the free pool really does grow by
     [bm_blocks bm] *)
  blkmap_wf cov logstart bm ->
  (* EVERY BLOCK THE INODE NAMES IS IN RANGE FOR THE BITMAP.  bfree needs
     [0 <= b < size] and it is NOT derivable from what we already have:
     [blkmap_wf] records covered / non-log / injective, and [cov_ok] only
     bounds a covered block by 2^31, while [bitmap_ok] runs the other way
     (clear bits BELOW size are covered).  So this is a genuine FS
     consistency fact -- "an inode names only real block numbers" -- that
     the model does not yet carry anywhere, and itrunc has to take it.
     Recorded as owed in claude-notes/design/fs-inode.md: it belongs in
     [blkmap_wf] (which would have to take [size]), or in whatever
     invariant ilock establishes when it reads an inode off the disk.

     Note there is deliberately NO [bm_blocks bm ⊆ used] premise: itrunc
     holds [blk_own] for every block it frees (via [inode_blocks] and
     [ind_res]), and bfree derives the bit-is-set fact from that token
     itself ([BitmapInv.free_pool_own_used]).  Demanding it here would have
     made the contract uncallable by iput, which has no source for it. *)
  (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
     bv_unsigned (bm_slot bm i) < size) ->
  (* EVERY DATA BLOCK IS A BLOCK'S WORTH OF BYTES.  bfree demands it of the
     block it frees, and [inode_blocks] does not carry it: the bundle names
     contents but says nothing about their length.  Like the range premise
     above this is a genuine FS fact the model does not yet hold anywhere,
     and it is recorded as owed in fs-inode.md alongside it. *)
  (forall i : nat, length (data i) = BSIZE) ->
  (* the record's addrs field names the cells the map owns -- iupdate's tie,
     restated here because itrunc rewrites both together *)
  di_addrs dn = bm_cells bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* ip->dev and ip->inum: read, never written *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  (* the five scalars (ip->size is written), the thirteen addrs cells and
     the indirect block's own resource *)
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  (* THE DATA BLOCKS, which is what actually gets freed *)
  inode_blocks γfs bm data -∗
  (* the two superblock fields, read and handed straight back *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* the bitmap, with its free pool *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* the inode block, as sixteen pure dinodes *)
  fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
  (* the caller's own pid cell *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  scheds_inv γs -∗
  running_claim j -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units, not two.  The indirect arm's bread holds ONE across
     the whole 256-entry loop -- the buffer stays checked out while the
     entries are freed -- and each nested bfree still wants the two its own
     bread/log_write pair needs.  brelse gives the held one back at +0x7c.
     The direct loop never has a bread outstanding, so two would do there;
     the arm is what forces three. *)
  bslots bn 3 -∗
  (* THE RESERVATION: two units.  One buys the bitmap block's log slot --
     ONCE, however many blocks are freed -- and one is iupdate's. *)
  log_op γ (S (S u)) -∗
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
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE INODE IS EMPTY: no block, size zero *)
      inode_meta ip (di_trunc dn) -∗
      inode_map γfs ip bm_empty -∗
      inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
      (* ...and every block it named is back in the pool *)
      bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
      (* the flush landed: slot [inum mod IPB] holds the truncated inode *)
      fsblock γfs (IBLOCK inum inodestart)
              (diblk_bytes (<[islot inum := di_trunc dn]> ds)) -∗
      bslots bn 3 -∗
      (* SPEND AT MOST TWO, AT LEAST ONE: iupdate always runs; the bitmap
         unit is spent only if the inode named a block at all *)
      (∃ u' : nat, ⌜(u <= u' <= S u)%nat⌝ ∗ log_op γ u') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ITRUNC.
  Parameter wp_itrunc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (ip : mword 64) (inum : mword 32)
      (dn : dinode) (bm : blkmap) (ds : list dinode)
      (data : nat -> list (bv 8))
      (u : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_itrunc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart bmapstart inodestart size dev used
                           ip inum dn bm ds data u
                           pidv dq dqd dqn dqb dqs m K eb C b.
End ITRUNC.
