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
   Everything goes in and comes back out unchanged EXCEPT THE INUM'S OWN
   ON-DISK RECORD, which comes back at [dn] -- the in-memory inode.

   THE BLOCK PREMISE IS GONE (claude-notes/design/fs-icache.md, §11.3 and
   §12).  [fsblock] is per BLOCK and a dinode block holds SIXTEEN inodes,
   so a contract that takes the block's half for the duration of the call
   is unsatisfiable by two lock holders in the same block.  The inode
   REGION ([InodeRegion.v]) owns the halves instead and never lets them
   out; the caller holds the EXCLUSIVE per-inum fragment
   [dinode_at γi inum dn0] plus the persistent [ireg_inv], and iupdate
   hands it back retagged at [dn].  The sixteen-dinode list [ds] is now
   proof-internal: iupdate learns it at its own bread, via
   [InodeRegion.ireg_read].

   [dn0] IS THE STALE ON-DISK RECORD AND NEED NOT EQUAL [dn].  An inode
   with unflushed changes is the normal caller -- that is what iupdate is
   for -- so nothing here ties the fragment's value to [inode_meta]'s.

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
   number anywhere -- so it needs no exclusive token.  Who owns an inode
   block is no longer deferred: the region does (see above).

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
Require Import InodeRegion.
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
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
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
  (* the inum is one the region covers: [nib] inode blocks, sixteen inums
     each.  This replaces the old [diblk_wf ds] premise -- the region owns
     the well-formedness of every block it holds. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* ...and the record whose scalars [inode_meta] owns names exactly the
     thirteen addrs cells [inode_map] owns.  THE tie between the two
     resources; see the header. *)
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  iupdate itself never
     acquires or releases anything -- it just calls bread, whose OWN acquire
     mints [arm_pay 0 eb _] and whose OWN release spends it again before
     bread returns to iupdate.  So the complement iupdate receives at entry
     is a PURE PASS-THROUGH: at [eb = true] it is [emp], so no existing
     caller gains an obligation; at [eb = false] it is the honest pair, held
     by the caller because the TRAP handed it over, and iupdate threads it
     straight through to bread and back, unused, all the way to its own
     exit.  See claude-notes/completed/sched-hart-generic.md and
     claude-notes/projects/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
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
  (* THE INODE REGION, and THIS INUM'S on-disk record: the exclusive
     per-inum fragment that replaced the block half (design §11.3/§12).
     [dn0] is the STALE record -- it need not equal [dn]. *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE RESERVATION, SPEND-EXACTLY: the one log_write always runs *)
  log_op γ (S u) -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH: this inum's on-disk record is now the in-memory one.
         CONDITIONAL since fs-icache §16.4: for an allocated [dn] this is
         the retagged [InodeRegion.dinode_at] as before, and for a type-0
         [dn] -- iput's [ip->type = 0; iupdate(ip)], the one place an inode
         goes back to the free pool -- the fragment is ABSORBED into the
         region invariant and what comes back is [InodeRegion.imark], the
         marker the free pool arm now carries.  One contract, because the
         two cases differ only in the payout. *)
      ireg_out γi inum dn -∗
      bslots bn 2 -∗
      log_op γ u -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE SET-FORM CONTRACT (fs-icache.md section 18 clause 1)              *)
(*  Everything except the ledger is VERBATIM [wp_iupdate_sconf_body].     *)
(*  [wp_iupdate_sconf] is this with the set forgotten, derived at the     *)
(*  [log_op] existential's own witness -- so no existing caller moves.    *)
(*                                                                        *)
(*  WHY writei NEEDS THIS.  writei's own set-form contract promises its    *)
(*  caller [Sb ⊆ Sb'], and iupdate runs on EVERY returning path of        *)
(*  writei -- including the [n = 0] one.  Against the counted contract    *)
(*  the set coming out of iupdate is an unrelated existential, so the      *)
(*  monotonicity claim is simply unprovable past the flush.  This is the   *)
(*  one clause of section 18's ruling that could not be met by touching    *)
(*  the four files S3j sized.                                             *)
(* ===================================================================== *)
Definition wp_iupdate_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
    (u : nat) (Sb : gset Z)
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
  (* the inum is one the region covers: [nib] inode blocks, sixteen inums
     each.  This replaces the old [diblk_wf ds] premise -- the region owns
     the well-formedness of every block it holds. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* ...and the record whose scalars [inode_meta] owns names exactly the
     thirteen addrs cells [inode_map] owns.  THE tie between the two
     resources; see the header. *)
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* THE TRAP-CSR COMPLEMENT.  Same pure-pass-through shape as
     [wp_iupdate_sconf_body] above -- required so that a caller reaching
     iupdate through the SET form (writei's own loop, deriving its counted
     [wp_writei_sconf] from [wp_writei_gen]) can reach this contract at
     [eb = false] too.  See claude-notes/projects/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
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
  (* THE INODE REGION, and THIS INUM'S on-disk record: the exclusive
     per-inum fragment that replaced the block half (design §11.3/§12).
     [dn0] is the STALE record -- it need not equal [dn]. *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE RESERVATION, SPEND-EXACTLY: the one log_write always runs *)
  (* THE RESERVATION, SET FORM: spend-exactly on the counter, and the set
     grows by exactly the one block iupdate logs -- this inum's inode
     block.  DETERMINATE, not an existential: iupdate is straight-line, so
     [IBLOCK inum inodestart] is the whole of [Sb' ∖ Sb] and a caller
     needs no ceiling to know it. *)
  log_opS γ (S u) Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- the set form says exactly
     what the counted form above says; see that banner. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH: this inum's on-disk record is now the in-memory one.
         CONDITIONAL since fs-icache §16.4: for an allocated [dn] this is
         the retagged [InodeRegion.dinode_at] as before, and for a type-0
         [dn] -- iput's [ip->type = 0; iupdate(ip)], the one place an inode
         goes back to the free pool -- the fragment is ABSORBED into the
         region invariant and what comes back is [InodeRegion.imark], the
         marker the free pool arm now carries.  One contract, because the
         two cases differ only in the payout. *)
      ireg_out γi inum dn -∗
      bslots bn 2 -∗
      log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]}) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CREDITED SET-FORM CONTRACT (fs-sysfile S5a finding 3, retrofit 2) *)
(*                                                                        *)
(*  create runs THREE iupdates and four dirlinks, and every one of them    *)
(*  flushes an inode block one of its predecessors has already logged.     *)
(*  [CreateBudget.cr_budget_needs_inode_credit] is the machine-checked     *)
(*  refutation of doing without: an uncredited iupdate inside every        *)
(*  dirlink costs three extra units across the mkdir arm and the late      *)
(*  fail arm then cannot call its second [iunlockput].                     *)
(*                                                                        *)
(*  This is [SpecLogWrite.wp_log_write_gen]'s own [cr] device lifted       *)
(*  through a straight-line function; [wp_iupdate_gen] is this at          *)
(*  [cru := false], so no existing caller moves.                          *)
(* ===================================================================== *)
Definition wp_iupdate_cred_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
    (u : nat) (Sb : gset Z) (cru : bool)
    (pidv : mword 32) (dq dqd dqn dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iupdate <= K)%nat ->
  (* THE ABSORPTION CREDIT'S HONESTY PREMISE (fs-sysfile S5a finding 3).
     [cru] claims "this op has already logged this inode's block"; the
     premise is what makes the claim true, and it is exactly the device
     [SpecBmap] carries for [bmapstart] ([bmap_cost]'s [cr]) and
     [SpecLogWrite.wp_log_write_gen] carries for its own block. *)
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
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
  (* the inum is one the region covers: [nib] inode blocks, sixteen inums
     each.  This replaces the old [diblk_wf ds] premise -- the region owns
     the well-formedness of every block it holds. *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
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
  (* THE INODE REGION, and THIS INUM'S on-disk record: the exclusive
     per-inum fragment that replaced the block half (design §11.3/§12).
     [dn0] is the STALE record -- it need not equal [dn]. *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* THE RESERVATION, SPEND-EXACTLY: the one log_write always runs *)
  (* THE RESERVATION, SET FORM: spend-exactly on the counter, and the set
     grows by exactly the one block iupdate logs -- this inum's inode
     block.  DETERMINATE, not an existential: iupdate is straight-line, so
     [IBLOCK inum inodestart] is the whole of [Sb' ∖ Sb] and a caller
     needs no ceiling to know it. *)
  log_opS γ (S u) Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- the set form says exactly
     what the counted form above says; see that banner.  (Round 12: this body
     was the one [5ca52338]'s sweep could not see, because it landed on our
     side of the fork.) *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH: this inum's on-disk record is now the in-memory one.
         CONDITIONAL since fs-icache §16.4: for an allocated [dn] this is
         the retagged [InodeRegion.dinode_at] as before, and for a type-0
         [dn] -- iput's [ip->type = 0; iupdate(ip)], the one place an inode
         goes back to the free pool -- the fragment is ABSORBED into the
         region invariant and what comes back is [InodeRegion.imark], the
         marker the free pool arm now carries.  One contract, because the
         two cases differ only in the payout. *)
      ireg_out γi inum dn -∗
      bslots bn 2 -∗
      (* THE CREDITED SPEND ([CreateBudget.iu_spend cru]): the unit comes
         BACK when the block was already in the op's set, and is spent
         otherwise.  The NEED does not move -- [log_write] takes
         [log_opS (S u)] on BOTH arms, so a unit is in hand even to
         absorb -- which is why the precondition above is unchanged. *)
      log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUPDATE.
  Parameter wp_iupdate_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iupdate_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                            cov logstart inodestart nib dev ip inum dn dn0 bm u
                            pidv dq dqd dqn dqs m K eb C b.

  (* the SET-FORM contract; [wp_iupdate_sconf] above is its instance with the
     set forgotten, kept as its own parameter so that every existing caller
     is unchanged (wp_bmap_gen / wp_balloc_gen's pattern) *)
  Parameter wp_iupdate_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iupdate_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                          cov logstart inodestart nib dev ip inum dn dn0 bm u Sb
                          pidv dq dqd dqn dqs m K eb C b.
  (* the CREDITED set-form contract (S5a finding 3): the same walk with the
     unit returned when the op has already logged this inode's block.
     [wp_iupdate_gen] is its [cru := false] instance. *)
  Parameter wp_iupdate_cred :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iupdate_cred_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                           cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                           pidv dq dqd dqn dqs m K eb C b.
End IUPDATE.
