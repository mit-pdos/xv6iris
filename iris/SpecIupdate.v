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
Require Import PanicStub.
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
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
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
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  The
     region's [InodeRegion.ireg_write_au] now demands that a flush either
     CLEAR the type or LEAVE IT ALONE, so that no-writer-retypes-an-
     allocated-inode is a theorem of the model rather than a claim about
     this tree's callers (§19.1(i)).  The premise travels through iupdate
     unchanged: [dn0] is the stale on-disk record and [dn] the one being
     flushed.  Every caller has it today -- iput's free path takes the LEFT
     disjunct (its [ip->type = 0] store), writei/itrunc/create the
     equation, since none of them ever moves the type field. *)
  InodeRegion.di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f).  The link
     ledger's (L1) will cap the live directory records naming this inum by
     that inum's [nlink], so the region's flush must refuse to LOWER it:
     sys_unlink's decrement is the one writer that does, and it goes
     through [InodeRegion.ireg_write_unlink], which pays for the drop by
     consuming a fragment.  Travels exactly as [di_type_stable] does, and
     for the same reason: the record the REGION holds at iupdate's seam is
     the STALE [dn0].  Every caller discharges it with
     [InodeRegion.di_nlink_stable_refl] -- no writer at or below iupdate
     moves [nlink] at all. *)
  InodeRegion.di_nlink_stable dn dn0 ->
  (* ...and the record whose scalars [inode_meta] owns names exactly the
     thirteen addrs cells [inode_map] owns.  THE tie between the two
     resources; see the header. *)
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  iupdate itself never
     acquires or releases anything -- it just calls bread, whose OWN acquire
     mints [arm_pay 0 eb _] and whose OWN release spends it again before
     bread returns to iupdate.  So the complement iupdate receives at entry
     is a PURE PASS-THROUGH: at [eb = true] it is [emp], so no existing
     caller gains an obligation; at [eb = false] it is the honest pair, held
     by the caller because the TRAP handed it over, and iupdate threads it
     straight through to bread and back, unused, all the way to its own
     exit.  See claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
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
      cpu_own 0 eb pj b lks -∗
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
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
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
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  The
     region's [InodeRegion.ireg_write_au] now demands that a flush either
     CLEAR the type or LEAVE IT ALONE, so that no-writer-retypes-an-
     allocated-inode is a theorem of the model rather than a claim about
     this tree's callers (§19.1(i)).  The premise travels through iupdate
     unchanged: [dn0] is the stale on-disk record and [dn] the one being
     flushed.  Every caller has it today -- iput's free path takes the LEFT
     disjunct (its [ip->type = 0] store), writei/itrunc/create the
     equation, since none of them ever moves the type field. *)
  InodeRegion.di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f).  The link
     ledger's (L1) will cap the live directory records naming this inum by
     that inum's [nlink], so the region's flush must refuse to LOWER it:
     sys_unlink's decrement is the one writer that does, and it goes
     through [InodeRegion.ireg_write_unlink], which pays for the drop by
     consuming a fragment.  Travels exactly as [di_type_stable] does, and
     for the same reason: the record the REGION holds at iupdate's seam is
     the STALE [dn0].  Every caller discharges it with
     [InodeRegion.di_nlink_stable_refl] -- no writer at or below iupdate
     moves [nlink] at all. *)
  InodeRegion.di_nlink_stable dn dn0 ->
  (* ...and the record whose scalars [inode_meta] owns names exactly the
     thirteen addrs cells [inode_map] owns.  THE tie between the two
     resources; see the header. *)
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT.  Same pure-pass-through shape as
     [wp_iupdate_sconf_body] above -- required so that a caller reaching
     iupdate through the SET form (writei's own loop, deriving its counted
     [wp_writei_sconf] from [wp_writei_gen]) can reach this contract at
     [eb = false] too.  See claude-notes/completed/eb-generic-sweep.md. *)
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
      cpu_own 0 eb pj b lks -∗
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
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
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
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  The
     region's [InodeRegion.ireg_write_au] now demands that a flush either
     CLEAR the type or LEAVE IT ALONE, so that no-writer-retypes-an-
     allocated-inode is a theorem of the model rather than a claim about
     this tree's callers (§19.1(i)).  The premise travels through iupdate
     unchanged: [dn0] is the stale on-disk record and [dn] the one being
     flushed.  Every caller has it today -- iput's free path takes the LEFT
     disjunct (its [ip->type = 0] store), writei/itrunc/create the
     equation, since none of them ever moves the type field. *)
  InodeRegion.di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f).  The link
     ledger's (L1) will cap the live directory records naming this inum by
     that inum's [nlink], so the region's flush must refuse to LOWER it:
     sys_unlink's decrement is the one writer that does, and it goes
     through [InodeRegion.ireg_write_unlink], which pays for the drop by
     consuming a fragment.  Travels exactly as [di_type_stable] does, and
     for the same reason: the record the REGION holds at iupdate's seam is
     the STALE [dn0].  Every caller discharges it with
     [InodeRegion.di_nlink_stable_refl] -- no writer at or below iupdate
     moves [nlink] at all. *)
  InodeRegion.di_nlink_stable dn dn0 ->
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
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
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
      cpu_own 0 eb pj b lks -∗
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

(* ===================================================================== *)
(*  THE CREDITED SET-FORM CONTRACT, eb-GENERIC (fs-sysfile GR-2b)         *)
(*                                                                        *)
(*  [wp_iupdate_cred] above pins [eb := true], which is all create needs   *)
(*  -- a syscall runs with an enabled base.  itrunc does NOT: its own      *)
(*  contract is eb-generic (it is a pure pass-through to its sleeping      *)
(*  callees, threading [trap_csrs_ext eb] / [cpu_claim_ext eb] straight    *)
(*  through), and its tail flush is the one call that has to carry the     *)
(*  [cru] credit.  So the credited walk has to be exposed at the SAME      *)
(*  altitude the counted one already is.                                   *)
(*                                                                        *)
(*  This is [wp_iupdate_cred_body] with the [eb = true] premise dropped,   *)
(*  the two complements threaded, and -- since fs-log.md §G.4 -- the       *)
(*  absorption credit taken as a RESOURCE against a NAMED birth epoch      *)
(*  rather than as the pure own-set premise.  It is the STRONGEST of the   *)
(*  four and the other three are derived from it: [wp_iupdate_cred] is     *)
(*  this at [eb := true], [wp_iupdate_gen] is this at [cru := false], and  *)
(*  [wp_iupdate_sconf] is [wp_iupdate_gen] at the [log_op] existential's   *)
(*  own witness; each derivation opens the epoch ([LogInv.log_opS_named])  *)
(*  and builds the credit with [LogInv.log_credit_own], so all three       *)
(*  statements -- and every one of their callers -- are byte-stable.       *)
(*  Kept as a FOURTH parameter rather than by widening one of the three,   *)
(*  so no existing caller's arity moves ([ProofWritei] applies             *)
(*  [wp_iupdate_gen] positionally).                                        *)
(* ===================================================================== *)
Definition wp_iupdate_credgen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
    (u : nat) (Sb : gset Z) (cru : bool) (e0 : nat) (v : nat)
    (pidv : mword 32) (dq dqd dqn dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iupdate <= K)%nat ->
  (* the absorption credit's honesty premise is a RESOURCE here, not the
     pure own-set claim the other three carry (fs-log.md §G.19/§G.4).
     [LogInv.log_credit] admits BOTH ways of knowing that this op's batch
     already holds this inode's block: the own-set fact every landed
     claimant has ([log_credit_own], one line, which is what keeps
     [wp_iupdate_cred] / [wp_iupdate_gen] and their callers byte-stable),
     and the GROUP witness -- [∃ e, logged_at γ e b ∗ ⌜e0 <= e⌝] -- that no
     caller can convert to a membership outside the log spinlock.  The
     second is the whole point: it is what [InodeRegion.ireg_obs_use] pays
     out at a [crz] iput, and this contract FORWARDS it to [log_write]
     rather than rebuilding it.

     It travels beside [log_opSe] (the birth epoch NAMED) and not
     [log_opS] (it buried), because the credit is only sound against the
     epoch of the op presenting it -- §G.9 finding 1. *)
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  InodeRegion.di_type_stable dn dn0 ->
  InodeRegion.di_nlink_stable dn dn0 ->
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 2 -∗
  (* THE DEPOSIT'S IN-HALF (fs-log.md §G.3/§G.16).  [v] is the caller's own
     epoch anchor -- in the one caller that matters, the value its escrow
     slot's observation counter currently holds ([IcacheEscrow.ic_ep_open]
     hands it out with exactly this bound).  Persistent, so it costs a
     caller nothing to keep, and every caller that has no use for the
     receipt passes [v := 0], where the bound is the unit. *)
  log_epoch_lb γ v -∗
  log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
  log_opSe γ (S u) Sb e0 -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ireg_out γi inum dn -∗
      bslots bn 2 -∗
      (* EPOCH-CLOSED ON THE WAY OUT.  The credit above is an ENTRY-side
         premise -- it is spent by the flush -- and [log_write]'s own post
         re-closes the birth-epoch existential ([LogInv.log_opSw]), so the
         contract is asymmetric on purpose: [log_opSe] in, [log_opS] out. *)
      log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
      (* THE DEPOSIT'S OUT-HALF.  iupdate is straight-line and always
         log_writes, so this is unconditional: the witness is minted by the
         [log_write] ghost step (both arms since §G.11) and the comparison
         is discharged THERE, where the [ln_ep] auth is open -- [v <= E] by
         [log_epoch_lb_le] against the premise above, and [e = E] because a
         live entry is born at the current epoch.  Neither half can be done
         at the escrow park, which is why §G.3's self-contained receipt is
         dead and this contract is where the deposit lives. *)
      (∃ e : nat, logged_at γ e (IBLOCK inum inodestart) ∗ ⌜(v <= e)%nat⌝) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE LINK-MINTING CONTRACT (design fs-icache.md §20.18, stage C2)      *)
(*                                                                        *)
(*  [ip->nlink++; iupdate(ip)] -- create's [dp->nlink++] at +0x128,        *)
(*  mkdir's [".."] payment and sys_link's own increment.  §20.6's table    *)
(*  calls it the ledger moving in the same ghost step as the count that    *)
(*  pays for it: (L1) grows on BOTH sides at once, which is what keeps     *)
(*  the region's cap an inequality nobody has to re-argue, and it is why   *)
(*  the mint cannot be a separate fupd the caller fires beside an ordinary *)
(*  flush -- between the two the invariant would hold [w = nlink + 1].     *)
(*                                                                        *)
(*  IT IS [wp_iupdate_cred_body] WITH TWO EDITS AND NOTHING ELSE.          *)
(*    (i) [InodeRegion.di_nlink_stable dn dn0] -- "nlink does not fall" -- *)
(*        becomes the EXACT increment.  The ordinary premise would be      *)
(*        satisfied by this caller too, but it is not enough for the       *)
(*        region: the mint has to know the count grew by exactly the one   *)
(*        unit the new fragment costs.  It is stated at the MACHINE's      *)
(*        width ([di_nlink dn = add_vec (di_nlink dn0) 1]) plus the        *)
(*        kernel's NLINK_MAX guard, not as the Z equation -- see the       *)
(*        premise itself for why the Z form is unsuppliable and what       *)
(*        derives it (InodeRegion's (L4), the twelfth stop).               *)
(*   (ii) the post's [InodeRegion.ireg_out γi inum dn] becomes             *)
(*        [dinode_at γi inum dn ∗ ilink (bv_unsigned inum)].  With a       *)
(*        nonzero type [ireg_out] IS [dinode_at], so this is the same      *)
(*        payout plus the minted fragment -- the ticket a written          *)
(*        directory record needs (§20.10's finding 1) and the one thing    *)
(*        no landed contract in the tree could produce.                    *)
(*                                                                        *)
(*  THE ONE ADDED PREMISE, AND WHY IT IS NOT OPTIONAL.                     *)
(*  [bv_unsigned (di_type dn) <> 0] is a THIRD difference from the         *)
(*  credited body, and it is forced rather than chosen: (L3) says a        *)
(*  type-0 record has [nlink = 0], while (i) makes the flushed record's    *)
(*  [nlink] at least one, so a type-0 [dn] makes the region's closing      *)
(*  clause FALSE -- the write is unprovable there, not merely             *)
(*  unsupported.  Every caller has it from [InodeLock.inode_ok]; the       *)
(*  ordinary body does not need it only because [ireg_out]'s type-0 arm    *)
(*  leaves through [InodeRegion.ireg_free_au] instead.                     *)
(*                                                                        *)
(*  A FIFTH PARAMETER, POSITIONAL, for the reason the fourth is one (the   *)
(*  banner above): no existing caller's arity moves, and the four landed   *)
(*  contracts stay byte-stable.  [cru]-credited and [eb := true], i.e.     *)
(*  cut to create's altitude -- a syscall runs with an enabled base, and   *)
(*  no nlink-raising flush in the kernel runs anywhere else.               *)
(* ===================================================================== *)
Definition wp_iupdate_link_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iupdate <= K)%nat ->
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  InodeRegion.di_type_stable dn dn0 ->
  (* THE ADDED PREMISE (see the banner): (L3) plus the increment below make
     a type-0 flush contradictory, so the region cannot take one here. *)
  bv_unsigned (di_type dn) <> 0 ->
  (* THE INCREMENT ITSELF, in place of [di_nlink_stable]: this flush RAISES
     the count by exactly one, and that one unit is what pays for the
     [ilink] the post hands out (§20.6's mkdir/sys_link rows).

     STATED AT THE MACHINE'S OWN WIDTH, AND THAT IS FORCED (fs-sysfile.md's
     twelfth stop).  The Z-level equation
     [bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn0) + 1] is what
     the ledger needs, but NO CALLER CAN PROVE IT: the store is a
     sixteen-bit [++] ([lhu] / [addiw] / [sh]), it wraps at
     [bv_unsigned = 65535], and nothing outside [InodeRegion] bounds a link
     count above -- xv6 117c0e7's guard is a SIGNED test [== 32767] and
     leaves that corner alive
     ([ProofCreateParts.cr_nlink_guard_leaves_the_wrap] is the witness).
     So the caller supplies the two facts its WALK has -- the value the
     [sh] commits, and the branch the guard gave it -- and the region
     derives the Z equation under (L4), where the bound is open.  Both are
     free at the fresh-child mint, where [fresh_shape] pins the old count
     to zero. *)
  di_nlink dn = add_vec (di_nlink dn0 : mword 16) (mword_of_int 1) ->
  di_nlink dn0 <> (mword_of_int 32767 : mword 16) ->
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  eb = true ->
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 2 -∗
  log_opS γ (S u) Sb -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH, AND THE MINT.  The retagged fragment exactly as the
         other four bodies hand it back (the type is nonzero, so
         [ireg_out] is [dinode_at] here), plus the ONE ledger fragment the
         raised count pays for.  It travels to the [dirlink] that deposits
         it in a directory's [DirLinks.dir_links]. *)
      dinode_at γi inum dn -∗
      ilink (bv_unsigned inum) -∗
      bslots bn 2 -∗
      log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE LINK-SPENDING CONTRACT (design fs-icache.md §20.18, stage C4)     *)
(*                                                                        *)
(*  [ip->nlink = 0; iupdate(ip)] -- create's fail arm, and                *)
(*  [dp->nlink--; iupdate(dp)] -- sys_unlink's parent decrement.  It is    *)
(*  the DUAL of [wp_iupdate_link] and it is that body with four edits:     *)
(*                                                                        *)
(*    (i) the increment is FLIPPED: [nlink dn0 = nlink dn + 1], i.e. the   *)
(*        OLD count is the new one plus one.  This is the only            *)
(*        nlink-LOWERING flush in the kernel, which is exactly why         *)
(*        [wp_iupdate_gen]'s [di_nlink_stable] may stand unweakened.       *)
(*   (ii) [ilink (bv_unsigned inum)] moves from the POST to the PREMISE:   *)
(*        the drop is PAID FOR by consuming one ledger fragment, so (L1)   *)
(*        falls on both sides in the same ghost step and no fragment ever  *)
(*        outlives the count that backs it.                               *)
(*  (iii) the payout is [dinode_at γi inum dn] alone -- the retagged       *)
(*        fragment, which with a nonzero type is what [ireg_out] is.       *)
(*   (iv) THE RECEIPT PREMISE, and it is the whole of stage C4.            *)
(*                                                                        *)
(*  WHY (iv) EXISTS.  [InodeRegion.izrcpt] is owed at the record this      *)
(*  flush writes: a record whose [nlink] is ZERO must carry a witness that *)
(*  its inode block is in the CURRENT batch's header, or a later iput      *)
(*  cannot claim the absorption its free path needs (fs-log.md §G.17).     *)
(*  No caller can build one -- the comparison it needs is against the      *)
(*  [ln_ep] auth, which lives behind the log spinlock -- so the receipt is *)
(*  built INSIDE log_write's ghost step, out of the two inputs             *)
(*  [SpecLogWrite.wp_log_write_au]'s closing wand now takes.  What is left *)
(*  for the caller is only to say WHICH of the two routes it is on, and    *)
(*  the premise is that choice, in [LogInv.log_credit]'s disjunctive       *)
(*  style:                                                                *)
(*                                                                        *)
(*    - LEFT, the WITNESS route (create's [ip->nlink = 0]): the record     *)
(*      being written may have [nlink = 0], so the receipt must be real.   *)
(*      It costs no resource -- the wand's [logged_at]/[<=] inputs are it  *)
(*      -- only the two AMBIENT TIES, [⌜γ = icfg_log⌝] and                 *)
(*      [⌜inodestart = icfg_ist⌝], which are what identify the region's    *)
(*      own log and first inode block with the threaded ones               *)
(*      ([SpecIput]'s [crz] premise carries the same pair, for the same    *)
(*      reason: a tie between a threaded name and an ambient record field  *)
(*      is sayable only as a pure equation, true at boot by [icfg_alloc]). *)
(*    - RIGHT, the VACUOUS route (sys_unlink's [dp->nlink--], and any      *)
(*      decrement that lands nonzero): [⌜nlink dn <> 0⌝] makes [izrcpt]'s  *)
(*      antecedent false, so the receipt is free, the anchor is the unit   *)
(*      at the caller's own [γ], and NEITHER tie is needed.                *)
(*                                                                        *)
(*  A SIXTH PARAMETER, POSITIONAL, for the fifth's reason: no landed       *)
(*  caller's arity moves and the five landed contracts stay byte-stable.   *)
(*  [cru]-credited and [eb := true], cut to create's altitude, exactly as  *)
(*  the fifth is.                                                         *)
(* ===================================================================== *)
Definition wp_iupdate_unlink_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iupdate <= K)%nat ->
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  InodeRegion.di_type_stable dn dn0 ->
  (* the fifth body's added premise, unchanged: (L3) makes a type-0
     record's count zero, and the region's closing clause needs the type to
     stay out of that corner while a fragment is being spent. *)
  bv_unsigned (di_type dn) <> 0 ->
  (* THE DECREMENT, the flip of the fifth body's increment: the OLD count
     is the new one plus one, and the [ilink] premise below is what pays
     for it.

     DELIBERATELY STILL IN Z FORM, and the asymmetry with its sibling is
     the point (the twelfth stop's ruling asked for the call).  The
     increment had to move to the machine's width because a caller cannot
     prove the Z equation of a count it does not bound; the DECREMENT has
     no such problem -- lowering never wraps in the reachable range, every
     caller reaches this contract having just written a KNOWN halfword
     (create's fail arm writes a literal zero at +0x146), and (L4) is
     preserved here for free because the new count is below one the
     invariant already bounded.  Matching the shapes would buy symmetry
     and cost the landed consumer a re-thread, so it is not done. *)
  bv_unsigned (di_nlink dn0) = bv_unsigned (di_nlink dn) + 1 ->
  di_addrs dn = bm_cells bm ->
  length (bm_dir bm) = NDIRECT ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  eb = true ->
  (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
     ("bcache", 4) -- "log" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* THE FRAGMENT THE DROP SPENDS (edit (ii)): consumed, not returned. *)
  ilink (bv_unsigned inum) -∗
  (* THE RECEIPT PREMISE (edit (iv); see the banner).  Persistent in both
     arms, so it costs a caller nothing to keep, and pure in both, so the
     choice is made with one [iLeft]/[iRight]. *)
  (⌜γ = icfg_log⌝ ∗ ⌜inodestart = icfg_ist⌝
   ∨ ⌜bv_unsigned (di_nlink dn) <> 0⌝) -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 2 -∗
  log_opS γ (S u) Sb -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map γfs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE FLUSH, AND NOTHING MINTED (edit (iii)): the retagged fragment
         alone -- the type is nonzero, so this is [ireg_out] here -- and
         the [ilink] that went in is GONE, spent by the count it paid. *)
      dinode_at γi inum dn -∗
      bslots bn 2 -∗
      log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUPDATE.
  Parameter wp_iupdate_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                            cov logstart inodestart nib dev ip inum dn dn0 bm u
                            pidv dq dqd dqn dqs m K eb b lks.

  (* the SET-FORM contract; [wp_iupdate_sconf] above is its instance with the
     set forgotten, kept as its own parameter so that every existing caller
     is unchanged (wp_bmap_gen / wp_balloc_gen's pattern) *)
  Parameter wp_iupdate_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                          cov logstart inodestart nib dev ip inum dn dn0 bm u Sb
                          pidv dq dqd dqn dqs m K eb b lks.
  (* the CREDITED set-form contract (S5a finding 3): the same walk with the
     unit returned when the op has already logged this inode's block.
     [wp_iupdate_gen] is its [cru := false] instance. *)
  Parameter wp_iupdate_cred :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_cred_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                           cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                           pidv dq dqd dqn dqs m K eb b lks.
  (* the credited set-form contract at itrunc's altitude: eb-generic, so a
     pure pass-through caller can hand its own complements through, and
     RESOURCE-credited, so a caller holding the group witness rather than
     the own-set fact can claim the absorption too (fs-log.md §G.4).  Both
     [wp_iupdate_gen] ([cru := false]) and [wp_iupdate_cred] ([eb := true])
     are derived from it through [LogInv.log_credit_own]; it is stated
     separately so neither of their arities moves. *)
  Parameter wp_iupdate_credgen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool) (e0 : nat) (v : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_credgen_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 v
                              pidv dq dqd dqn dqs m K eb b lks.

  (* the LINK-MINTING contract (design §20.18 stage C2): the credited walk
     at a flush that RAISES [nlink] by one, paying out the [ilink] fragment
     that raise buys.  A fifth parameter for the fourth's reason -- widening
     any of the four would move a landed caller's arity, and this one's
     postcondition differs, not just its premises. *)
  Parameter wp_iupdate_link :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_link_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                           cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                           pidv dq dqd dqn dqs m K eb b lks.

  (* the LINK-SPENDING contract (design §20.18 stage C4): the credited walk
     at a flush that LOWERS [nlink] by one, spending the [ilink] that drop
     costs and carrying the zero-record receipt through log_write's own
     ghost step.  A sixth parameter for the fifth's reason. *)
  Parameter wp_iupdate_unlink :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_iupdate_unlink_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                             cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                             pidv dq dqd dqn dqs m K eb b lks.
End IUPDATE.
