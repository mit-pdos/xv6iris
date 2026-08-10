(* SpecIput.v -- the public interface of iput.

   ==== TWO MODULE TYPES LIVE HERE, AND ONE OF THEM IS SCHEDULED TO DIE ====

   [IPUT2] (bottom of the file) is THE contract: iput over the real inode
   cache, proven by [ProofIput.v] and instantiated by [LinkIput.v].  New
   callers take this one.

   [IPUT] (immediately below) is the OLD, emp-shaped statement -- the one
   written when there was no inode model and [ProcInv.cwd_ref] was literally
   [emp].  It is FROZEN VERBATIM: not one character of it, of
   [wp_iput_sconf_body], of [K_iput] or of [iput_units] may move, because six
   already-proven cones (kexit, fileclose, pipealloc, sys_close, sys_exit,
   sys_pipe) are functors over it and their proof files are not to be
   touched.  [LinkIputCompat.v] supplies it with the single bridging [Axiom]
   that keeps those cones building.

   THE BRIDGE IS NOT A THEOREM AND IS NOT DERIVED FROM [IPUT2].  It cannot
   be: the v1 statement consumes [ProcInv.cwd_ref ip] at a raw pointer [ip],
   and [cwd_ref] is [emp] -- there is no slot, no fraction and no identity in
   it, so nothing in it determines which itable entry the caller means, and
   [IPUT2]'s [inode_ref (icn_ref cn) k q dev inum] cannot be manufactured
   from it.  Retiring the axiom is therefore a CALLER-SIDE change, not a
   derivation: C6b replaces the [emp] placeholders
   ([FileInv.inode_ref] / [ProcInv.cwd_ref]) with real references carried
   through an [icacheG]-supplied gname, re-proves the six cones against
   [IPUT2], and then deletes [LinkIputCompat.v], this module type,
   [wp_iput_sconf_body] and its two constants in one move, renaming
   [IPUT2] -> [IPUT] mechanically.  See claude-notes/projects/fs-icache.md,
   C6b.

   Until then the kexit-cone [Print Assumptions] audit shows exactly one fs
   axiom, [LinkIputCompat.IputCompat.wp_iput_sconf], in place of the old
   [LinkIput.Iput.wp_iput_sconf] -- the same assumption, moved, NOT a new
   one and NOT a stronger one.

   ================= THE FROZEN v1 STATEMENT FOLLOWS ====================

   The original header, kept as written:

     void iput(struct inode *ip) {
       acquire(&itable.lock);
       if(ip->ref == 1 && ip->valid && ip->nlink == 0){
         // inode has no links and no other references: truncate and free.
         acquiresleep(&ip->lock);
         release(&itable.lock);
         itrunc(ip);
         ip->type = 0;
         iupdate(ip);
         ip->valid = 0;
         releasesleep(&ip->lock);
         acquire(&itable.lock);
       }
       ip->ref--;
       release(&itable.lock);
     }

   ==== WHAT THE CONTRACT SAYS, AND WHY IT IS THIS WEAK ==================

   iput DESTROYS one inode reference and MAY SPEND LOG BUDGET.  That is the
   whole of it, and it is the whole of what its callers -- kexit here, and
   sys_chdir / sys_unlink / fileclose later -- actually depend on.

   The reference is [ProcInv.cwd_ref ip].  There is no inode model in this
   tree yet, so that predicate is literally [emp] (design/proc-struct.md,
   "holes to be honest about"): it is a PLACEHOLDER with the shape of
   [ofile_slot]'s file clause, deliberately introduced so that the contracts
   which surrender an inode reference can be written NOW and gain content
   later without being restated.  This spec is one of those contracts.  When
   the inode layer lands, [cwd_ref] becomes "ip names a live itable entry
   and this is one of its references" and iput's precondition here does not
   change a character.

   The budget is a SPEND-AT-MOST clause, the shape [SpecBmap.v] fixed and
   for the same reason: [log_op] moves only through [LogInv.log_spend_step]
   against the ledger authority inside log.lock, and iput never takes that
   lock -- so it cannot hand a surplus back, and the honest postcondition is
   an interval.  The fast path (a reference that is not the last) spends
   NOTHING and the interval covers that too.  [iput_units] is the whole
   reservation: xv6 sizes MAXOPBLOCKS so that one operation's worth of
   metadata writes fits, and itrunc + iupdate is the operation this spends
   for.  A caller inside begin_op/end_op therefore always satisfies the
   premise, and none of them cares what comes back.

   iput SLEEPS -- acquiresleep on the inode, and bread underneath itrunc /
   iupdate -- so it threads the running-process bundle exactly as
   SpecBalloc.v / SpecIupdate.v do: procs_inv / p_pid, the disk fabric,
   three buffer slots, and the parking premise [eb = true].  It enters and
   returns at noff 0.  The parked scheduler record is not among them: it
   lives in the running proc's own [p->lock] ([SchedCtx.run_slot]).

   WHAT IS DELIBERATELY NOT HERE.  Nothing about ip's fields, nothing about
   which arm ran, and no [inode_map]/[inode_blocks] traffic: with no inode
   model those would be invented vocabulary, and inventing it here -- in a
   contract nobody can yet prove -- is exactly how an assumed spec becomes
   wrong.  The one thing an assumed contract must not do is claim MORE than
   the code delivers; this claims strictly less. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
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
Require Import ProcInv.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* iput's own frame is 48 bytes; its deepest callee is bread (40) below
   itrunc's own frame, plus acquiresleep.  Sized like balloc's, one frame
   deeper. *)
Definition K_iput : nat := 60%nat.

(* THE BUDGET IT MAY SPEND: the whole reservation.  itrunc's bfree writes
   (bitmap blocks) plus iupdate's one are what xv6 sizes MAXOPBLOCKS for. *)
Definition iput_units : nat := MAXOPBLOCKS.

Definition wp_iput_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (ip : mword 64) (n : nat)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iput in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iput <= K)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* enough budget for the truncate-and-free arm *)
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- everything below
     sleeps.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* three buffer slots: the inode block is held across the indirect
     block's bread and across log_write, as in bmap *)
  bslots bn 3 -∗
  (* THE REFERENCE BEING DESTROYED -- today a placeholder, see the header *)
  cwd_ref ip -∗
  (* this operation's reservation *)
  log_op γ n -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 3 -∗
      (* at most [iput_units] gone, and none gained *)
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IPUT.
  Parameter wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (n : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iput_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart dev ip n pidv dq m K eb C b.
End IPUT.

(* ===================================================================== *)
(*  ===== SpecIput v2 -- THE REAL CONTRACT, over the real inode cache ==== *)
(* ===================================================================== *)

(* Two below-icache blockers were found by tracing the proof forward and
   both are now ruled on (design §13.12):

     (B1) iput calls acquiresleep at noff = 1 (itable.lock held), and
          SpecAcquiresleep demands [cpu_own 0 ...].  ROUTE B adopted: the
          sleeping branch is panic("sched locks"), so it DIVERGES and
          [panic_wp_any] -- which iput already carries -- closes it.
          LANDED (ef035525): [SpecSched.wp_sched_locks_body],
          [SpecSleep.wp_sleep_locks_body] and
          [SpecAcquiresleep.wp_acquiresleep_nested_body] are proven and
          instantiated.  The truncate arm calls
          [wp_acquiresleep_nested_sconf] at n := 0.  NOTHING in this
          statement changes because of it.

     (B2) SpecItrunc's [forall i < MAXFILE, length (data i) = BSIZE] is not
          derivable: [data] is EXISTENTIAL inside [ic_loaded], and
          [inode_ok] pinned lengths only at HOLES ([blk_holes_zero]).
          FIXED AND LANDED (a791194a): [InodeInv.inode_sized] IS
          [inode_ok]'s seventh conjunct, so iput derives the premise from
          the checked-out bundle at the call site.  NO premise appears
          below for it, and SpecItrunc is unchanged.

   NOTE ON THE TWO CONSTANTS.  [K_iput] is shared with the frozen v1
   statement (same value, same reason: iput's own 48-byte frame plus
   bread's, one frame deeper than balloc's).  The BUDGET is not shared:
   v1 reserved the whole [MAXOPBLOCKS], v2 knows the real number, and the
   v1 constant may not move, so v2 gets its own.                         *)

(* itrunc's two (bitmap block + its closing iupdate) plus iput's own
   iupdate at +0x6c.  SPEND-AT-MOST: the fast path spends nothing. *)
Definition iput2_units : nat := 3%nat.

Definition wp_iput2_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)          (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names)                                   (* the icache's names  *)
    (gtl : gname)                                     (* itable.lock         *)
    (gil gisl : gname)                                (* ip->lock            *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (k : nat) (q : Qp) (inum : mword 32)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iput <= K)%nat ->
  (* ENTRY BY SLOT -- a0 is the entry address, and [ientry_inj] is what
     makes the 64-bit pointer and the slot the same thing *)
  (k < NINODE)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* --- itrunc's geometry, threaded verbatim (SpecItrunc.v) --- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the inum is one the inode REGION covers: ireg_read / ipool_acc *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* bfree's per-slot range fact, via IcacheInv.blkmap_slot_inrange *)
  cov_below cov size ->
  (* enough budget for the truncate-and-free arm *)
  (iput2_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* PARKING PREMISE -- UNCONDITIONAL.  iput MAY truncate, and no caller
     can know in advance which arm runs, so the bundle is not conditional.
     (Note (B1): under Route B the truncate arm's acquiresleep is the
     NESTED one, which does not park; bread under itrunc/iupdate still
     does, so this premise stays.) *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  (* the itable spinlock over the v2 resource; §13.11's trailing device *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  (* the [ref] words *)
  itable_inv (icn_ref cn) -∗
  (* THIS slot's escrow -- iput knows its slot, so unlike iget it needs no
     ic_escrows family *)
  ic_escrow cn gfs gi cov logstart k -∗
  (* the inode region *)
  ireg_inv gi gfs inodestart nib -∗
  (* the entry's sleeplock, over the CHECKOUT TOKEN alone *)
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* ---- THE REFERENCE BEING DESTROYED ---- *)
  inode_ref (icn_ref cn) k q dev inum -∗
  (* ---- itrunc / iupdate's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* the caller's own pid cell (acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* three buffer slots: itrunc's indirect arm is what forces three *)
  bslots bn 3 -∗
  (* this operation's reservation *)
  log_op g n -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE BITMAP IS TWO-ARMED (the C2 finding, predicted for exactly
         this contract): the truncate arm returns [used minus bm_blocks bm]
         at the ESCROW's existential [bm], the close arms return [used]
         untouched.  An unconditional record would be unprovable. *)
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      bslots bn 3 -∗
      (* at most [iput2_units] gone, and none gained *)
      ⌜((n - iput2_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (* THE LEDGER: one unit back, on EVERY arm.  islot2's live arm holds
         [iref_slots (Pos.to_nat n)]; a non-last close takes n -> n-1 and
         frees one, a last close deletes the slot and frees the one the
         n = 1 arm held.  iget spends exactly one on both ITS arms, so
         iget/iput are a matched pair against the fixed IREFSLOTS supply. *)
      iref_slot -∗
      (* ...AND NOTHING ELSE.  The reference is consumed; xv6's iput
         returns void and the caller's pointer is dead. *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IPUT2.
  Parameter wp_iput2_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iput2_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                          cov logstart bmapstart inodestart nib size dev used
                          k q inum n pidv dq dqb dqs m K eb C b.
End IPUT2.
