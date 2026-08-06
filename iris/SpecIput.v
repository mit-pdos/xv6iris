(* SpecIput.v -- the public interface of iput, stated independently of any
   proof.  iput is ASSUMED: this file is a [Module Type] with no [Proof<F>.v]
   behind it, the sanctioned pattern already used for balloc / writei /
   fileclose (claude-notes/design/spec-modules.md, "An ASSUMED callee").
   [LinkIput.v] supplies the single instance with an [Axiom], so kexit's own
   proof stays axiom-free and proving iput later replaces exactly one file.

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
   iupdate -- so it threads the full running-process bundle exactly as
   SpecBalloc.v / SpecIupdate.v do: procs_inv / scheds_inv / own_ctx /
   park_hlf / p_pid, the disk fabric, three buffer slots, and the parking
   premise [eb = true].  It enters and returns at noff 0.

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
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
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
    (Φ : mval -> iProp Σ)
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
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
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
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 3 -∗
      (* at most [iput_units] gone, and none gained *)
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type IPUT.
  Parameter wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
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
      wp_iput_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart dev ip n pidv dq m K eb C b.
End IPUT.
