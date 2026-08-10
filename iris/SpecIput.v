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

   ==== THE REFERENCE PREMISE IS THE REMAINING HOLE ======================

   It is [FileInv.inode_ref ip 1], which is literally [emp].  It used to be
   spelled [ProcInv.cwd_ref ip] -- the SAME proposition, but named after the
   process side and dragging a [ProcInv] import into a filesystem contract,
   which is what forced [fileclose] to launder a file's payload into a "cwd"
   reference at its [iput] call.  That laundering is gone; the name here is
   now the one whose content it actually is.

   [ProcInv.cwd_ref] IS REAL NOW ([InodeRef.iref_at]), and this premise is
   deliberately NOT it.  The blocker is the other caller: the last
   [fileclose] of an FD_INODE file must hand this function the reference its
   [struct file] held, and [FileInv.file_payload]'s inode arm is still a
   placeholder because parking ONE reference behind FRACTIONAL payload
   holders is an unsolved file-table design question -- see
   claude-notes/projects/cwd-ref.md, "STILL TO DO -- the consumers".
   Strengthening this premise before that lands would break fileclose, which
   is proven.

   WHAT THAT COSTS TODAY, precisely: kexit holds a real [cwd_ref] and must
   DROP it here rather than spend it (ProofKexit.v, at the [ld a0,336(s3)]),
   which is marked at its site and goes away with the file-table half.

   THE POSTCONDITION'S [iref_slot] IS NOT PART OF THAT HOLE, and it is
   true of the code: iput decrements [ip->ref], and [IcacheInv.islot] parks
   one unit of the fixed supply per outstanding reference, so a reference
   destroyed frees exactly one place for another.  kexit NEEDS it -- the
   ZOMBIE [ProcInv.proc_dormant] it builds parks [1 + IREFSPARE], the [1]
   being the cwd unit this call hands back -- and the accounting law
   [IREFSLOTS = NPROC*(1 + IREFSPARE) + NFILE] is false without it.
   [fileclose]'s last closer gets one too and currently drops it; that drop
   is the file table's half of the same hole and is marked there.

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
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ,
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
  (* THE REFERENCE BEING DESTROYED -- still a placeholder, see the header *)
  FileInv.inode_ref ip 1 -∗
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
      (* THE PLACE THE DESTROYED REFERENCE FREED -- see the header. *)
      iref_slot -∗
      (* at most [iput_units] gone, and none gained *)
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op γ n' -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IPUT.
  Parameter wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ,
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
