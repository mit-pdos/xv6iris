(* SpecInstallTrans.v -- the public interface of install_trans, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     static void install_trans(int recovering) {
       for (int tail = 0; tail < log.lh.n; tail++) {
         struct buf *lbuf = bread(log.dev, log.start + tail + 1);
         struct buf *dbuf = bread(log.dev, log.lh.block[tail]);
         memmove(dbuf->data, lbuf->data, BSIZE);
         bwrite(dbuf);
         if (recovering == 0) bunpin(dbuf);
         brelse(lbuf);
         brelse(dbuf);
       }
     }

   (gcc hoisted the [log.lh.n] test ahead of the prologue: at n <= 0 the
   function returns from a bare [c.ret] at +0xca having built no frame at
   all, and the printk of the recovering arm is inside the loop body.)

   THE COMMITTER-ONLY HELPER, WITH ITS FLAG AS A GHOST ARGUMENT.
   install_trans is [static]; end_op's commit calls it with recovering = 0
   and initlog's recover_from_log with recovering = 1, and both callers are
   holding the checked-out [log_batch] -- the "log" spinlock is NOT held.
   The [recovering] bool is a ghost argument pinning a0 (the [either_copy]
   precedent).

   STAGE 2 STATES TWO INSTANCES, and the premise
   [recovering = false \/ n = 0] is exactly their union:
     - recovering = false, any n -- end_op's commit-time install;
     - recovering = true with n = 0 -- initlog's clean-image call, which
       takes the +0x08 early return and does NOTHING (which is why the
       printk arm and the skipped bunpin never run in stage 2 at all).
   The recovering = true, n > 0 form -- real crash recovery, where the
   installed blocks are NOT pinned and there is no batch to speak of -- is
   STAGE 4's, and gets added with the crash invariant.

   WHAT IT TAKES, AND WHY.  install_trans breads both blocks itself, so per
   write-set entry it wants no handle; it wants the log copy's CLIENT half
   and the log side's DIRTY half of the home block:

     [∗ list] i |-> w in W,
        fsblock (log_slot_bno logstart i)   (Lw i) *   (* its log copy    *)
        (uint w) |->[fs_dirty]{1/2} true

   plus the PURE tie for the home side:

     forall i w, W !! i = Some w -> L !! uint w = Some (Lw i)

   A COMMITTER-SIDE CONTRACT WITNESSES HOME CONTENT THROUGH THE AUTHORITY IT
   HOLDS, NOT THROUGH A CLIENT HALF -- a home block's [fsblock] is
   UNOBTAINABLE here.  The home blocks' client halves belong to the FS layer
   above by construction (log_write hands each one back to its caller, and
   [log_batch] retains only the log REGION's), so end_op -- the only caller
   with a non-empty write set -- could never discharge such a premise.  What
   the committer does hold is [ghost_map_auth (fs_L γfs) 1 L], and one
   [ghost_map_lookup] against the payload the bread returns pins the home
   block's bytes to [L !! uint w], which the pure premise identifies with
   [Lw i].  The log slot's client half stays a resource: it rides in
   [log_batch], so the caller has it for free.

   Both sides therefore land at content [Lw i], which is the write_log
   invariant made a precondition: after write_log ran, log slot i holds
   exactly the logged content of W[i], and the committer's authority has
   FROZEN both ever since.  It is what makes the memmove a
   content-preserving copy and therefore makes the destination handle
   [bio_locked] again (bytes = the payload's index), which is what bwrite
   and brelse demand.  Nothing is assumed about the DISK content of either
   -- bwrite moves the home block's disk cell, which is the whole point of
   the pass.

   [ghost_map_auth (fs_L γfs) 1 L] rides through UNCHANGED: install writes
   the DISK, not the logical view (the memmove writes bytes already equal to
   the logged content).  [ghost_map_auth (fs_dirty γfs) 1 D] does move: each
   entry's flip true -> false at its bunpin needs the authority plus both
   halves (the payload's, out of the handle, and the log side's, peeled out
   of the batch's big-op by the caller), and the post's authority is
   [dirty_clear D (map uint W)].

   SLOT ACCOUNTING.  install_trans holds two buffers at a time, so it takes
   [bslots bn 2]; it returns [bslots bn (2 + length W)].  The surplus is
   real: each entry's [bunpin] frees the pin unit that log_write's [bpin]
   absorbed, and this is where it re-enters circulation.  Its home is the
   POOL parked in [log_batch] ([bslots bn ((LOGBLOCKS - n) + 2)]) -- the
   caller (end_op, or initlog with an empty log) deposits the surplus there
   when it re-forms the batch at n = 0, and the arithmetic is exact because
   length W = n.  Nothing of that shows here: this contract is stated in
   terms of its own two in-flight buffers and says only what it produces.

   install_trans sleeps (bread, bwrite, brelse), so it threads the full
   running-process bundle exactly as SpecBread.v does, plus the disk fabric;
   it enters and returns at noff 0.  It has no panic site of its own, but
   its callees' arms want [panic_wp_any]. *)
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

(* install_trans's own frame is 10 slots ([c.addi sp,sp,-80] at +0x0c); its
   deepest callee is bread (40).  memmove/bwrite/bunpin/brelse want less. *)
Definition K_install_trans : nat := 50%nat.

Definition wp_install_trans_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (recovering : bool)
    (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
    (L : gmap Z (list (bv 8))) (D : gmap Z bool)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (R : iProp Σ) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.install_trans in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_install_trans <= K)%nat ->
  (* the covered range's block-number bounds + the log region is covered:
     install_trans breads log slot [tail] as well as the home block *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* THE STAGE-2 RESTRICTION.  end_op installs at recovering = false;
     initlog calls at recovering = true but with an EMPTY log, where the
     function returns from its pre-frame test having done nothing.  Real
     recovery (recovering = true, n > 0) is stage 4's. *)
  (recovering = false \/ n = 0%nat) ->
  (* a0 is the flag *)
  m !!! Regidx (mword_of_int 10 : mword 5)
    = (mword_of_int (if recovering then 1 else 0) : mword 64) ->
  (* the batch's shape *)
  (n = length W /\ (n <= LOGBLOCKS)%nat) ->
  NoDup (map uint W) ->
  (forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)) ->
  (* THE HOME SIDE'S CONTENT WITNESS, as a fact about the authority below:
     a client [fsblock] for a home block cannot be had on the committer's
     side (see the header). *)
  (forall (i : nat) (w : SailStdpp.Values.mword 32),
     W !! i = Some w -> L !! uint w = Some (Lw i)) ->
  (* install_trans directly breads/bwrites/brelses/bunpins, all against
     "bcache" (4); it takes no lock of its own and calls no other function
     with a lower bound, so this is the one premise its whole cone needs. *)
  locks_below lks "bcache" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  install_trans has NO
     acquire/release of its own -- it delegates entirely to bread/bwrite, so
     a parking thread must hand [trap_csrs]/[cpu_claim] across the crossing
     exactly as [SpecBwrite.v] does: at [eb = true] this is [emp] (the
     callee's own acquire mints what it needs) and at [eb = false] it is the
     honest pair, held because the TRAP handed it over.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* NOT [log_ctx]: this helper holds no lock -- see LogInv.log_frozen *)
  log_frozen logstart dev -∗
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ---- the checked-out batch's pieces install_trans touches ---- *)
  (* the in-memory header, READ ONLY (the write set it walks) *)
  lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
  ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
  (* the logged view's authority: FROZEN and unchanged -- install writes
     the disk, not L *)
  ghost_map_auth (fs_L γfs) 1 L -∗
  (* the pinned-set authority: exactly W's entries go back to false *)
  ghost_map_auth (fs_dirty γfs) 1 D -∗
  (* per entry: the LOG COPY's client half at the logged content
     (write_log's postcondition, frozen by the authority above), plus the
     log side's dirty half of the home block.  The home block's own content
     comes from the authority (the pure premise above), not from a client
     half -- see the header. *)
  ([∗ list] i ↦ w ∈ W,
     fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
     (uint w) ↪[fs_dirty γfs]{#(1/2)} true) -∗
  (* two slot units: it holds lbuf and dbuf at the same time *)
  bslots bn 2 -∗
  (* THE CRASH PERMITS for the home writes (phase C2b/D1 stage 4).  One per
     entry -- but the entries' fupds are SEQUENTIAL, each consuming the
     era-side resource the previous one returned (for the FS client that is
     the log-region mirror half, which is what tells a fupd that the on-disk
     header still names the block it is about to overwrite).  A big-op of
     independent permits could therefore never be supplied: there is one
     such resource, not [n] of them.  So the premise is a REUSABLE GENERATOR
     over the one threaded resource [R], persistent and instantiated at each
     entry in turn; [R] itself is opaque here, which keeps install_trans as
     crash-agnostic as the rest of the log proofs.
     ([FsCrash.fs_install_permit] is exactly this shape, at
     [R := LogInv.log_mirror_at (n, map uint W)].  Its [▷] is what the
     bwrite's own [▷ Q] postcondition hands back, and a client whose [R] is
     timeless -- the mirror half is -- strips it inside the fupd.) *)
  □ (∀ (i : nat) (w : SailStdpp.Values.mword 32) (bs' : list (bv 8)),
       ⌜W !! i = Some w⌝ -∗ ⌜length bs' = 1024%nat⌝ -∗ ▷ R -∗
       disk_write_permit gen_id (Some ((1024 * uint w)%Z, bs')) R) -∗
  ▷ R -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two would coincide at [eb = true] --
     which is why this went unnoticed while [eb = true] was forced -- but at
     [eb = false] the [b] form would promise the caller it comes back on the
     hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* the in-memory header, unchanged (lh.n := 0 is the CALLER's store) *)
      lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
      ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
      ghost_map_auth (fs_L γfs) 1 L -∗
      ghost_map_auth (fs_dirty γfs) 1 (dirty_clear D (map uint W)) -∗
      ([∗ list] i ↦ w ∈ W,
         fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
         (uint w) ↪[fs_dirty γfs]{#(1/2)} false) -∗
      (* the two units back, PLUS one per entry: each bunpin frees the pin
         unit log_write's bpin absorbed.  See the header note. *)
      bslots bn (2 + length W) -∗
      (* the threaded resource, back from the last entry's DMA completion *)
      ▷ R -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type INSTALL_TRANS.
  Parameter wp_install_trans_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (recovering : bool)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (R : iProp Σ) (lks : gset string),
      wp_install_trans_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                                  cov logstart dev recovering n W Lw L D
                                  pidv dq m K eb b R lks.
End INSTALL_TRANS.
