(* SpecLogWrite.v -- the public interface of log_write, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void log_write(struct buf *b) {
       int i;
       acquire(&log.lock);
       if (log.lh.n >= LOGBLOCKS)      panic("too big a transaction");
       if (log.outstanding < 1)        panic("log_write outside of trans");
       for (i = 0; i < log.lh.n; i++)
         if (log.lh.block[i] == b->blockno) break;   // log absorption
       log.lh.block[i] = b->blockno;
       if (i == log.lh.n) { bpin(b); log.lh.n++; }
       release(&log.lock);
     }

   log_write does NOT sleep -- it takes only the "log" SPINLOCK and calls
   bpin (which takes the bcache spinlock) -- so it threads no running-process
   bundle: [cpu_own n eb p C b] at the caller's own nesting level, exactly
   like SpecBpin.v.  It does need [panic_wp_any]: both of its own panic arms
   are DEAD (see below), but acquire's own holding-check arm wants a panic
   contract regardless.

   THE CONTRACT (claude-notes/design/fs-log.md, "log_write(b)").  The caller
   arrives holding a buffer it has typically EDITED, so its handle is
   [bio_held] with the traveling bytes [bs] and the payload still indexed at
   the block's old logical content [bsl] -- not [bio_locked], which is
   precisely why it cannot brelse the buffer yet.  log_write moves the
   logged view L(bno) from [bsl] to [bs] (the log lock's authority plus the
   caller's [fsblock] half plus the handle's payload half), so the handle
   comes back RE-INDEXED and DIRTY: [bio_locked ... bs bsd true], which is
   what brelse will accept.

   [d] is the incoming payload polarity, and it decides which path runs:
     d = false -- the first log_write of this block in the current batch.
                  The block is appended to lh.block[], lh.n++, and [bpin]
                  mints the pin that keeps the buffer un-evictable until
                  install_trans installs it.
     d = true  -- log ABSORPTION: the block is already in lh.block[] (its
                  dirty payload carries the earlier bpin's reference), so no
                  bpin runs at all.
   NEITHER PATH COSTS THE CALLER A SLOT UNIT: [bslot bn] goes in and comes
   back out, unconditionally.  On the absorb path it is simply never spent;
   on the append path [bpin] absorbs it and the n++ releases one unit of the
   POOL parked in [log_batch] ([bslots bn ((LOGBLOCKS - n) + 2)]) to replace
   it -- pool + n is invariant, and install_trans's bunpins refill it.  A
   conditional refund would poison every caller proof, which is exactly the
   argument the design doc's decision record makes about the budget unit.

   The BUDGET unit, by contrast, IS spent unconditionally on both paths
   ([log_op (S u)] in, [log_op u] out) -- always-consume is the C code's own
   worst-case MAXOPBLOCKS accounting (design doc, decision record).

   BOTH PANICS ARE DEAD, and the two ledger facts are what kill them:
     "too big a transaction"     -- a unit in hand forces lh.n < LOGBLOCKS
                                    (log_res's sum tie n + op_sum <= 30).
     "log_write outside of trans"-- an op token against the ledger authority
                                    forces log.outstanding >= 1
                                    (LogInv.log_op_positive). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import WpLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* log_write's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its
   deepest callee is bpin, which wants 14 (its own 4 plus acquire/release's
   10).  acquire/release directly want only 10. *)
Definition K_log_write : nat := 18%nat.

Definition wp_log_write_gen_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (cr : bool) (Sb : gset Z)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (* bpin runs UNDER log.lock, i.e. at nesting level S n, and its own
     acquire pushes again: the premise must cover TWO pushes above the
     entry level (the SpecPipeclose/SpecConsoleintr convention -- the +1
     form is underivable at the bpin call site, cpu_cells' own bound at
     level S n gives back only +1). *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage.  (The
     covered fact is also carried by the handle below; it is restated here
     because log_batch's own conjunct is what the append path must
     re-establish.) *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  (* THE CREDIT'S PREMISE: claiming the free arm means claiming this op
     has already appended [bno] in this batch. *)
  (cr = true -> uint bno ∈ Sb) ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* THE RESERVATION.  A unit must be IN HAND either way -- that is what
     bounds lh.n below LOGBLOCKS and so keeps the header's next slot
     writable ([nl <= 29]); a caller with an exhausted budget has no
     business in log_write even to absorb.  Uncredited (cr = false) the
     unit is spent and the block joins this op's already-logged set;
     credited (cr = true) the block is already in that set, log_write
     ABSORBS, lh.n does not grow, and THE UNIT COMES BACK. *)
  log_opS γ (S u) Sb -∗
  (* the caller's own view of the block, at its OLD content *)
  fsblock γfs (uint bno) bsl -∗
  (* the checked-out buffer.  [bio_held], NOT [bio_locked]: the caller has
     typically edited the bytes, so bs <> bsl and the payload is still
     indexed at bsl. *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the block is in the set either way -- it was already there on the
       credited arm ([Sb ∪ {[bno]} = Sb] under the premise), where the unit
       is also handed straight back *)
    log_opS γ (if cr then S u else u) (Sb ∪ {[uint bno]}) -∗
    (* L(bno) is now the bytes the caller wrote *)
    fsblock γfs (uint bno) bs -∗
    (* the handle re-indexed at those bytes and now DIRTY: brelse-able *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY -- see the header note *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_log_write_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γd : disk_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (k : nat) (pidv bno : mword 32)
    (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.log_write in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_log_write <= K)%nat ->
  (* bpin runs UNDER log.lock, i.e. at nesting level S n, and its own
     acquire pushes again: the premise must cover TWO pushes above the
     entry level (the SpecPipeclose/SpecConsoleintr convention -- the +1
     form is underivable at the bpin call site, cpu_cells' own bound at
     level S n gives back only +1). *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* a0 is the buffer being logged *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* the block is a covered HOME block: never the log's own storage.  (The
     covered fact is also carried by the handle below; it is restated here
     because log_batch's own conjunct is what the append path must
     re-establish.) *)
  uint bno ∈ cov ->
  ~ (uint bno ∈ log_region_set logstart) ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the slot unit backing the (possible) bpin *)
  bslot bn -∗
  (* one unit of this operation's reservation, spent unconditionally *)
  log_op γ (S u) -∗
  (* the caller's own view of the block, at its OLD content *)
  fsblock γfs (uint bno) bsl -∗
  (* the checked-out buffer.  [bio_held], NOT [bio_locked]: the caller has
     typically edited the bytes, so bs <> bsl and the payload is still
     indexed at bsl. *)
  bio_held bn (fs_view γfs γd dev cov) k pidv dev bno bs bsl bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* the unit is gone *)
    log_op γ u -∗
    (* L(bno) is now the bytes the caller wrote *)
    fsblock γfs (uint bno) bs -∗
    (* the handle re-indexed at those bytes and now DIRTY: brelse-able *)
    bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
    (* the slot unit comes back UNCONDITIONALLY -- see the header note *)
    bslot bn -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type LOG_WRITE.
  (* THE CREDITED / GENERAL FORM.  [wp_log_write_sconf] below is the
     set-forgetting instance of this at [cr = false]; it is kept as its own
     parameter so that every existing caller -- which threads [log_op] and
     neither knows nor cares which blocks this op has logged -- is unchanged. *)
  Parameter wp_log_write_gen :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_log_write_gen_body bn γ γfs γd cov logstart dev k pidv bno
                            bs bsl bsd d u cr Sb m n eb p C K b.

  Parameter wp_log_write_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId} (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_log_write_sconf_body bn γ γfs γd cov logstart dev k pidv bno
                              bs bsl bsd d u m n eb p C K b.
End LOG_WRITE.
