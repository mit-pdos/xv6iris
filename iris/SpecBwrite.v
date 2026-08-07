(* SpecBwrite.v -- the public interface of bwrite, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void bwrite(struct buf *b) {
       if (!holdingsleep(&b->lock)) panic("bwrite");
       virtio_disk_rw(b, 1);
     }

   The write-through: the caller's held buffer goes to the disk.  The
   block's [disk_block] rides INSIDE the handle (claude-notes/design/
   fs-log.md), so the exchange is interior: the handle comes back with its
   disk value equal to its bytes.  The handle is the PAYLOAD-LESS
   [bio_hold0]: a content-changing write (write_head rewriting the
   header) necessarily has logical /= disk on one side of the call
   whatever the order of the ghost update and the write, so the clean
   payload's disk tie cannot appear here -- the caller holds its
   [bio_pay] aside across the call ([BioInv.bio_held_split]) and
   re-pairs afterwards (write_head: gamma_L update AFTER the write, then
   the clean tie holds; install_trans: the dirty payload never mentions
   the disk value at all).
   The panic arm is dead: [bio_locked] carries the sleeplock token and the
   holder-carried pid cell, and the caller's own pid cell agrees, so
   holdingsleep returns 1 (SpecHoldingsleep.v's holder variant).

   Because the body calls virtio_disk_rw, this spec threads rw's whole
   resource list (SpecVirtioDiskRw.v): the running-process identity and
   sleep plumbing, the disk fabric, and the vdisk lock. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
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
Require Import BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* bwrite's own frame is 32 bytes (4 slots); its deepest callee is
   virtio_disk_rw (34). *)
Definition K_bwrite : nat := 38%nat.

Definition wp_bwrite_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names) (V : bio_view Σ) (k : nat)
    (pidv dev bno : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (bs bsd : list (bv 8)) (b : bool)
    (Q : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bwrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_bwrite <= K)%nat ->
  (* rw's honest arithmetic premise: sector = blockno * 2 in 32 bits *)
  (uint bno < 2147483648)%Z ->
  (* the handle's interior disk fragment lives at the fabric's ghost *)
  bv_gd V = γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 is the buffer *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- which only the interior acquire can mint,
     and only with an enabled base.  See SpecSched.v / SpecSleep.v. *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  (* enters at noff 0 (rw's acquire raises it to what sleep demands) *)
  cpu_own 0 eb pj C b -∗
  (* TRAP CSRs: NOT threaded.  This function acquires at level 0 and releases
     before returning, so it is push/pop- AND trap-CSR-BALANCED: its own
     [acquire] mints the [trap_csrs_pay 0 eb] its interior sleep needs and its
     [release] spends it.  A CALLER-held level-0 pay would be a second one, and
     a second one is UNIMPLEMENTABLE above a park -- sleep carries exactly the
     one the pushing acquire minted, so the extra copy would be [trap_csrs] at
     the parking hart with the postcondition wanting it at the resuming one
     (and at [eb = true] two of them at one hart are outright contradictory).
     See claude-notes/completed/sched-hart-generic.md. *)
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn V -∗
  (* the caller's own pid cell, agreeing with the handle's (holdingsleep) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle rw's sleeps thread through *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* the held buffer, payload aside (its interior disk fragment included) *)
  bio_hold0 bn V k pidv dev bno bs bsd -∗
  (* THE CRASH PERMIT (claude-notes/design/fs-log.md stage 4 item 3): bwrite
     is a WRITE-THROUGH, so it is one of the WAL's write kinds and its
     caller owes the durability view shift.  Threaded verbatim to
     virtio_disk_rw (SpecVirtioDiskRw.v), which deposits it in the permit
     channel at the publish; the DMA COMPLETION -- the instant these bytes
     reach the durable image -- runs it, and [Q] is the caller's RECEIPT.
     Placed adjacent to the handle, exactly where rw places its own (after
     the buffer/[disk_block] pair it is about).

     THE PERMIT IS INDEXED BY THIS CALL'S OWN WRITE (phase C2a): bwrite
     always writes, and it writes [bs] at block [bno] -- bytes
     [1024 * bno ..].  A WRITE's permit is NOT free the way a READ's is, and
     that is the honest content of the indexed crash predicate: every one of
     the three log.c call sites supplies a REAL durability fupd
     ([FsCrash.fs_logfill_permit] and its siblings), and there is no
     [Pc]-generic way to write a disk block. *)
  disk_write_permit gen_id (Some (1024 * uint bno, bs)%Z) Q -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* the write-through: the handle's disk value is now its bytes *)
      bio_hold0 bn V k pidv dev bno bs bs -∗
      (* THE RECEIPT, under ONE later -- rw's own postcondition shape (the
         permit invariant is not timeless, and the saved-proposition
         agreement costs the other later, which rw's epilogue pays off). *)
      ▷ Q -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BWRITE.
  Parameter wp_bwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (bs bsd : list (bv 8)) (b : bool)
      (Q : iProp Σ),
      wp_bwrite_sconf_body Φ γs j γl γu γd γk pd pav pu bn V k
                           pidv dev bno dq m K eb C bs bsd b Q.
End BWRITE.
