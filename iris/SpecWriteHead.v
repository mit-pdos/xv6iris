(* SpecWriteHead.v -- the public interface of write_head, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     static void write_head(void) {
       struct buf *buf = bread(log.dev, log.start);
       struct logheader *hb = (struct logheader * ) buf->data;
       hb->n = log.lh.n;
       for (int i = 0; i < log.lh.n; i++) hb->block[i] = log.lh.block[i];
       bwrite(buf);
       brelse(buf);
     }

   THE COMMITTER-ONLY HELPER.  write_head is [static]; its only callers are
   end_op (via the inlined commit) and initlog (via the inlined
   recover_from_log), and BOTH of them are holding the checked-out
   [log_batch] when they call it -- the "log" spinlock is NOT held (the C
   code runs commit with no locks, which is the whole point of the
   committing flag).  So this contract does NOT take [log_res]; it takes,
   EXPLICITLY, exactly the pieces of the batch write_head touches:

     - the header cells it READS: lh.n at [lh_n_pa] and lh.block[i] at
       [lh_block i] for i < n = length W.  Both come back UNCHANGED --
       write_head only copies the in-memory header OUT to the buffer.
     - the logged-view AUTHORITY [ghost_map_auth (fs_L γfs) 1 L].  This is
       the freeze-by-auth: while the committer holds it nobody else can
       move L, and write_head needs it because it rewrites the header
       BLOCK's logical content.
     - the header block's own client half [fsblock γfs (log_hdr_bno
       logstart) bsh] -- the log is its own client for the header and the
       LOGBLOCKS slots.  It comes back at the new content [bs'], with the
       authority updated at that one key.
     - one [bslot] for its bread, returned by its brelse.

   WHAT THE POST SAYS ABOUT THE NEW HEADER.  Two facts, and the second one
   is what makes the commit fupd possible: [hdr_n bs' = n] -- the header's
   first little-endian 32-bit word, i.e. the [int n] field (LogInv.hdr_n) --
   and the FULL on-disk encoding [hdr_dec bs' = (n, map uint W)]
   (FsCrash.hdr_dec), i.e. that the copy loop really did lay W out as the
   following little-endian words.  The first is what initlog's clean-image
   path needs (it re-reads the header it just wrote, and its precondition is
   that n = 0 there); the second is what identifies the durable state this
   write commits to ([FsCrash.fs_commit_permit] decodes the header it is
   handed), so when n > 0 this bwrite is THE COMMIT POINT (D := L over W).

   write_head sleeps (bread, bwrite, brelse), so it threads the full
   running-process bundle exactly as SpecBread.v does, plus the disk
   fabric; it enters and returns at noff 0. *)
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
Require Import KernelDataInv.
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* write_head's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its
   deepest callee is bread (40).  bwrite/brelse want less. *)
Notation K_write_head := (62%nat) (only parsing).
Definition wp_write_head_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (n : nat) (W : list (mword 32)) (L : gmap Z (list (bv 8)))
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (Q : iProp Σ) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.write_head in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_write_head <= K)%nat ->
  (* the covered range's block-number bounds + the log region is covered:
     write_head breads the header block [log_hdr_bno logstart] *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the batch's shape: the cells below read the write set W *)
  (n = length W /\ (n <= LOGBLOCKS)%nat) ->
  (* write_head reaches "bcache" (rank 4) via both bread (its own scan/
     recycle acquires) and brelse (its unlink/splice acquire); nothing in
     its cone touches a lower rank, so one premise covers both callees. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
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
  (* ---- the checked-out batch's pieces write_head actually touches ---- *)
  (* the in-memory header, READ ONLY *)
  lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
  ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
  (* the freeze: the logged view's authority *)
  ghost_map_auth (fs_L γfs) 1 L -∗
  (* the header block's client half, at whatever it currently holds *)
  (∃ bsh : list (bv 8), fsblock γfs (log_hdr_bno logstart) bsh) -∗
  (* the slot unit for its bread *)
  bslot bn -∗
  (* THE CRASH PERMIT for the header write (phase C2b/D1 stage 3).  The
     caller does not know the header IMAGE this function will assemble -- it
     is built from [n] and [W] by the copy loop -- so the permit is supplied
     as a FAMILY over the bytes, given the one fact the assembly establishes
     about them.  At [n = 0] (initlog's clear, and the clear that ends a
     commit) [hdr_n bs' = 0] plus [FsCrash.hdr_dec_zero] pins the whole
     decoding, which is all a clear's fupd needs
     ([FsCrash.fs_clear_permit]); the COMMIT arm ([FsCrash.fs_commit_permit])
     consumes the third hypothesis instead. *)
  (∀ bs' : list (bv 8), ⌜length bs' = 1024%nat⌝ -∗ ⌜hdr_n bs' = Z.of_nat n⌝ -∗
     ⌜hdr_dec bs' = (n, map uint W)⌝ -∗
     disk_write_permit gen_id (Some ((1024 * log_hdr_bno logstart)%Z, bs')) Q) -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (bs' : list (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* the in-memory header, unchanged *)
      lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
      ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
      (* the authority back, moved at exactly the header block's key *)
      ghost_map_auth (fs_L γfs) 1 (<[log_hdr_bno logstart := bs']> L) -∗
      fsblock γfs (log_hdr_bno logstart) bs' -∗
      (* the two facts stated about the new header image: its n field, and
         the full (n, W) encoding the copy loop laid down *)
      ⌜hdr_n bs' = Z.of_nat n⌝ -∗
      ⌜hdr_dec bs' = (n, map uint W)⌝ -∗
      bslot bn -∗
      (* the permit's RECEIPT, back from the DMA completion *)
      ▷ Q -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WRITE_HEAD.
  Parameter wp_write_head_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (L : gmap Z (list (bv 8)))
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (Q : iProp Σ) (lks : gset string),
      wp_write_head_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                               cov logstart dev n W L pidv dq m K eb b Q lks.
End WRITE_HEAD.
