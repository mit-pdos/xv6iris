(* SpecVirtioDiskRw.v -- the public interface of virtio_disk_rw, stated
   independently of its proof.

   virtio_disk_rw(b, write) moves ONE 1024-byte block between the caller's
   buffer cache entry [b] and the disk.  The headline of the spec is the
   DISK POINTS-TO exchange:

     write = 0 (READ):   { disk_block bno data }  ->  { disk_block bno data
                            ∗ b->data holds data }
     write ≠ 0 (WRITE):  { disk_block bno old ∗ b->data holds new }
                         ->  { disk_block bno new ∗ b->data still new }

   Concurrency is entirely inside the two shared structures the spec merely
   references: the vdisk_lock's resource [disk_res] (DiskInv.v) and the
   device invariant [dev_inv] whose [virtio_proto] half carries the DMA
   lease and the per-request protocol (VirtioProto.v).  Nothing about other
   requests appears here.

   The function sleeps twice (descriptor exhaustion; completion), so it
   threads the full sleep/wakeup plumbing of SpecSleep.v: the process
   identity (γs, j), procs_inv, the running-thread bundle.
   It enters at noff 0 (acquire raises to 1, which is what sleep demands)
   and returns at noff 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

(* rw's own frame is 96 bytes (12 slots); its deepest callee is sleep (22). *)
Notation K_virtio_disk_rw := (34%nat) (only parsing).
(* the caller's buffer bundle [buf_own] (blockno at 1/2, disk and data full)
   now lives in BufOwn.v (via DiskInv's re-export): the bio.c layer shares
   it, and the bcache scan is why the blockno half stays behind. *)

Definition wp_virtio_disk_rw_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !uartGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* fabric + lock ghosts *)
    (pd pav pu : mword 64)
    (m : regfile) (K : nat) (eb : bool)
    (bno dsk0 : mword 32) (bs_buf bs_disk : list (bv 8)) (b : bool)
    (Q : iProp Σ) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.virtio_disk_rw in
  let pj := proc_addr j in
  (* a0 = the [struct buf *b] argument, a1 = write.  Renamed to [bp] (was
     [b]): [b] is now the SIE-index binder every contract in this port
     carries, so the pre-existing local collides with it (porting-guide
     rule: rename the pre-existing binder, never the new index). *)
  let bp : Arch.pa := m !!! Regidx (mword_of_int 10 : mword 5) in
  let wr : bool :=
    negb (eq_vec (m !!! Regidx (mword_of_int 11 : mword 5) : mword 64)
                 (zero_reg : mword 64)) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_virtio_disk_rw <= K)%nat ->
  (* PREMISE ADDED (2026-07-28): the sector number is computed by the C source
     as [b->blockno * (BSIZE / 512)] in 32-BIT arithmetic (blockno is a
     [uint]), so the doubling must not wrap -- otherwise the request's sector
     would not be [2 * bno] and the block the device touches would not be the
     one [disk_block γd (uint bno) _] names.  xv6 mounts a filesystem of
     FSSIZE = 2000 blocks, so this is not a restriction in practice; it is
     the honest statement of what the code computes. *)
  (uint bno < 2147483648)%Z ->
  (* PREMISE ADDED (2026-07-28): the descriptor the driver publishes names
     [b->data] as a PHYSICAL DMA address, while [buf_own]'s bytes are owned
     at the VA tier ([↦ₘ], the byte at [pa_of ppn va]) -- the two coincide
     only for an identity (static) kernel mapping.  So the publish genuinely
     requires the buffer to be kernel DATA; without it the code hands the
     device the wrong address and is WRONG, not merely unprovable.  It holds
     for every caller: [b] is a [struct buf] inside bio.c's static [bcache].
     (Same shape as the [uint bno < 2^31] premise above: the honest
     statement of what the code needs.)  [KptPt.kdata_svpn_class] turns it
     into the [kmap_static … KP_rw] the tier bridges consume. *)
  (forall k, (k < 1024)%nat -> addr_is_kdata (pa_add (b_data bp) k)) ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* order premise at the lowest rank this cone reaches. *)
  locks_below lks "virtio_disk" ->
  sie_cap_gpr m K b pj -∗
  (* enters at noff 0; acquire raises to the level sleep requires *)
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM.  Everything below sleeps,
     and a parking thread must hand [trap_csrs] and [cpu_claim] across the
     crossing (SpecSched.v).  At [eb = true] this function's OWN acquire
     frees them out of [sie_arm true], so the complement is [emp] and the
     caller brings nothing -- which is why this used to be an [eb = true]
     premise instead.  At [eb = false] the push_off frees nothing and the
     caller brings the pair, holding it because the TRAP handed it over. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* the caller's buffer and the disk block it names.
     BSIZE = 1024 and sector = blockno * 2, so the block's byte range on
     the disk starts at 1024 * blockno. *)
  buf_own bp bno dsk0 bs_buf -∗
  disk_block γd (uint bno) bs_disk -∗
  (* THE CRASH PERMIT (claude-notes/design/fs-log.md stage 4; PermInv.v).
     The caller supplies its own logically-atomic view shift over the crash
     predicate, curried with the write's identity and its own ghosts; the
     driver deposits it in the permit channel at the publish, and the DMA
     COMPLETION -- the instant this request's bytes reach the durable image
     -- runs it.  [Q] is the caller's RECEIPT, and it comes back below.
     THE PERMIT IS INDEXED BY THIS REQUEST'S WRITE (phase C2a): a READ moves
     no disk byte, so its index is [None] and [disk_write_permit_trivial]
     still proves it for an ARBITRARY crash predicate -- every read caller is
     unchanged.  A WRITE's index is the block this call is about
     ([1024 * bno], BSIZE bytes), which is what lets the caller's fupd be
     about its OWN block and what the DMA completion discharges from the
     published slot ([VirtioQueue.vs_wr]).  A caller with no durability
     obligation instantiates the pair trivially and its statement is
     unchanged in meaning. *)
  disk_write_permit gen_id
    (if wr then Some (1024 * uint bno, bs_buf)%Z else None) Q -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] (porting guide: "a PARKING
     function's [wp_next] index is [true] UNCONDITIONALLY").  virtio_disk_rw
     sleeps -- twice -- so a [swtch] can move the hart with interrupts OFF,
     which has nothing to do with SIE.  While this contract carried
     [eb = true ->], [cpu_own_eb_agree] forced [b = true] too and the two
     spellings coincided, which is what hid this: the [b = false] instance
     was vacuous, so the weak "returns on the hart that called it" promise
     was never actually collected.  It stops being vacuous the moment
     [eb = false] is reachable, which is exactly this generalization. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      (* the exchange: a read fills the buffer from the block, a write
         moves the buffer's bytes onto the disk; b->disk ends at 0 *)
      buf_own bp bno (mword_of_int 0 : mword 32)
              (if wr then bs_buf else bs_disk) -∗
      disk_block γd (uint bno) (if wr then bs_buf else bs_disk) -∗
      (* THE RECEIPT, under ONE later: collecting it costs the permit
         invariant's own later (it is not timeless -- it holds arbitrary
         client view shifts) plus the saved-proposition agreement's, and the
         epilogue's instruction stream pays one of the two off. *)
      ▷ Q -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type VIRTIODISKRW.
  Parameter wp_virtio_disk_rw_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !diskGhostG Σ, !uartGhostG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (m : regfile) (K : nat) (eb : bool)
      (bno dsk0 : mword 32) (bs_buf bs_disk : list (bv 8)) (b : bool)
      (Q : iProp Σ) (lks : gset string),
      wp_virtio_disk_rw_sconf_body γs j γl γu γd γk pd pav pu
                                   m K eb bno dsk0 bs_buf bs_disk b Q lks.
End VIRTIODISKRW.
