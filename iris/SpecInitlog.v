(* SpecInitlog.v -- the public interface of initlog, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void initlog(int dev, struct superblock *sb) {
       initlock(&log.lock, "log");
       log.start = sb->logstart;
       log.dev   = dev;
       recover_from_log();            // INLINED, and read_head with it
     }
     static void read_head(void) {
       struct buf *buf = bread(log.dev, log.start);
       struct logheader *lh = (struct logheader * ) buf->data;
       log.lh.n = lh->n;
       for (int i = 0; i < log.lh.n; i++) log.lh.block[i] = lh->block[i];
       brelse(buf);
     }
     static void recover_from_log(void) {
       read_head(); install_trans(1); log.lh.n = 0; write_head();
     }

   (The C's [if (sizeof(struct logheader) >= BSIZE) panic(...)] is
   compile-time false and is not in the image: initlog has no panic site of
   its own.)

   THE CONSTRUCTOR.  initlog is where the whole log layer comes into
   existence: it is handed the RAW material -- the .bss-zeroed [struct log]
   cells, the superblock field naming the log's start block, the FsBlocks
   authorities and the log region's client halves -- and its postcondition
   is the persistent [log_ctx], the context every other log.c function
   takes.  The ledger authority ([LogInv.log_ledger_alloc]) and the "log"
   spinlock's ghost name are allocated INSIDE the proof, so neither appears
   in the interface; only [∃ γ : log_names, log_ctx ...] comes out.

   STAGE 2 IS THE CLEAN-IMAGE FORM.  The premise [hdr_n bs_hdr = 0] says the
   on-disk header's [n] field reads zero -- true of a freshly mkfs'd image,
   and of any image that was cleanly unmounted.  It makes read_head's copy
   loop dead (blez at +0x40 taken), makes the [install_trans(1)] call return
   from its own pre-frame test having done nothing, and makes the closing
   [write_head] write a header that still says n = 0.  REAL RECOVERY -- a
   committed on-disk log to install -- is stage 4, the consumer of the crash
   receipt [P_fs] (claude-notes/design/fs-log.md).

   WHAT COMES IN, PIECE BY PIECE.
     - the two ARGUMENTS: a0 = dev (sign-extended, RV64 ABI), a1 = sb, plus
       a fraction of [sb->logstart] at offset 20 -- read once at +0x28 and
       handed straight back.
     - the RAW spinlock cells of [struct log] (the lock is its first member,
       so &log.lock = &log) plus [kernel_data], out of which the proof reads
       the "log" string literal at [log_name_str] -- the SpecBinit /
       SpecIinit pattern.
     - the REST of struct log's cells.  [log.outstanding] and
       [log.committing] arrive AT ZERO: initlog never writes them, and the
       invariant needs them zero, which is exactly the .bss guarantee for a
       static object.  Everything else arrives at an arbitrary value
       (initlog overwrites start/dev/lh.n; lh.block[] is only written by the
       dead copy loop, so all thirty slots come in -- and go into the batch
       -- as junk).
     - the FsBlocks material: both authorities (they become the batch's
       freeze), the LOG SIDE's dirty halves over the whole covered range at
       [false] (the payloads hold the other halves), and the log region's
       CLIENT halves -- the header block at [bs_hdr] and the thirty slots at
       arbitrary content.  The log is its own client for exactly those
       blocks.
     - the SLOT POOL to stock, plus a working pair: [bslots bn 34].  Thirty
       two of them ([(LOGBLOCKS - 0) + 2]) go into [log_batch]'s pool and
       stay sealed inside the lock; the pair comes back.  (initlog itself
       only ever holds one buffer, but the [install_trans] contract asks for
       two even on the dead path.)

   The heavy assembly (raw cells + material -> [log_res] -> sealed lock) is
   the PROOF's ghost step, not part of this statement.

   initlog sleeps (bread / brelse, and write_head's bwrite), so it threads
   the full running-process bundle exactly as SpecBread.v does, plus the
   disk fabric and [bio_ctx]; it enters and returns at noff 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
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
Require Import FsCrash.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* initlog's own frame is 6 slots ([c.addi16sp sp,-48] at +0x00); its
   deepest callee is install_trans (50).  write_head wants 44, bread 40,
   initlock 2. *)
Definition K_initlog : nat := 56%nat.

(* the string literal initlog passes to initlock -- it sits in .rodata past
   etext with no ELF symbol of its own (the [auipc a1,0x4 ; addi a1,a1,-1658]
   pair at +0x1a/+0x1e), so it is spelled out here; the proof reads its bytes
   out of [kernel_data] with [kernel_data_string]. *)
Definition log_name_str : Z := 0x800074f8.

Definition wp_initlog_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32) (sb : mword 64)
    (bs_hdr : list (bv 8))
    (L : gmap Z (list (bv 8))) (D : gmap Z bool)
    (* the raw struct log cells initlog is handed *)
    (vlock : mword 32) (vname vcpu : mword 64)
    (v_start v_dev v_nc v_n : mword 32)
    (pidv : mword 32) (dq dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.initlog in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let c_name := lock_name_field log_addr in
  let c_cpu := lock_cpu log_addr in
  (K_initlog <= K)%nat ->
  (* the covered range's block-number bounds + the log's own storage is
     covered: initlog breads the header and write_head breads it again *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  eb = true ->
  (* THE STAGE-2 CLEAN-IMAGE PRECONDITION: the on-disk header says n = 0, so
     read_head's copy loop and install_trans's recovery pass are both dead.
     Real recovery is stage 4. *)
  hdr_n bs_hdr = 0 ->
  (* the two arguments (RV64 ABI: the [int dev] arrives sign-extended) *)
  m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
  m !!! Regidx (mword_of_int 11 : mword 5) = sb ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* THE CRASH SEAM (phase C2b/D1 stage 3): the persistent identification of
     the machine layer's crash predicate with THIS file system's [P_fs].  It
     is what lets [initlog]'s final [write_head] carry a REAL durability fupd
     -- the swap that takes custody of the crash record for this era.  The
     boot client gets it from the adequacy instantiation. *)
  fs_crash_seam cov logstart -∗
  (* the era certificate: the swap installs custody AT [gen_id], and the
     registry element + started lower bound are exactly what identifies it *)
  gen_cert -∗
  (* THE ERA'S LOG-REGION MIRROR VARIABLE (phase C2b/D1 stage 2), whole: no
     custody of the crash record has been taken yet, so both halves are the
     era's, and [initlog] is what splits them -- one into [log_batch] (the
     era's continuing half), one into [P_fs]'s checked-out arm when the swap
     lands (stage 3).  It comes from the era boot bundle, minted at PowerOn
     beside the disk image map. *)
  log_mirror_full -∗
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* ---- the superblock field, read once ---- *)
  pa_add sb 20 ↦₄{dqs} (mword_of_int logstart : mword 32) -∗
  (* ---- the RAW spinlock cells of struct log (&log.lock = &log) ---- *)
  log_addr ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  (* ---- the rest of struct log.  outstanding and committing arrive ZERO:
     initlog never writes them and the invariant needs them zero, which is
     the .bss guarantee for a static object. ---- *)
  l_start ↦₄ v_start -∗
  l_dev ↦₄ v_dev -∗
  l_out ↦₄ (mword_of_int 0 : mword 32) -∗
  l_cmt ↦₄ (mword_of_int 0 : mword 32) -∗
  l_ncommit ↦₄ v_nc -∗
  lh_n_pa ↦₄ v_n -∗
  ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ w : mword 32, lh_block i ↦₄ w) -∗
  (* ---- the FsBlocks material the batch is assembled from ---- *)
  ghost_map_auth (fs_L γfs) 1 L -∗
  ghost_map_auth (fs_dirty γfs) 1 D -∗
  (* the LOG SIDE's dirty halves, over the whole covered range, all false:
     nothing is logged yet *)
  ([∗ set] z ∈ cov, z ↪[fs_dirty γfs]{#(1/2)} false) -∗
  (* the log region's CLIENT halves: the header at the clean-image content,
     the thirty slots at anything *)
  fsblock γfs (log_hdr_bno logstart) bs_hdr -∗
  ([∗ list] i ∈ seq 0 LOGBLOCKS,
     ∃ bs : list (bv 8), fsblock γfs (log_slot_bno logstart i) bs) -∗
  (* THE SLOT POOL, STOCKED.  initlog is where [log_batch]'s pool comes
     from: at n = 0 the batch wants [bslots bn ((LOGBLOCKS - 0) + 2)] =
     32 units, and initlog needs a working pair of its own on top (its
     bread/brelse, and install_trans's contract asks for two even on the
     dead n = 0 path).  The pair comes back; the 32 stay sealed in the
     lock. *)
  bslots bn ((LOGBLOCKS + 2) + 2)%nat -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* the superblock fraction, untouched *)
      pa_add sb 20 ↦₄{dqs} (mword_of_int logstart : mword 32) -∗
      (* only initlog's own working pair: the other 32 are the batch's pool *)
      bslots bn 2 -∗
      (* THE LOG LAYER, BUILT.  Everything else initlog was handed is now
         sealed inside the "log" spinlock's resource. *)
      (∃ γ : log_names, log_ctx γ bn γfs cov logstart dev) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type INITLOG.
  Parameter wp_initlog_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (sb : mword 64)
      (bs_hdr : list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (vlock : mword 32) (vname vcpu : mword 64)
      (v_start v_dev v_nc v_n : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_initlog_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                            cov logstart dev sb bs_hdr L D
                            vlock vname vcpu v_start v_dev v_nc v_n
                            pidv dq dqs m K eb C b.
End INITLOG.
