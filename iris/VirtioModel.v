(* ====================================================================== *)
(* VirtioModel.v                                                           *)
(*                                                                         *)
(* A virtio-mmio (version 2) BLOCK device -- the disk xv6's                 *)
(* kernel/virtio_disk.c drives.  Like DevModel.v (which imports this file   *)
(* and routes the [0x1000_1000, 0x1000_2000) MMIO window here) this file is *)
(* deliberately iris-free.                                                  *)
(*                                                                         *)
(* Two things make this device qualitatively different from the UART and    *)
(* the PLIC, and they drive the whole design of this file:                  *)
(*                                                                         *)
(*  1. It is a BUS MASTER.  Its work is not done through the MMIO registers *)
(*     at all: the registers only tell it where, in the harts' own byte     *)
(*     memory, to find a virtqueue.  The actual disk transfer is DMA -- the *)
(*     device READS descriptors, the available ring and (for a write        *)
(*     request) the data buffer out of RAM, and WRITES the data buffer (for *)
(*     a read request), a status byte and the used ring back into RAM.  So  *)
(*     the autonomous device transition here is a function of the byte      *)
(*     memory, and returns the bytes it wrote: hence                        *)
(*     [virtio_req_step : virtio_state -> mem -> option (virtio_state *     *)
(*     mem_writes)], and hence RiscvLang's [disk_step] carries the memory.  *)
(*                                                                          *)
(*  2. Its MMIO register state SPLITS in two, and the split is load-bearing *)
(*     rather than cosmetic ([virtio_cfg] vs the rest of [virtio_state]):   *)
(*     the CONFIGURATION (queue addresses, queue size, ready/status bits)   *)
(*     is written by the driver and NEVER touched by the device, while the  *)
(*     dynamic part (how far the device has consumed the available ring,    *)
(*     how many used entries it has produced, the interrupt status, the     *)
(*     disk contents) is what an autonomous step advances.  A DMA-footprint *)
(*     obligation stated over the configuration alone (see                  *)
(*     [virtio_dma_ok] in §6) is therefore preserved by every device step   *)
(*     for free, and only a driver's MMIO write has to re-establish it.     *)
(*                                                                          *)
(* Deliberate modelling choices, all of which ADD device behaviours (and so *)
(* only ever make a driver proof harder, never unsound):                    *)
(*                                                                          *)
(*  - QUEUE_NOTIFY is a no-op.  The device polls the available ring on its  *)
(*    own schedule, so it may pick a request up as soon as the driver has   *)
(*    published it -- before the notifying store retires.                   *)
(*  - a request completes ATOMICALLY in one step (data + status + used ring *)
(*    entry + used index in a single transition).  A real device may write  *)
(*    the buffer in pieces, but the used-index bump is what a driver waits  *)
(*    for and it is ordered last either way.                                *)
(*  - DMA is not restricted to bytes that are already present in the byte   *)
(*    memory: a write set simply overrides it.  What actually bounds the    *)
(*    device's reach is the device invariant's DMA lease (WpVirtio.v), not  *)
(*    this file.                                                            *)
(*  - a malformed queue (bad descriptor chain, a request type that is       *)
(*    neither IN nor OUT, a data descriptor whose write flag contradicts    *)
(*    the request type) simply does not step.  That loses LIVENESS only --  *)
(*    a driver that builds such a chain waits forever rather than being     *)
(*    caught -- and never adds a state the real device could not reach.     *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
From Stdlib Require Import FunctionalExtensionality.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Platform geometry, device identity and register offsets.             *)
(*    (QEMU virt board / xv6 memlayout.h: VIRTIO0 = 0x1000_1000.)          *)
(* ---------------------------------------------------------------------- *)

Definition virtio_base : Z := 0x10001000.
Definition virtio_size : Z := 0x1000.

(* the four identification registers the driver checks before it will talk *)
Definition virtio_magic_value : Z := 0x74726976.   (* "virt" *)
Definition virtio_version : Z := 2.                (* non-legacy mmio *)
Definition virtio_blk_device_id : Z := 2.          (* 2 = block device *)
Definition virtio_vendor_id : Z := 0x554d4551.     (* "QEMU" *)

(* THIS DEVICE OFFERS THE TWO WRITE-CACHE FEATURES
   (claude-notes/projects/async-disk.md).  Bit 9 is VIRTIO_BLK_F_FLUSH (which
   QEMU also reads as "write-back allowed") and bit 11 is
   VIRTIO_BLK_F_CONFIG_WCE; together they are the volatile write cache a real
   virtio-blk backend has by default.  Offering them is what makes the
   negotiation MEAN something: [virtio_wce] below reads the DRIVER's answer
   back off the recorded driver-features word, and xv6 answers "no"
   (kernel/virtio_disk.c clears both), which is why xv6's disk is
   writethrough.  Any superset the driver clears would do; these are the two
   that matter, and both stay inside the low 32 bits the MMIO register
   carries. *)
Definition virtio_device_features : Z := Z.lor (Z.shiftl 1 9) (Z.shiftl 1 11).

(* The bits kernel/virtio_disk.c clears before it writes DRIVER_FEATURES:
   RO(5), SCSI(7), FLUSH(9), CONFIG_WCE(11), MQ(12), ANY_LAYOUT(27),
   INDIRECT_DESC(28), EVENT_IDX(29). *)

(* THE NEGOTIATION XV6 PERFORMS, COMPUTED: what the driver writes back is 0.
   This is the pure half of "xv6 declines the cache" -- the WP that walks the
   eight [features &= ~(1 << ...)] statements lands on this word. *)

(* THE HIGH FEATURE WORD.  Feature bits above 31 are reached by selecting
   word 1 with DeviceFeaturesSel, and bit 32 is VIRTIO_F_VERSION_1 -- the bit
   a 1.x driver MUST ack for the transport to be legal.  Offering it is what
   makes a modern negotiation (select 1, read, select 1, ack, FEATURES_OK)
   describable at all; with the two SEL registers undecoded it was a stuck
   machine at the first select (finding 3). *)
Definition virtio_device_features_hi : Z := 1.   (* VIRTIO_F_VERSION_1 *)

(* The largest queue this device supports: the board's, 1024.  A driver may
   program any power of two up to it -- the old model advertised 8 and
   accepted only {1,2,4,8}, which is finding 1. *)
Definition virtio_queue_num_max : Z := 1024.

(* register offsets within the window (all registers are 32 bits wide) *)
Definition vio_off_magic_value : Z := 0x000.
Definition vio_off_version : Z := 0x004.
Definition vio_off_device_id : Z := 0x008.
Definition vio_off_vendor_id : Z := 0x00c.
Definition vio_off_device_features : Z := 0x010.
Definition vio_off_driver_features : Z := 0x020.
Definition vio_off_queue_sel : Z := 0x030.
Definition vio_off_queue_num_max : Z := 0x034.
Definition vio_off_queue_num : Z := 0x038.
Definition vio_off_queue_ready : Z := 0x044.
Definition vio_off_queue_notify : Z := 0x050.
Definition vio_off_interrupt_status : Z := 0x060.
Definition vio_off_interrupt_ack : Z := 0x064.
Definition vio_off_status : Z := 0x070.
Definition vio_off_queue_desc_low : Z := 0x080.
Definition vio_off_queue_desc_high : Z := 0x084.
Definition vio_off_driver_desc_low : Z := 0x090.
Definition vio_off_driver_desc_high : Z := 0x094.
Definition vio_off_device_desc_low : Z := 0x0a0.
Definition vio_off_device_desc_high : Z := 0x0a4.
(* ...and the ones the model used to answer [None] for (findings 3, 13, 14) *)
Definition vio_off_device_features_sel : Z := 0x014.
Definition vio_off_driver_features_sel : Z := 0x024.
Definition vio_off_shm_sel : Z := 0x0ac.
Definition vio_off_shm_len_low : Z := 0x0b0.
Definition vio_off_shm_len_high : Z := 0x0b4.
Definition vio_off_shm_base_low : Z := 0x0b8.
Definition vio_off_shm_base_high : Z := 0x0bc.
Definition vio_off_queue_reset : Z := 0x0c0.
Definition vio_off_config_generation : Z := 0x0fc.
(* the DEVICE-SPECIFIC configuration space, which for virtio-blk starts with
   the 64-bit capacity in sectors *)
Definition vio_off_config : Z := 0x100.
Definition vio_off_config_capacity_low : Z := 0x100.
Definition vio_off_config_capacity_high : Z := 0x104.
Definition virtio_window_size : Z := 0x200.

(* device-status bits (virtio_config.h) *)

(* descriptor flags *)
Definition vring_desc_f_next : Z := 1.
Definition vring_desc_f_write : Z := 2.

(* block-request types (virtio spec §5.2) *)
Definition virtio_blk_t_in : Z := 0.    (* read the disk *)
Definition virtio_blk_t_out : Z := 1.   (* write the disk *)
(* ...and the barrier a write-back cache needs: make everything durable.
   Recognised (status OK, no data transfer) rather than UNSUPP, because the
   device now HAS a cache to flush (claude-notes/projects/async-disk.md). *)
Definition virtio_blk_t_flush : Z := 4.

(* the interrupt-status bit for "the device used some buffers" *)
Definition vio_isr_used_buffer : Z := 1.

(* virtqueue layout, in bytes *)
Definition vq_desc_size : Z := 16.        (* addr:8 len:4 flags:2 next:2 *)
Definition vq_avail_ring_off : Z := 4.    (* after flags:2 idx:2 *)
Definition vq_used_ring_off : Z := 4.     (* after flags:2 idx:2 *)
Definition vq_used_elem_size : Z := 8.    (* id:4 len:4 *)
Definition vq_idx_off : Z := 2.           (* the idx field of either ring *)

(* a disk sector *)
Definition virtio_sector_size : Z := 512.

(* the status bytes a block request can complete with (spec 5.2.6) *)
Definition virtio_blk_s_ok : Z := 0.
Definition virtio_blk_s_unsupp : Z := 2.

(* The queue sizes this device accepts: the powers of two up to
   [virtio_queue_num_max].  A QUEUE_NUM write of anything else is REFUSED
   (see [virtio_write]) rather than silently accepted -- the ring geometry
   below divides by this number, and a device that let the driver pick an
   illegal one would be modelling hardware that does not exist. *)
(* A LEGAL QUEUE SIZE: a power of two, at least one, no larger than the
   device's maximum.  (The old model accepted {1,2,4,8} because that is what
   its [virtio_queue_num_max] = 8 allowed; the board's queue is 1024.) *)
Definition vq_size_ok (n : Z) : bool :=
  (0 <? n) && (n <=? virtio_queue_num_max) && (Z.land n (n - 1) =? 0).

(* ---------------------------------------------------------------------- *)
(* 1. The device state.                                                    *)
(* ---------------------------------------------------------------------- *)

(* The DRIVER-OWNED half: written only by MMIO stores, never by the device.
   Everything the DMA footprint of a request depends on lives here, which is
   what makes [virtio_dma_ok] (§6) survive an autonomous step for free. *)
Record virtio_cfg := VirtioCfg {
  vc_status : bv 32;      (* device status (ACKNOWLEDGE/DRIVER/FEATURES_OK/DRIVER_OK) *)
  vc_dfeat  : bv 32;      (* the driver-features word 0, recorded *)
  vc_qsel   : bv 32;      (* selected queue (only queue 0 exists) *)
  vc_qnum   : bv 32;      (* driver-programmed queue size *)
  vc_ready  : bool;       (* queue 0 ready *)
  vc_desc   : Arch.pa;    (* descriptor table base *)
  vc_avail  : Arch.pa;    (* available ring base (driver -> device) *)
  vc_used   : Arch.pa;    (* used ring base (device -> driver) *)
  (* THE WORD SELECTORS.  Feature bits come in 32-bit words and the transport
     reaches the upper ones through a selector written first, so each side of
     the negotiation is TWO registers: the select and the data.  All three
     selectors below are ordinary storage the driver writes and the device
     reads back through whichever data register they gate. *)
  vc_devfsel : bv 32;     (* DeviceFeaturesSel: which word a read reports *)
  vc_dfsel   : bv 32;     (* DriverFeaturesSel: which word a write acks *)
  vc_dfeat1  : bv 32;     (* the driver-features word 1 (VERSION_1 lives here) *)
  vc_shmsel  : bv 32;     (* SHMSel: which shared-memory region -- none exist *)
}.

Record virtio_state := VirtioState {
  v_cfg      : virtio_cfg;
  v_isr      : bv 32;        (* interrupt status; nonzero drives the irq line *)
  (* THE REQUEST LIFECYCLE, IN TWO PHASES (claude-notes/design/virtio-driver.md).
     QEMU keeps these separate and so must we, because xv6's safety depends
     on the difference:

       POP -- the device takes the next available-ring entry.  This is
       STRICTLY IN ORDER ([virtqueue_pop] increments [last_avail_idx] by
       one); [v_seen] is that index, and the positions the driver has
       published but the device has not popped are exactly the interval
       [[v_seen, avail_idx)].  In-order popping is what lets xv6 reuse the
       ring slot [idx % NUM]: the entry it overwrites belonged to a position
       the device is provably past.

       COMPLETE -- the device pushes a used-ring element for a request it
       popped earlier.  This may happen in ANY order among the requests in
       flight (tools/vtest/README.md finding 5), which is what the two
       captures in vtest-rocq/DiskOrder.v show and what xv6's interrupt
       handler is written for.

     [v_inflight] is the set BETWEEN the two: popped, not yet completed. *)
  v_seen     : bv 16;        (* the POP index: entries before it are taken *)
  v_inflight : gset (bv 16); (* popped, not yet completed -- any may finish *)
  v_used_idx : bv 16;        (* used-ring index produced so far *)
  v_disk     : Z -> bv 8;    (* the DURABLE disk image, byte-addressed *)
  (* THE VOLATILE WRITE CACHE (claude-notes/projects/async-disk.md).  A disk
     write does not reach [v_disk] when the request completes; it reaches
     this map, keyed by ABSOLUTE SECTOR NUMBER, and drains to [v_disk] one
     sector at a time in ANY order, at steps of the device's own choosing.
     [virtio_reset] DROPS it -- that is the data loss of a power cycle, for
     free.  A write is atomic at the 512-byte sector and not at the
     1024-byte block xv6 works in
     (claude-notes/completed/sector-atomic-disk.md): the drain is where that
     tearing lives now. *)
  v_cache    : gmap Z (list (bv 8));
  (* ...and WHICH request's data has been CAPTURED into the cache.  A write
     request is served in two halves -- capture (read the driver's buffer,
     once) and completion -- because in write-back mode the buffer belongs to
     the driver again the moment the request completes, so the device must own
     the bytes before it says so.  It is a POSITION and not a flag because
     the served order is free: the capture belongs to the request whose
     payload is latched, whichever one the device picks up next.  ONE latch,
     so a second write waits for the first to complete -- a restriction on
     the DEVICE's internal concurrency, not on any driver, and every
     completion order is still reachable through it. *)
  v_taken    : option (bv 16);
  (* THE BACKING DEVICE'S SIZE, in 512-byte sectors, reported through the
     configuration space at offset 0x100.  [v_disk] is a TOTAL function, so
     the model's image has no edge of its own: the capacity is a separate
     fact about the medium the board attached, which is why it is a field
     rather than something derived.  A reset keeps it -- the configuration
     goes, the disk does not. *)
  v_cap      : bv 64;
}.

(* replace the dynamic part, keeping the configuration *)
Definition set_vcfg (v : virtio_state) (c : virtio_cfg) : virtio_state :=
  VirtioState c (v_isr v) (v_seen v) (v_inflight v) (v_used_idx v) (v_disk v) (v_cache v) (v_taken v) (v_cap v).

(* THE DISK IMAGE'S GHOST VIEW (claude-notes/design/crash.md).  The image is
   a TOTAL function, while its ghost mirror is a partial map -- a fragment
   exists only for offsets somebody minted, exactly as [mem_view] relates
   the byte memory to its ghost map.  The predicate lives HERE, in the
   iris-free model, rather than with the points-to it serves
   ([DiskPtsto.v]): the auth it ties rides in [RiscvPtsto.era_interp],
   which is below the driver protocol. *)
Definition disk_view (dmap : gmap Z (bv 8)) (dk : Z -> bv 8) : Prop :=
  forall (o : Z) (b : bv 8), dmap !! o = Some b -> dk o = b.

Definition zero32 : bv 32 := Z_to_bv 32 0.
Definition zero16 : bv 16 := Z_to_bv 16 0.
Definition zero64 : Arch.pa := Z_to_bv 64 0.

(* the queue is live: the driver has published addresses, sized the queue,
   flipped QUEUE_READY and set DRIVER_OK. *)
Definition virtio_driver_ok (c : virtio_cfg) : bool :=
  Z.testbit (bv_unsigned (vc_status c)) 2.

Definition virtio_live (c : virtio_cfg) : bool :=
  vc_ready c && virtio_driver_ok c && vq_size_ok (bv_unsigned (vc_qnum c)).

(* THE CACHE MODE, a pure function of the NEGOTIATED feature word -- no new
   device field (claude-notes/projects/async-disk.md §1).  QEMU samples the
   backend's write-cache setting at DRIVER_OK from whether
   VIRTIO_BLK_F_FLUSH (bit 9) was negotiated: negotiated -> write-BACK (a
   write completes when it is merely cached, and VIRTIO_BLK_T_FLUSH is what
   makes it durable); declined -> writeTHROUGH (a write completes only once
   it is on the medium).  [vc_dfeat] is driver-written and device-never-
   touched, and the driver cannot rewrite it without a reset, so reading it
   off the live configuration is exactly QEMU's sampling.  CONFIG_WCE's
   [writeback] config field stays unmodelled -- xv6 declines that bit too, so
   it never writes there. *)
Definition virtio_wce (c : virtio_cfg) : bool :=
  Z.testbit (bv_unsigned (vc_dfeat c)) 9.

(* a driver that negotiated NOTHING has declined the cache *)

(* the device's (level) interrupt output: asserted while the interrupt-status
   register is nonzero, i.e. until the driver acknowledges. *)
Definition virtio_irq (v : virtio_state) : bool :=
  negb (bv_unsigned (v_isr v) =? 0).

(* ---------------------------------------------------------------------- *)
(* 2. MMIO: one 32-bit register access.                                    *)
(*                                                                         *)
(*    virtio-mmio has no read-sensitive register, so a read is a PURE       *)
(*    observation and [virtio_read] returns a value only (unlike            *)
(*    [uart_read], whose RHR pops the receive FIFO).  Offsets the xv6       *)
(*    driver never touches -- and writes to read-only registers -- are      *)
(*    [None] = the machine is STUCK, so a WP certifies the driver stays     *)
(*    inside the modelled subset.                                          *)
(* ---------------------------------------------------------------------- *)

Definition virtio_read (v : virtio_state) (off : Z) : option (bv 32) :=
  let c := v_cfg v in
  if off =? vio_off_magic_value then Some (Z_to_bv 32 virtio_magic_value)
  else if off =? vio_off_version then Some (Z_to_bv 32 virtio_version)
  else if off =? vio_off_device_id then Some (Z_to_bv 32 virtio_blk_device_id)
  else if off =? vio_off_vendor_id then Some (Z_to_bv 32 virtio_vendor_id)
  (* DEVICE FEATURES: the word DeviceFeaturesSel selects.  Word 0 is what
     this device offers, word 1 carries VIRTIO_F_VERSION_1, and every other
     selection reads zero -- there are no bits up there. *)
  else if off =? vio_off_device_features then
    Some (Z_to_bv 32 (if bv_unsigned (vc_devfsel c) =? 0 then virtio_device_features
                      else if bv_unsigned (vc_devfsel c) =? 1 then virtio_device_features_hi
                      else 0))
  (* the two per-queue registers report on the SELECTED queue, and queue 0 is
     the only one this device has: any other selection reads as absent. *)
  else if off =? vio_off_queue_num_max then
    Some (Z_to_bv 32 (if bv_unsigned (vc_qsel c) =? 0 then virtio_queue_num_max
                      else 0))
  else if off =? vio_off_queue_ready then
    Some (Z_to_bv 32 (if (bv_unsigned (vc_qsel c) =? 0) && vc_ready c then 1
                      else 0))
  else if off =? vio_off_interrupt_status then Some (v_isr v)
  else if off =? vio_off_status then Some (vc_status c)
  (* QUEUE RESET reads 0: this device does not offer VIRTIO_F_RING_RESET, so
     no queue is ever in the reset state. *)
  else if off =? vio_off_queue_reset then Some zero32
  (* THE SHARED-MEMORY REGIONS, of which this device has NONE.  The transport
     says a region that does not exist reports a length of all-ones, and the
     selector is ordinary storage, so every selection reads the same. *)
  else if (off =? vio_off_shm_len_low) || (off =? vio_off_shm_len_high)
          || (off =? vio_off_shm_base_low) || (off =? vio_off_shm_base_high)
  then Some (Z_to_bv 32 0xffffffff)
  (* CONFIG GENERATION: the config space of this device never changes under
     the driver's feet, so the generation is always 0 and a driver's
     read-check-reread loop always agrees with itself. *)
  else if off =? vio_off_config_generation then Some zero32
  (* THE CONFIGURATION SPACE.  virtio-blk's first field is the 64-bit
     CAPACITY in sectors, and it is not feature-gated -- every virtio-blk
     device has one.  The fields after it belong to features this device does
     not offer (size_max, seg_max, geometry, ...), so they read zero: a
     driver may only look at a config field whose feature it negotiated. *)
  else if off =? vio_off_config_capacity_low then
    Some (bv_extract 0 32 (v_cap v))
  else if off =? vio_off_config_capacity_high then
    Some (bv_extract 32 32 (v_cap v))
  else if (vio_off_config <=? off) && (off <? virtio_window_size)
          && (off mod 4 =? 0)
  then Some zero32
  else None.

(* splice a 32-bit half into a 64-bit queue address *)
Definition set_lo (a : Arch.pa) (w : bv 32) : Arch.pa :=
  Z_to_bv 64 (Z.lor (bv_unsigned w)
                    (Z.shiftl (Z.shiftr (bv_unsigned a) 32) 32)).
Definition set_hi (a : Arch.pa) (w : bv 32) : Arch.pa :=
  Z_to_bv 64 (Z.lor (Z.land (bv_unsigned a) 0xffffffff)
                    (Z.shiftl (bv_unsigned w) 32)).

(* The driver programs each 64-bit queue address as two 32-bit halves, so the
   configuration it ends up with is only recognisable as "the page I kalloc'd"
   modulo reassembling them.  [set_lo_hi_id] is that reassembly, and it is what
   lets a driver spec name the queue addresses directly instead of leaking the
   half-splitting into its postcondition. *)
Definition lo32 (a : Arch.pa) : bv 32 := bv_extract 0 32 a.
Definition hi32 (a : Arch.pa) : bv 32 := bv_extract 32 32 a.

Lemma lor_split32 (x : Z) :
  0 <= x -> Z.lor (x `mod` 4294967296) (Z.shiftl (Z.shiftr x 32) 32) = x.
Proof.
  intro Hx. apply Z.bits_inj_iff'. intros i Hi.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  change 4294967296 with (2 ^ 32).
  destruct (decide (i < 32)) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite (Z.testbit_neg_r (Z.shiftr x 32) (i - 32)) by lia.
    apply orb_false_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite orb_false_l, Z.shiftr_spec by lia.
    f_equal. lia.
Qed.

(* A device RESET (status <- 0) drops the whole configuration and all queue
   progress; the disk image, of course, survives. *)
Definition virtio_cfg0 : virtio_cfg :=
  VirtioCfg zero32 zero32 zero32 zero32 false zero64 zero64 zero64
              zero32 zero32 zero32 zero32.

Definition virtio_reset (v : virtio_state) : virtio_state :=
  VirtioState virtio_cfg0 zero32 zero16 ∅ zero16 (v_disk v) ∅ None (v_cap v).

(* WHAT A RESET DEVICE SATISFIES.  These are the four facts a boot client owes
   [VirtioProto.disk_ghosts_alloc] and [WpUart.dev_inv_alloc] about the device
   it allocates the protocol invariant over, and they hold of ANY reset device
   -- the disk image is the only field [virtio_reset] keeps, and none of the
   four mentions it.  (The [boot_facts] of a power-on say exactly
   [dvirtio = virtio_reset v0] for some [v0], so this is what the crash-layer
   boot client reads them off.) *)
Lemma virtio_reset_not_live (v : virtio_state) :
  virtio_live (v_cfg (virtio_reset v)) = false.
Proof. reflexivity. Qed.

Lemma virtio_reset_seen (v : virtio_state) : v_seen (virtio_reset v) = zero16.
Proof. reflexivity. Qed.

Lemma virtio_reset_used_idx (v : virtio_state) :
  v_used_idx (virtio_reset v) = zero16.
Proof. reflexivity. Qed.

(* A POWER CYCLE DROPS THE VOLATILE CACHE.  Whatever had already drained is
   on the disk ([v_disk] survives), and everything still cached is GONE --
   which is the write-back cache's data loss, obtained for free from the fact
   that [virtio_reset] keeps only [v_disk].  With a writethrough driver
   nothing is ever cached across a completion, so nothing is ever lost; that
   is the content of [virtio_wt_inv] (section 6c). *)
Lemma virtio_reset_cache (v : virtio_state) : v_cache (virtio_reset v) = ∅.
Proof. reflexivity. Qed.

Lemma virtio_reset_inflight (v : virtio_state) : v_inflight (virtio_reset v) = ∅.
Proof. reflexivity. Qed.

Lemma virtio_reset_taken (v : virtio_state) : v_taken (virtio_reset v) = None.
Proof. reflexivity. Qed.

(* ...and a reset device has declined the cache, vacuously *)
Lemma virtio_reset_wce (v : virtio_state) :
  virtio_wce (v_cfg (virtio_reset v)) = false.
Proof. by vm_compute. Qed.

Definition virtio_write (v : virtio_state) (off : Z) (w : bv 32)
  : option virtio_state :=
  let c := v_cfg v in
  (* a per-queue write names the SELECTED queue, and queue 0 is the only one
     this device has.  A write with any other selection is IGNORED -- which
     is what the hardware does, and what the model used to REFUSE (finding
     16).  Refusing made the geometry legal by construction, but at the price
     of a driver that touches queue 1 having no model execution at all; the
     geometry is kept by [virtio_live]'s own conditions instead. *)
  let qsel0 := bv_unsigned (vc_qsel c) =? 0 in
  if off =? vio_off_status then
    (* writing 0 is the reset command *)
    if bv_unsigned w =? 0 then Some (virtio_reset v)
    else Some (set_vcfg v (VirtioCfg w (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                     (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                     (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_device_features_sel then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                w (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_driver_features_sel then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                (vc_devfsel c) w (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_driver_features then
    (* the ack lands in the word DriverFeaturesSel names; a selection with no
       bits behind it is accepted and goes nowhere, as on the hardware *)
    if bv_unsigned (vc_dfsel c) =? 0 then
      Some (set_vcfg v (VirtioCfg (vc_status c) w (vc_qsel c) (vc_qnum c)
                                  (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                  (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
    else if bv_unsigned (vc_dfsel c) =? 1 then
      Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                  (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                  (vc_devfsel c) (vc_dfsel c) w (vc_shmsel c)))
    else Some v
  else if off =? vio_off_queue_sel then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) w (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_shm_sel then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) w))
  else if off =? vio_off_queue_num then
    (* an ILLEGAL SIZE is still refused: a queue whose size is not a power of
       two no larger than the maximum is a configuration no real device
       accepts, and refusing at the write is what keeps the geometry legal by
       construction rather than leaving the device to cope with it. *)
    if negb qsel0 then Some v else
    if negb (vq_size_ok (bv_unsigned w)) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) w
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_queue_ready then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (negb (bv_unsigned w =? 0))
                                (vc_desc c) (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_queue_notify then
    (* a hint only: this device polls the available ring itself.  The value is
       the queue number, and a queue that does not exist is ignored. *)
    Some v
  else if off =? vio_off_interrupt_ack then
    Some (VirtioState c (Z_to_bv 32 (Z.land (bv_unsigned (v_isr v))
                                            (Z.lnot (bv_unsigned w)))) (v_seen v) (v_inflight v) (v_used_idx v) (v_disk v) (v_cache v) (v_taken v) (v_cap v))
  else if off =? vio_off_queue_desc_low then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_lo (vc_desc c) w)
                                (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_queue_desc_high then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_hi (vc_desc c) w)
                                (vc_avail c) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_driver_desc_low then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_lo (vc_avail c) w) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_driver_desc_high then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_hi (vc_avail c) w) (vc_used c)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_device_desc_low then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c)
                                (set_lo (vc_used c) w)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else if off =? vio_off_device_desc_high then
    if negb qsel0 then Some v else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c)
                                (set_hi (vc_used c) w)
                                (vc_devfsel c) (vc_dfsel c) (vc_dfeat1 c) (vc_shmsel c)))
  else None.

(* -- MMIO totality, for the offsets the xv6 driver names --

   [virtio_disk_init] reads MAGIC/VERSION/DEVICE_ID/VENDOR_ID/
   DEVICE_FEATURES/STATUS/QUEUE_READY/QUEUE_NUM_MAX and [virtio_disk_intr]
   reads INTERRUPT_STATUS; those nine are exactly the reads this device
   services.  A driver proof under a contents-agnostic device invariant
   cannot supply the result equation itself, so it needs these to conjure
   one. *)

(* A write is accepted when the register exists AND the driver has put the
   device in a state where the write means something: the per-queue registers
   need queue 0 selected, QUEUE_NUM needs a legal size, QUEUE_NOTIFY needs an
   existing queue number.  Anything else is stuck -- deliberately, so that a
   driver proof has to establish these rather than have the device paper over
   them (see the header). *)
(* WHICH WRITES THE DEVICE ANSWERS.  Only two things are refused now: an
   illegal QUEUE SIZE (a power of two up to the maximum, or the geometry is
   one no real device accepts) and an offset this device has no register at.
   A per-queue write with a foreign selection is ACCEPTED and ignored, and so
   is a notification naming a queue that does not exist -- finding 16, where
   the model used to be stuck at both. *)



(* The two MMIO writes the driver performs while the queue is LIVE -- the
   completion acknowledgement in [virtio_disk_intr] and the queue kick in
   [virtio_disk_rw] -- leave the configuration alone.  So they cannot
   invalidate a DMA lease (WpVirtio.virtio_lease_cfg), which is what lets the
   steady-state driver path run without re-establishing one. *)




Lemma mod_shiftr_id (x : Z) :
  0 <= x -> x < 18446744073709551616 ->
  (x ≫ 32) `mod` 4294967296 = x ≫ 32.
Proof.
  intros H0 H1. apply Z.mod_small.
  rewrite Z.shiftr_div_pow2 by (intro Hc; discriminate).
  change (2 ^ 32) with 4294967296. split.
  - apply Z.div_pos; [exact H0 | reflexivity].
  - apply Z.div_lt_upper_bound; [reflexivity|].
    change (4294967296 * 4294967296) with 18446744073709551616. exact H1.
Qed.

(* Writing an address low half then high half reassembles the address. *)
Lemma set_lo_hi_id (a : Arch.pa) : set_hi (set_lo zero64 (lo32 a)) (hi32 a) = a.
Proof.
  pose proof (bv_unsigned_in_range 64 a) as [Halo Hahi].
  unfold bv_modulus in Hahi. change (Z.of_N 64) with 64 in Hahi.
  change (2 ^ 64) with 18446744073709551616 in Hahi.
  apply bv_eq. unfold set_hi, set_lo, lo32, hi32, zero64.
  rewrite !Z_to_bv_unsigned, !bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N 0) with 0. change (Z.of_N 32) with 32.
  change (Z.of_N 64) with 64.
  change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  rewrite Z.shiftr_0_r.
  assert (Hz : Z.shiftl (Z.shiftr (0 `mod` 18446744073709551616) 32) 32 = 0)
    by reflexivity.
  rewrite Hz, Z.lor_0_r.
  (* the low half survives the 64-bit wrap and the 32-bit mask *)
  pose proof (Z.mod_pos_bound (bv_unsigned a) 4294967296 ltac:(lia)) as [Hl1 Hl2].
  rewrite (Z.mod_small (bv_unsigned a `mod` 4294967296) 18446744073709551616)
    by lia.
  change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones by lia. change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small (bv_unsigned a `mod` 4294967296) 4294967296) by lia.
  (* the high half needs no mask either *)
  rewrite (mod_shiftr_id (bv_unsigned a) Halo Hahi).
  rewrite (lor_split32 (bv_unsigned a) Halo).
  apply Z.mod_small. split; [exact Halo | exact Hahi].
Qed.

(* Record eta, so a fact stated over the split state applies to a state that
   arrived whole (as the device thread's does). *)
Lemma virtio_state_eta (v : virtio_state) :
  v = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v) (v_used_idx v) (v_disk v) (v_cache v) (v_taken v) (v_cap v).
Proof. by destruct v. Qed.

(* No MMIO write touches the disk image -- not even the reset command. *)
Lemma virtio_write_disk (v : virtio_state) (off : Z) (w : bv 32) (v' : virtio_state) :
  virtio_write v off w = Some v' -> v_disk v' = v_disk v.
Proof.
  unfold virtio_write. cbv zeta.
  (* Peel the decode one guard at a time -- each [destruct] leaves the arm
     and the rest of the chain, so this is linear, not exponential.  Every
     arm answers [Some] of a state built from [v]'s own disk (the ignored
     per-queue writes give back [v] itself), and the only [None] left is the
     offset this device has no register at. *)
  repeat (match goal with
          | |- (if ?b then _ else _) = Some _ -> _ => destruct b
          end);
    first [ discriminate | intro H; injection H as <-; reflexivity ].
Qed.

(* ... and the two writes the driver makes while the queue is LIVE leave the
   write cache alone too, so a transfer in flight survives them.  (The RESET
   command does NOT: it drops the whole cache -- see [virtio_reset_cache].) *)


(* AN MMIO WRITE IS EITHER THE RESET COMMAND OR LEAVES THE CACHE ALONE -- the
   totality form, which is what the writethrough invariant's preservation
   under a CONFIGURATION write runs on (section 6c): a reset empties the
   cache, and every other register write does not touch it. *)

(* ---------------------------------------------------------------------- *)
(* 3. DMA primitives: byte-list reads and writes over the harts' memory.   *)
(*                                                                         *)
(*    RiscvModelBytes' [read_bytes]/[write_bytes] handle a single           *)
(*    little-endian machine word, which is what the descriptor and ring     *)
(*    FIELDS are.  A data transfer is a whole block, so it needs the        *)
(*    byte-LIST forms; they are the same [pa_add]-indexed lookups.          *)
(* ---------------------------------------------------------------------- *)

Definition read_byte_list (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : nat)
  : option (list (bv 8)) :=
  mapM (fun j : nat => mm !! pa_add pa j) (seq 0 n).

Definition write_byte_list (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) : gmap Arch.pa (bv 8) :=
  foldr (fun jb acc => <[ pa_add pa (fst jb) := snd jb ]> acc) mm
        (imap (fun j b => (j, b)) bs).

(* field reads, at the three widths the virtqueue structures use *)

(* [pa_add] with a Z displacement (all the layout arithmetic is in Z) *)
Definition pa_off (a : Arch.pa) (z : Z) : Arch.pa := pa_add a (Z.to_nat z).

(* -- the disk image -- *)

Definition disk_read (dk : Z -> bv 8) (off : Z) (n : nat) : list (bv 8) :=
  (fun j : nat => dk (off + Z.of_nat j)) <$> seq 0 n.

Definition disk_write (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) : Z -> bv 8 :=
  fun a => if off <=? a then
             match bs !! Z.to_nat (a - off) with
             | Some b => b
             | None => dk a
             end
           else dk a.

(* the disk is a memory: reading back what was just written yields it *)
Lemma disk_read_write (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) :
  disk_read (disk_write dk off bs) off (length bs) = bs.
Proof.
  unfold disk_read, disk_write.
  apply list_eq. intro i. rewrite list_lookup_fmap.
  destruct (decide (i < length bs)%nat) as [Hlt|Hge].
  - rewrite (lookup_seq_lt 0 (length bs) i Hlt). cbn [fmap option_fmap option_map].
    cbv beta. replace (0 + i)%nat with i by lia.
    destruct (lookup_lt_is_Some_2 bs i Hlt) as [b Hb].
    assert (Hle : off <=? off + Z.of_nat i = true) by (apply Z.leb_le; lia).
    rewrite Hle, Z.add_simpl_l, Nat2Z.id, Hb. reflexivity.
  - rewrite (lookup_seq_ge 0 (length bs) i) by lia. cbn [fmap option_fmap option_map].
    symmetry. apply lookup_ge_None_2. lia.
Qed.

(* A byte outside the written range reads through. *)
Lemma disk_write_out (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) (a : Z) :
  a < off \/ off + Z.of_nat (length bs) <= a ->
  disk_write dk off bs a = dk a.
Proof.
  intros [Hlt|Hge]; unfold disk_write.
  - rewrite (proj2 (Z.leb_gt off a)); [reflexivity|lia].
  - destruct (off <=? a) eqn:Hle; [|reflexivity].
    rewrite (lookup_ge_None_2 bs (Z.to_nat (a - off))); [reflexivity|].
    apply Z.leb_le in Hle. lia.
Qed.

(* -- THE WRITE IDENTITY of one completed request (claude-notes/design/    *)
(*    fs-log.md stage 4 phase C2a).                                         *)
(*                                                                          *)
(* The crash predicate is INDEXED by the disk image, so the write permit a  *)
(* client deposits must say WHICH image the completion will move it to.     *)
(* [disk_wr] is exactly that, as pure data the request slot can carry:      *)
(* [None] for a request that moves no disk byte (a READ), [Some (off, bs)]  *)
(* for one that writes [bs] at [off].  Keeping it an OPTION rather than a   *)
(* degenerate write is what keeps a READ's permit FREE -- [wr_apply None]   *)
(* is the identity ON THE NOSE, so [▷ Pc dk ==∗ ▷ Pc (wr_apply None dk)]    *)
(* is provable for an ARBITRARY crash predicate and every read caller's     *)
(* statement is unchanged.  (A [Some (0, [])] encoding would need funext to *)
(* be the identity, and then reads would not be free.)                      *)
Definition disk_wr : Type := option (Z * list (bv 8)).

Definition wr_apply (w : disk_wr) (dk : Z -> bv 8) : Z -> bv 8 :=
  match w with
  | None => dk
  | Some ob => disk_write dk ob.1 ob.2
  end.

Lemma wr_apply_none (dk : Z -> bv 8) : wr_apply None dk = dk.
Proof. reflexivity. Qed.

(* -- SECTOR GRANULARITY (claude-notes/completed/sector-atomic-disk.md) --

   A disk write is atomic at the SECTOR (512 bytes) and NOT at the 1024-byte
   BLOCK xv6 works in, so a crash can leave one sector of a block written and
   the other not.  The device therefore lands a request's data one sector per
   autonomous step (section 6), and the block-sized [disk_wr] a client
   deposits its permit at is CUT into per-sector writes here.

   [wr_sector w i] is sector [i] of [w]: the 512 bytes of [w]'s payload at
   payload offset [512*i], addressed at [w]'s own offset plus the same
   displacement.  [wr_sector None i = None] keeps a READ's permit free
   exactly as [wr_apply None] does.  The two facts the device layer runs on
   are [wr_sector_comm] (distinct sectors of one write commute, so the device
   may land them in ANY order) and [wr_fold_all] (landing every sector -- in
   any order, with repetitions allowed -- IS the whole write). *)

Definition virtio_sector_bytes : nat := 512%nat.

Lemma virtio_sector_size_bytes :
  virtio_sector_size = Z.of_nat virtio_sector_bytes.
Proof. reflexivity. Qed.

(* how many sectors an [n]-byte transfer occupies: ceil (n / 512).  A partial
   last sector is a sector of its own; nothing in xv6 sends one (BSIZE = 2
   sectors), but the model must not silently drop its bytes. *)
Definition sector_count (n : nat) : nat :=
  Nat.div (n + (virtio_sector_bytes - 1))%nat virtio_sector_bytes.

Lemma sector_count_cover (n : nat) :
  (n <= virtio_sector_bytes * sector_count n)%nat.
Proof.
  unfold sector_count.
  pose proof (Nat.div_mod (n + (virtio_sector_bytes - 1))%nat virtio_sector_bytes
                ltac:(unfold virtio_sector_bytes; lia)) as Hdm.
  pose proof (Nat.mod_upper_bound (n + (virtio_sector_bytes - 1))%nat
                virtio_sector_bytes
                ltac:(unfold virtio_sector_bytes; lia)) as Hlt.
  unfold virtio_sector_bytes in Hdm, Hlt |- *. lia.
Qed.

(* the sector an offset falls in, as bounds *)
Lemma sector_of_bounds (d : nat) :
  (virtio_sector_bytes * Nat.div d virtio_sector_bytes <= d
   < virtio_sector_bytes * Nat.div d virtio_sector_bytes
     + virtio_sector_bytes)%nat.
Proof.
  pose proof (Nat.div_mod d virtio_sector_bytes
                ltac:(unfold virtio_sector_bytes; lia)) as Hdm.
  pose proof (Nat.mod_upper_bound d virtio_sector_bytes
                ltac:(unfold virtio_sector_bytes; lia)) as Hlt.
  unfold virtio_sector_bytes in Hdm, Hlt |- *. lia.
Qed.

(* every byte offset of an [n]-byte transfer lies in one of its sectors *)
Lemma sector_count_lt (n i : nat) :
  (i < n)%nat -> (Nat.div i virtio_sector_bytes < sector_count n)%nat.
Proof.
  intro Hi. pose proof (sector_count_cover n) as Hcov.
  pose proof (sector_of_bounds i) as Hb.
  unfold virtio_sector_bytes in Hcov, Hb |- *. lia.
Qed.

Definition wr_nsectors (w : disk_wr) : nat :=
  match w with
  | None => 0%nat
  | Some ob => sector_count (length ob.2)
  end.

Definition wr_sector (w : disk_wr) (i : nat) : disk_wr :=
  match w with
  | None => None
  | Some ob =>
      Some (ob.1 + virtio_sector_size * Z.of_nat i,
            take virtio_sector_bytes (drop (virtio_sector_bytes * i)%nat ob.2))
  end.

(* A READ has no sectors and no permit: the read side of the driver is
   unaffected by any of this. *)
Lemma wr_sector_none (i : nat) : wr_sector None i = None.
Proof. reflexivity. Qed.


(* -- pointwise facts about [disk_write], which is where all of this is
      actually proved (the function equalities below are these plus funext) -- *)

(* the byte a write lands, at an address inside its range *)
Lemma disk_write_in (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) (a : Z)
    (b : bv 8) :
  off <= a -> bs !! Z.to_nat (a - off) = Some b -> disk_write dk off bs a = b.
Proof.
  intros Hle Hb. unfold disk_write.
  rewrite (proj2 (Z.leb_le off a) Hle), Hb. reflexivity.
Qed.

(* a write is determined, at each address, by the underlying image ONLY
   where it does not itself land a byte *)
Lemma disk_write_agree (dk dk' : Z -> bv 8) (off : Z) (bs : list (bv 8))
    (a : Z) :
  (a < off \/ off + Z.of_nat (length bs) <= a -> dk a = dk' a) ->
  disk_write dk off bs a = disk_write dk' off bs a.
Proof.
  intro H. unfold disk_write. destruct (off <=? a) eqn:E.
  - destruct (bs !! Z.to_nat (a - off)) eqn:Hb; [reflexivity|].
    apply H. right. apply lookup_ge_None in Hb.
    apply Z.leb_le in E. lia.
  - apply H. left. apply Z.leb_gt in E. lia.
Qed.

Lemma disk_write_nil (dk : Z -> bv 8) (off : Z) : disk_write dk off [] = dk.
Proof.
  apply functional_extensionality. intro a.
  apply disk_write_out. cbn [length]. lia.
Qed.

(* THE COMMUTATION.  Two writes to DISJOINT ranges commute -- which is what
   lets the device land a request's sectors in ANY order. *)

(* -- the geometry of one sector of a write -- *)

Lemma sector_chunk_len (bs : list (bv 8)) (i : nat) :
  (length (take virtio_sector_bytes (drop (virtio_sector_bytes * i)%nat bs))
     <= virtio_sector_bytes)%nat
  /\ ((virtio_sector_bytes * i
       + length (take virtio_sector_bytes
                   (drop (virtio_sector_bytes * i)%nat bs)) <= length bs)%nat
      \/ length (take virtio_sector_bytes
                   (drop (virtio_sector_bytes * i)%nat bs)) = 0%nat).
Proof.
  rewrite !length_take, !length_drop. unfold virtio_sector_bytes. lia.
Qed.

(* an address in NO sector of [i] reads straight through *)
Lemma wr_sector_miss (off : Z) (bs : list (bv 8)) (i : nat) (a : Z)
    (dk : Z -> bv 8) :
  a < off + virtio_sector_size * Z.of_nat i
  \/ off + virtio_sector_size * (Z.of_nat i + 1) <= a ->
  wr_apply (wr_sector (Some (off, bs)) i) dk a = dk a.
Proof.
  intro H. cbn [wr_sector wr_apply fst snd]. apply disk_write_out.
  pose proof (sector_chunk_len bs i) as [Hle _].
  unfold virtio_sector_size, virtio_sector_bytes in *. lia.
Qed.

(* ...and so does an address outside the WHOLE write *)
Lemma wr_sector_outside (off : Z) (bs : list (bv 8)) (i : nat) (a : Z)
    (dk : Z -> bv 8) :
  a < off \/ off + Z.of_nat (length bs) <= a ->
  wr_apply (wr_sector (Some (off, bs)) i) dk a = dk a.
Proof.
  intro H. cbn [wr_sector wr_apply fst snd]. apply disk_write_out.
  pose proof (sector_chunk_len bs i) as [Hle Hcov].
  unfold virtio_sector_size, virtio_sector_bytes in *. lia.
Qed.

(* the byte sector [i] lands is the byte the WHOLE write lands there *)
Lemma wr_sector_hit (off : Z) (bs : list (bv 8)) (i : nat) (a : Z)
    (dk : Z -> bv 8) :
  off + virtio_sector_size * Z.of_nat i <= a ->
  a < off + virtio_sector_size * (Z.of_nat i + 1) ->
  wr_apply (wr_sector (Some (off, bs)) i) dk a = disk_write dk off bs a.
Proof.
  intros H1 H2. cbn [wr_sector wr_apply fst snd].
  unfold virtio_sector_size, virtio_sector_bytes in *.
  assert (Hj : (Z.to_nat (a - (off + 512 * Z.of_nat i)) < 512)%nat) by lia.
  assert (Hidx : Z.to_nat (a - off)
                 = (512 * i + Z.to_nat (a - (off + 512 * Z.of_nat i)))%nat)
    by lia.
  unfold disk_write.
  rewrite (proj2 (Z.leb_le (off + 512 * Z.of_nat i) a)) by lia.
  rewrite (proj2 (Z.leb_le off a)) by lia.
  rewrite Hidx, lookup_take by lia. rewrite lookup_drop. reflexivity.
Qed.

(* Distinct sectors of ONE write commute -- the model's licence to land them
   in any order. *)

(* THE REASSEMBLY FACT.  Landing every sector of [w] -- in ANY order, with
   repetitions allowed -- is exactly [w].  This is what lets a request slot
   keep the BLOCK write as its recorded [disk_wr] while the crash permits are
   handed out one sector at a time. *)
Definition wr_fold (w : disk_wr) (l : list nat) (dk : Z -> bv 8) : Z -> bv 8 :=
  foldr (fun i d => wr_apply (wr_sector w i) d) dk l.


Lemma wr_fold_cons (w : disk_wr) (i : nat) (l : list nat) (dk : Z -> bv 8) :
  wr_fold w (i :: l) dk = wr_apply (wr_sector w i) (wr_fold w l dk).
Proof. reflexivity. Qed.

Lemma wr_fold_all (w : disk_wr) (l : list nat) (dk : Z -> bv 8) :
  (forall i, (i < wr_nsectors w)%nat -> i ∈ l) ->
  wr_fold w l dk = wr_apply w dk.
Proof.
  destruct w as [[off bs]|]; last first.
  { intros _. induction l as [|i l IH]; [reflexivity|].
    rewrite wr_fold_cons, IH. reflexivity. }
  intro Hall. apply functional_extensionality. intro a.
  cbn [wr_apply fst snd].
  destruct (decide (off <= a < off + Z.of_nat (length bs))) as [Hin|Hout];
    last first.
  { (* outside the whole write: every sector misses, and so does [w] *)
    rewrite (disk_write_out dk off bs a) by lia.
    clear Hall. induction l as [|i l IH]; [reflexivity|].
    rewrite wr_fold_cons, wr_sector_outside; [exact IH | lia]. }
  (* inside: exactly the sector holding [a] decides the byte, and it is the
     byte the whole write lands there *)
  assert (Hoff : off <= a) by lia.
  assert (Hsx : is_Some (bs !! Z.to_nat (a - off)))
    by (apply lookup_lt_is_Some_2; lia).
  destruct Hsx as [x Hx].
  rewrite (disk_write_in dk off bs a x Hoff Hx).
  remember (Nat.div (Z.to_nat (a - off)) virtio_sector_bytes) as k eqn:Hkdef.
  assert (Hk : (k < wr_nsectors (Some (off, bs)))%nat).
  { cbn [wr_nsectors snd]. rewrite Hkdef. apply sector_count_lt. lia. }
  specialize (Hall k Hk).
  pose proof (sector_of_bounds (Z.to_nat (a - off))) as Hdk.
  rewrite <- Hkdef in Hdk.
  assert (Hlo : off + virtio_sector_size * Z.of_nat k <= a).
  { unfold virtio_sector_size, virtio_sector_bytes in *. lia. }
  assert (Hhi : a < off + virtio_sector_size * (Z.of_nat k + 1)).
  { unfold virtio_sector_size, virtio_sector_bytes in *. lia. }
  clear Hk Hin Hdk Hkdef.
  induction l as [|i l IH]; [by apply elem_of_nil in Hall|].
  rewrite wr_fold_cons.
  destruct (decide (i = k)) as [->|Hne].
  - rewrite (wr_sector_hit off bs k a _ Hlo Hhi).
    exact (disk_write_in _ off bs a x Hoff Hx).
  - rewrite wr_sector_miss.
    + apply IH. apply elem_of_cons in Hall as [->|Hall]; [congruence|exact Hall].
    + unfold virtio_sector_size in *.
      destruct (Nat.lt_total i k) as [Hlt|[He|Hgt]]; [right|congruence|left]; lia.
Qed.

(* The same reassembly, LEFT-folded -- the shape a SEQUENCE of drains has
   ([virtio_drains], section 6b): the device applies the sectors in the order
   it picks them, earliest first.  [wr_fold_all] already tolerates any order
   and any repetition, so this is just the [foldl]/[foldr] bridge. *)
Definition wr_foldl (w : disk_wr) (l : list nat) (dk : Z -> bv 8) : Z -> bv 8 :=
  foldl (fun d i => wr_apply (wr_sector w i) d) dk l.

Lemma wr_foldl_rev (w : disk_wr) (l : list nat) (dk : Z -> bv 8) :
  wr_foldl w l dk = wr_fold w (reverse l) dk.
Proof.
  revert dk. induction l as [|i l IH]; intro dk; [reflexivity|].
  change (wr_foldl w (i :: l) dk)
    with (wr_foldl w l (wr_apply (wr_sector w i) dk)).
  rewrite (IH (wr_apply (wr_sector w i) dk)).
  rewrite reverse_cons. unfold wr_fold. rewrite foldr_app. reflexivity.
Qed.


(* THE BYTES OF ONE SECTOR, as the list a cache entry holds.  [wr_sector]
   carries the offset as well; the cache keys by absolute sector number, so
   only the payload travels. *)
Definition wr_sector_bytes (w : disk_wr) (i : nat) : list (bv 8) :=
  match wr_sector w i with Some ob => ob.2 | None => [] end.

Lemma wr_sector_bytes_none (i : nat) : wr_sector_bytes None i = [].
Proof. reflexivity. Qed.

(* DRAINED BYTES = CAPTURED BYTES.  Writing sector [i]'s cached payload at
   the sector's own disk offset IS the sector-[i] piece of the whole write --
   which is what lets stage 2 keep [wr_sector (vs_wr sl) i] as the permit
   index while the bytes come out of the cache rather than off the bus. *)
Lemma wr_sector_write (off : Z) (bs : list (bv 8)) (i : nat) (dk : Z -> bv 8) :
  disk_write dk (off + virtio_sector_size * Z.of_nat i)
    (wr_sector_bytes (Some (off, bs)) i)
  = wr_apply (wr_sector (Some (off, bs)) i) dk.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. THE VOLATILE WRITE CACHE'S VIEW OF THE DISK.                        *)
(*                                                                        *)
(*    A read must see the device's OWN latest bytes, cached or durable --   *)
(*    read-your-writes, which every real cache provides and which a driver  *)
(*    relies on without knowing it.  [cache_view] is that overlay: the      *)
(*    cached sector's byte where one exists, the durable image's elsewhere. *)
(*    With an empty cache it IS the durable image, so in writethrough       *)
(*    (where nothing survives a completion) every read reduces to [v_disk]  *)
(*    and the driver layer sees no change at all.                          *)
(* ---------------------------------------------------------------------- *)

Definition cache_view (v : virtio_state) : Z -> bv 8 :=
  fun a =>
    match v_cache v !! (a / virtio_sector_size) with
    | Some bs =>
        match bs !! Z.to_nat (a `mod` virtio_sector_size) with
        | Some b => b
        | None => v_disk v a
        end
    | None => v_disk v a
    end.

(* an address whose sector is not cached reads the durable image *)
Lemma cache_view_miss (v : virtio_state) (a : Z) :
  v_cache v !! (a / virtio_sector_size) = None -> cache_view v a = v_disk v a.
Proof. intro H. unfold cache_view. by rewrite H. Qed.

(* NOTHING CACHED: the overlay is the durable image, on the nose. *)

(* the sector arithmetic: inside sector [s], the index is the displacement *)
Lemma sector_div_mod (s a : Z) :
  virtio_sector_size * s <= a < virtio_sector_size * s + virtio_sector_size ->
  a / virtio_sector_size = s /\ a `mod` virtio_sector_size = a - virtio_sector_size * s.
Proof.
  intro Hb. unfold virtio_sector_size in *.
  assert (Ha : a = s * 512 + (a - 512 * s)) by lia.
  split.
  - rewrite Ha at 1. rewrite Z.div_add_l by lia.
    rewrite (Z.div_small (a - 512 * s) 512) by lia. lia.
  - rewrite Ha at 1. rewrite Z.add_comm, Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.

(* A CACHED SECTOR READS AS ITS BYTES. *)

(* ...and so the whole sector reads back as the cached list. *)

(* ---------------------------------------------------------------------- *)
(* 4. The memory VIEW: what the device sees when it masters the bus.       *)
(*                                                                        *)
(*    A DMA read of an address the byte map does not cover does not fail   *)
(*    and does not read zero -- it reads WHATEVER IS THERE, which this     *)
(*    model does not know.  So the device does not read a [gmap] at all;   *)
(*    it reads a TOTAL view [vmem], and the only thing tying the view to   *)
(*    the machine is [mem_view]: it agrees with the byte map wherever that *)
(*    map is defined, and is unconstrained everywhere else.  RiscvLang's   *)
(*    [DiskStepDma] quantifies the view EXISTENTIALLY, so a step off the   *)
(*    end of what the driver owns is genuine nondeterminism rather than a  *)
(*    silently-missing transition.                                        *)
(*                                                                        *)
(*    Two consequences worth spelling out, because they are the point:     *)
(*     - every device read is total, so no MMIO-independent read can ever  *)
(*       stall the device (the old model stalled on five of them, and each *)
(*       stall silently excused a driver that had pointed the queue at     *)
(*       memory it did not own);                                          *)
(*     - a claim about what the device reads is exactly a claim about      *)
(*       memory the claimant OWNS: [view_word_read] turns a successful     *)
(*       partial read of an owned sub-map into an equation about the view. *)
(* ---------------------------------------------------------------------- *)

Definition vmem := Arch.pa -> bv 8.

Definition mem_view (m : gmap Arch.pa (bv 8)) (mv : vmem) : Prop :=
  forall (a : Arch.pa) (b : bv 8), m !! a = Some b -> mv a = b.

(* the view of a sub-map is the view of the whole map *)
Lemma mem_view_subseteq (m1 m2 : gmap Arch.pa (bv 8)) (mv : vmem) :
  m1 ⊆ m2 -> mem_view m2 mv -> mem_view m1 mv.
Proof.
  intros Hsub Hv a b Ha. apply Hv. exact (lookup_weaken _ _ _ _ Ha Hsub).
Qed.

(* [n] bytes at [a], as the device sees them *)
Definition view_bytes (mv : vmem) (a : Arch.pa) (n : nat) : list (bv 8) :=
  (fun j : nat => mv (pa_add a j)) <$> seq 0 n.

(* an [n]-byte little-endian field, as the device sees it *)
Definition view_word (mv : vmem) (a : Arch.pa) (n : N) : bv (8 * n) :=
  Z_to_bv (8 * n) (assemble_bytes (view_bytes mv a (N.to_nat n))).

Lemma view_bytes_length (mv : vmem) (a : Arch.pa) (n : nat) :
  length (view_bytes mv a n) = n.
Proof. unfold view_bytes. rewrite length_fmap, length_seq. reflexivity. Qed.

(* THE transfer lemma: what the view says about bytes the claimant owns is
   exactly what those bytes are.  Everything the device invariant knows about
   the device's reads comes through here. *)
Lemma view_bytes_read (m : gmap Arch.pa (bv 8)) (mv : vmem) (a : Arch.pa)
    (n : nat) (bs : list (bv 8)) :
  mem_view m mv -> read_byte_list m a n = Some bs -> view_bytes mv a n = bs.
Proof.
  intros Hv Hr. unfold read_byte_list in Hr. apply mapM_Some_1 in Hr.
  pose proof (Forall2_length Hr) as Hlen. rewrite length_seq in Hlen.
  apply list_eq. intro i. unfold view_bytes. rewrite list_lookup_fmap.
  destruct (decide (i < n)%nat) as [Hi|Hi].
  - assert (Hseq : seq 0 n !! i = Some i).
    { rewrite (lookup_seq_lt 0 n i Hi). reflexivity. }
    rewrite Hseq. cbn [fmap option_fmap option_map].
    destruct (Forall2_lookup_l _ _ _ i i Hr Hseq) as (b & Hbs & Hmm).
    rewrite Hbs. f_equal. exact (Hv _ _ Hmm).
  - rewrite (lookup_seq_ge 0 n i) by lia. cbn [fmap option_fmap option_map].
    symmetry. apply lookup_ge_None_2. lia.
Qed.

Lemma view_word_read (m : gmap Arch.pa (bv 8)) (mv : vmem) (a : Arch.pa)
    (n : N) (w : bv (8 * n)) :
  mem_view m mv -> read_bytes m a n = Some w -> view_word mv a n = w.
Proof.
  intros Hv. unfold read_bytes, view_word.
  destruct (mapM (fun j : nat => m !! pa_add a j) (seq 0 (N.to_nat n)))
    as [bs|] eqn:Hm; [|discriminate].
  intro H. injection H as <-.
  rewrite (view_bytes_read m mv a (N.to_nat n) bs Hv Hm). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. Reading a request out of the virtqueue.                              *)
(*                                                                        *)
(*    xv6's disk transfers always use the legacy three-descriptor chain of *)
(*    spec 5.2: a device-readable 16-byte header (type/reserved/sector), a *)
(*    data descriptor, and a device-writable one-byte status.  That is the *)
(*    ONLY chain shape this device serves, and it is the only thing that   *)
(*    can still stop it: [chain_at] returns [None] exactly when the shape  *)
(*    is wrong, and RiscvLang turns that into a step that may write        *)
(*    ANYTHING ANYWHERE ([DiskStepWild]) rather than into silence.         *)
(*                                                                        *)
(*    Deliberately NOT conditions here (each would be a stall that excused *)
(*    a driver, and reality does something rather than nothing):           *)
(*     - the descriptors' WRITE flags.  The transfer direction follows the *)
(*       request TYPE, and a device-writable data buffer is written        *)
(*       whatever the flag says.  Strictly more permissive than a device   *)
(*       that checks, so a driver proof cannot lean on the flag.          *)
(*     - the status descriptor's length.  One byte is written at its       *)
(*       address regardless.                                              *)
(*     - an unrecognised request type.  A real device completes the        *)
(*       request with status UNSUPP, and so does this one (section 6).      *)
(* ---------------------------------------------------------------------- *)

(* one descriptor, decoded *)
Record vq_desc := VqDesc {
  vd_addr  : Arch.pa;
  vd_len   : bv 32;
  vd_flags : bv 16;
  vd_next  : bv 16;
}.

Definition vd_has (d : vq_desc) (flag : Z) : bool :=
  Z.land (bv_unsigned (vd_flags d)) flag =? flag.

Definition desc_at (c : virtio_cfg) (mv : vmem) (i : Z) : vq_desc :=
  let base := pa_off (vc_desc c) (vq_desc_size * i) in
  VqDesc (view_word mv base 8) (view_word mv (pa_off base 8) 4)
         (view_word mv (pa_off base 12) 2) (view_word mv (pa_off base 14) 2).

(* the available ring: [flags:2 idx:2 ring[qnum]:2each] *)
Definition avail_idx_at (c : virtio_cfg) (mv : vmem) : bv 16 :=
  view_word mv (pa_off (vc_avail c) vq_idx_off) 2.
Definition avail_ring_at (c : virtio_cfg) (mv : vmem) (i : bv 16) : bv 16 :=
  view_word mv (pa_off (vc_avail c)
                  (vq_avail_ring_off
                   + 2 * (bv_unsigned i mod bv_unsigned (vc_qnum c)))) 2.

(* The chain at available-ring position [i]: exactly three descriptors, each
   named by an in-range index.  This is the whole well-formedness condition. *)
(* THE CHAIN FROM A DESCRIPTOR HEAD.  This is what the device actually holds
   on to once it has taken a request: QEMU keeps the popped chain, not the
   ring position it came from, and the used ring reports the HEAD back --
   which is what xv6 indexes [disk.info[]] by.  Heads are descriptor indices,
   so they are below [qnum] and distinct among live requests (a descriptor
   belongs to one chain), which is why they do not wrap the way a
   16-bit ring position does. *)
Definition chain_from (c : virtio_cfg) (mv : vmem) (h : bv 16)
  : option (bv 16 * vq_desc * vq_desc * vq_desc) :=
  let qnum := bv_unsigned (vc_qnum c) in
  if negb (bv_unsigned h <? qnum) then None else
  let d0 := desc_at c mv (bv_unsigned h) in
  if negb (vd_has d0 vring_desc_f_next) then None else
  if negb (bv_unsigned (vd_next d0) <? qnum) then None else
  let d1 := desc_at c mv (bv_unsigned (vd_next d0)) in
  if negb (vd_has d1 vring_desc_f_next) then None else
  if negb (bv_unsigned (vd_next d1) <? qnum) then None else
  let d2 := desc_at c mv (bv_unsigned (vd_next d1)) in
  (* exactly three: the status descriptor ends the chain *)
  if vd_has d2 vring_desc_f_next then None else
  Some (h, d0, d1, d2).

(* ...and the chain at an available-ring POSITION is the one whose head that
   entry names.  Only the POP reads the ring; every later phase works from
   the head it took. *)

Definition virtio_chain_ok (c : virtio_cfg) (mv : vmem) (h : bv 16) : bool :=
  match chain_from c mv h with Some _ => true | None => false end.


(* the decoded request: what the chain says to do, and where to report it *)
Record vio_req := VioReq {
  vr_head   : bv 16;    (* head descriptor index -- goes in the used ring *)
  vr_type   : bv 32;    (* VIRTIO_BLK_T_IN / _OUT, or anything else *)
  vr_sector : bv 64;
  vr_buf    : Arch.pa;  (* data buffer *)
  vr_len    : bv 32;    (* data length *)
  vr_status : Arch.pa;  (* the one-byte status the device must write *)
  (* ...and whether the DATA descriptor is device-WRITABLE, which is what
     decides how much of the chain the device may write and therefore what
     goes in the used element's [len].  It is a property of the descriptor
     flags, not of the request type: an unrecognised type published through a
     read-shaped chain has a writable data buffer the device simply does not
     fill. *)
  vr_wr     : bool;
}.

Definition req_from (c : virtio_cfg) (mv : vmem) (h : bv 16) : option vio_req :=
  match chain_from c mv h with
  | None => None
  | Some (h, d0, d1, d2) =>
      (* the header: type:4 reserved:4 sector:8 *)
      Some (VioReq h (view_word mv (vd_addr d0) 4)
                     (view_word mv (pa_off (vd_addr d0) 8) 8)
                     (vd_addr d1) (vd_len d1) (vd_addr d2)
                     (vd_has d1 vring_desc_f_write))
  end.



(* ---------------------------------------------------------------------- *)
(* 5b. THE AVAILABLE-RING WINDOW, and the set of positions the device may  *)
(*     still serve.                                                        *)
(*                                                                        *)
(*     A driver publishes at positions 0, 1, 2, ... of the available ring  *)
(*     and a device SERVES them in whatever order it finishes them -- that *)
(*     is what a device with more than one request in flight does, and it  *)
(*     is what the used ring reports back (QEMU produces both orders for   *)
(*     two in-flight writes; tools/vtest/README.md finding 5).  So the     *)
(*     device state cannot be a single consumed index: it is a WATERMARK   *)
(*     [v_seen] plus the set [v_inflight] of positions served out of turn.    *)
(*                                                                        *)
(*     The window arithmetic is the hardware's own: positions are 16-bit   *)
(*     counters that wrap, and "published" is a MODULAR DISTANCE test      *)
(*     against the driver's index -- [p] is published iff it is closer to  *)
(*     the watermark, going forwards, than the published index is.  No     *)
(*     fuel, no enumeration of [bv 16] anywhere.                          *)
(* ---------------------------------------------------------------------- *)

Definition one16 : bv 16 := Z_to_bv 16 1.

(* how far FORWARDS from [a] to [b], modulo the counter's width *)
Definition vdist (a b : bv 16) : Z := (bv_unsigned b - bv_unsigned a) `mod` 65536.

Lemma vdist_bounds (a b : bv 16) : 0 <= vdist a b < 65536.
Proof. unfold vdist. apply Z.mod_pos_bound. lia. Qed.

Lemma vdist_refl (a : bv 16) : vdist a a = 0.
Proof. unfold vdist. rewrite Z.sub_diag. reflexivity. Qed.

Lemma vdist_zero (a b : bv 16) : vdist a b = 0 -> a = b.
Proof.
  unfold vdist. intro H.
  pose proof (bv_unsigned_in_range _ a) as Ha.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  unfold bv_modulus in Ha, Hb. cbn in Ha, Hb.
  apply bv_eq. apply Z.mod_divide in H; [| lia ].
  destruct H as [k Hk]. lia.
Qed.

(* a position is determined by its distance from any other *)
Lemma vdist_inj (a b c : bv 16) : vdist a b = vdist a c -> b = c.
Proof.
  unfold vdist. intro H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  pose proof (bv_unsigned_in_range _ c) as Hc.
  unfold bv_modulus in Hb, Hc. cbn in Hb, Hc.
  assert (Hd : (bv_unsigned b - bv_unsigned c) `mod` 65536 = 0).
  { replace (bv_unsigned b - bv_unsigned c)
      with ((bv_unsigned b - bv_unsigned a) - (bv_unsigned c - bv_unsigned a))
      by lia.
    rewrite Zminus_mod, H, Z.sub_diag. reflexivity. }
  apply Z.mod_divide in Hd; [| lia ]. destruct Hd as [z Hz]. lia.
Qed.

Lemma bv_unsigned_one16 : bv_unsigned one16 = 1.
Proof. reflexivity. Qed.

Lemma bv16_wrap (z : Z) : bv_wrap 16 z = z `mod` 65536.
Proof. unfold bv_wrap, bv_modulus. f_equal. Qed.

(* the successor position, and what it does to every distance *)
Lemma vdist_succ (a b : bv 16) :
  vdist (bv_add a one16) b = (vdist a b - 1) `mod` 65536.
Proof.
  unfold vdist. rewrite bv_add_unsigned, bv_unsigned_one16, bv16_wrap.
  rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma vdist_succ_pos (a b : bv 16) :
  vdist a b <> 0 -> vdist (bv_add a one16) b = vdist a b - 1.
Proof.
  intro H. rewrite vdist_succ. pose proof (vdist_bounds a b).
  apply Z.mod_small. lia.
Qed.

Lemma vdist_succ_self (a : bv 16) : vdist (bv_add a one16) a = 65535.
Proof. rewrite vdist_succ, vdist_refl. reflexivity. Qed.

(* [p] is a position the driver has PUBLISHED and the watermark has not
   passed: strictly inside the window that runs from [lo] to [ai]. *)
Definition vpos_pub (lo ai p : bv 16) : bool := vdist lo p <? vdist lo ai.



(* THE ENUMERATION.  The window is [lo], [lo+1], ... for as many positions
   as the driver is ahead by, so "is there anything to serve?" is a fold over
   a list whose length is the outstanding count -- decidable and computable,
   with no scan of [bv 16] anywhere. *)
Fixpoint vpos_list (n : nat) (lo : bv 16) : list (bv 16) :=
  match n with O => [] | S k => lo :: vpos_list k (bv_add lo one16) end.





(* ---------------------------------------------------------------------- *)
(* 6. The autonomous request step: the device's own execution context.     *)
(* ---------------------------------------------------------------------- *)

(* Completing a request writes, in one transition: the transferred data (for
   a disk READ), the status byte, the used-ring element, and the used index.
   Ordering the index bump last is what the driver's completion test relies
   on, and doing it all atomically gives exactly that. *)
(* THE USED ELEMENT'S [len] IS THE DEVICE-WRITABLE PART OF THE CHAIN: the
   status byte, plus the data buffer when the driver marked that descriptor
   WRITABLE.  So a disk READ reports 513 and a disk WRITE reports 1, which is
   what the hardware does; the model used to report the DATA descriptor's
   length in both directions (finding 4) -- 512 where the hardware says 1.
   Nothing in this tree noticed because xv6's driver ignores the field; a
   driver that used it to learn how much of a partial read arrived would have
   been verified against a device that does not exist.

   THE DISCRIMINATOR IS THE DESCRIPTOR FLAG, NOT THE REQUEST TYPE, and that
   is the whole subtlety: an unrecognised type or a FLUSH published through a
   read-shaped chain has a writable data buffer that the device never fills,
   and the hardware still counts it (DiskErr.v measures exactly that).  The
   spec's "number of bytes WRITTEN" would say 1 there; every real device
   reports the writable segment's length instead, and a model that reported 1
   would produce a value the hardware does not -- which is the defect this
   finding was about, merely relocated. *)
Definition vreq_used_len (r : vio_req) : bv 32 :=
  if vr_wr r then Z_to_bv 32 (bv_unsigned (vr_len r) + 1) else Z_to_bv 32 1.

Definition virtio_used_writes (c : virtio_cfg) (ui : bv 16) (r : vio_req)
  : gmap Arch.pa (bv 8) :=
  let qnum := bv_unsigned (vc_qnum c) in
  let slot := bv_unsigned ui mod qnum in
  let elem := pa_off (vc_used c) (vq_used_ring_off + vq_used_elem_size * slot) in
  let m1 := write_bytes ∅ elem 4 (Z_to_bv 32 (bv_unsigned (vr_head r))) in
  let m2 := write_bytes m1 (pa_off elem 4) 4 (vreq_used_len r) in
  write_bytes m2 (pa_off (vc_used c) vq_idx_off) 2 (bv_add ui (Z_to_bv 16 1)).

Definition byte_zero : bv 8 := Z_to_bv 8 0.

(* Completing ONE parsed request.  TOTAL: there is no request the device
   refuses to answer.  An unrecognised type is reported back with status
   UNSUPP and no data transfer, exactly as a real block device does. *)
(* THE DISK WRITE ONE REQUEST MAKES, as pure data (section 3's [disk_wr]).
   A READ -- and an unrecognised type -- moves no disk byte, so it is [None]
   and its permit is free.  This is the write the CAPTURE cuts into
   [wr_nsectors] cache entries and the DRAINS put down one at a time
   (sections 6a and 6b). *)
Definition vreq_wr (mv : vmem) (r : vio_req) : disk_wr :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    Some (bv_unsigned (vr_sector r) * virtio_sector_size,
          view_bytes mv (vr_buf r) (Z.to_nat (bv_unsigned (vr_len r))))
  else None.

(* ...and how many sectors that is.  VIEW-INDEPENDENT: the device's schedule
   may not depend on what it reads out of the buffer. *)
Definition vreq_nsectors (r : vio_req) : nat :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    sector_count (Z.to_nat (bv_unsigned (vr_len r)))
  else 0%nat.

Lemma vreq_nsectors_wr (mv : vmem) (r : vio_req) :
  wr_nsectors (vreq_wr mv r) = vreq_nsectors r.
Proof.
  unfold vreq_wr, vreq_nsectors, wr_nsectors.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out); [|reflexivity].
  cbn [snd]. by rewrite view_bytes_length.
Qed.


Lemma vreq_nsectors_in (r : vio_req) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out -> vreq_nsectors r = 0%nat.
Proof. intro H. unfold vreq_nsectors. by rewrite (proj2 (Z.eqb_neq _ _) H). Qed.

(* -- THE CACHE ONE REQUEST CAPTURES (claude-notes/projects/async-disk.md) --

   The cache is keyed by ABSOLUTE SECTOR NUMBER, so sector [i] of a request
   whose header names sector [vr_sector r] is at key [vr_sector r + i] and its
   bytes at disk offset [512 * (vr_sector r + i)] -- which is exactly
   [wr_sector]'s own offset for that piece ([vreq_sector_write] below).  That
   coincidence is the whole reason the crash permits can stay indexed by
   [wr_sector w i] while the bytes travel through the cache. *)

Definition vreq_key (r : vio_req) (i : nat) : Z :=
  bv_unsigned (vr_sector r) + Z.of_nat i.

Lemma vreq_key_inj (r : vio_req) (i j : nat) :
  vreq_key r i = vreq_key r j -> i = j.
Proof. unfold vreq_key. lia. Qed.

(* the cache entries for a sub-list of the request's sectors... *)
Definition vreq_cache_of (mv : vmem) (r : vio_req) (is : list nat)
  : gmap Z (list (bv 8)) :=
  list_to_map ((fun i => (vreq_key r i, wr_sector_bytes (vreq_wr mv r) i))
                 <$> is).

(* ...and for ALL of them: what one capture step deposits. *)
Definition vreq_cache (mv : vmem) (r : vio_req) : gmap Z (list (bv 8)) :=
  vreq_cache_of mv r (seq 0 (vreq_nsectors r)).

(* the sector NUMBERS a request touches.  VIEW-INDEPENDENT, like
   [vreq_nsectors]: the completion gate may not depend on the payload. *)
Definition vreq_sectors (r : vio_req) : gset Z :=
  list_to_set (vreq_key r <$> seq 0 (vreq_nsectors r)).


Lemma vreq_cache_of_fst (mv : vmem) (r : vio_req) (is : list nat) :
  ((fun i => (vreq_key r i, wr_sector_bytes (vreq_wr mv r) i)) <$> is).*1
  = vreq_key r <$> is.
Proof. rewrite <- list_fmap_compose. reflexivity. Qed.

Lemma vreq_cache_of_dom (mv : vmem) (r : vio_req) (is : list nat) :
  dom (vreq_cache_of mv r is) = list_to_set (vreq_key r <$> is).
Proof.
  unfold vreq_cache_of. rewrite dom_list_to_map_L, vreq_cache_of_fst.
  reflexivity.
Qed.


Lemma vreq_cache_of_cons (mv : vmem) (r : vio_req) (i : nat) (is : list nat) :
  vreq_cache_of mv r (i :: is)
  = <[ vreq_key r i := wr_sector_bytes (vreq_wr mv r) i ]>
      (vreq_cache_of mv r is).
Proof. reflexivity. Qed.

Lemma vreq_cache_of_nil (mv : vmem) (r : vio_req) :
  vreq_cache_of mv r [] = ∅.
Proof. reflexivity. Qed.

Lemma vreq_sectors_spec (r : vio_req) (s : Z) :
  s ∈ vreq_sectors r <-> exists i, (i < vreq_nsectors r)%nat /\ s = vreq_key r i.
Proof.
  unfold vreq_sectors. rewrite elem_of_list_to_set, elem_of_list_fmap.
  split.
  - intros (i & -> & Hi). apply elem_of_seq in Hi. exists i. split; [lia|done].
  - intros (i & Hi & ->). exists i. split; [done|]. apply elem_of_seq. lia.
Qed.

(* THE SECTORS A REQUEST TOUCHES, in EITHER direction -- [vreq_sectors] is
   the write's payload and is empty for a read, and the completion gate needs
   the read's range too (see [virtio_complete_ok]). *)
Definition vreq_span (r : vio_req) : nat :=
  sector_count (Z.to_nat (bv_unsigned (vr_len r))).

Definition vreq_touch (r : vio_req) : gset Z :=
  list_to_set (vreq_key r <$> seq 0 (vreq_span r)).

Lemma vreq_touch_spec (r : vio_req) (s : Z) :
  s ∈ vreq_touch r <-> exists i, (i < vreq_span r)%nat /\ s = vreq_key r i.
Proof.
  unfold vreq_touch. rewrite elem_of_list_to_set, elem_of_list_fmap.
  split.
  - intros (i & -> & Hi). apply elem_of_seq in Hi. exists i. split; [lia|done].
  - intros (i & Hi & ->). exists i. split; [done|]. apply elem_of_seq. lia.
Qed.

(* for a WRITE the two agree: its payload IS its span *)
Lemma vreq_touch_out (r : vio_req) :
  bv_unsigned (vr_type r) = virtio_blk_t_out -> vreq_touch r = vreq_sectors r.
Proof.
  intro H. unfold vreq_touch, vreq_sectors, vreq_span, vreq_nsectors.
  by rewrite H, Z.eqb_refl.
Qed.

(* THE COLLAPSE: a request none of whose sectors is cached reads the DURABLE
   image, so the overlay the device serves reads from is invisible to it.
   Every byte of the request's range lies in one of the sectors its span
   names, so an uncached span is an uncached range. *)
Lemma cache_view_read (v : virtio_state) (r : vio_req) :
  vreq_touch r ∩ dom (v_cache v) = ∅ ->
  disk_read (cache_view v)
    (bv_unsigned (vr_sector r) * virtio_sector_size)
    (Z.to_nat (bv_unsigned (vr_len r)))
  = disk_read (v_disk v)
      (bv_unsigned (vr_sector r) * virtio_sector_size)
      (Z.to_nat (bv_unsigned (vr_len r))).
Proof.
  intro Hdisj. unfold disk_read. apply list_fmap_ext. intros k x Hk.
  apply lookup_seq in Hk as [-> Hk].
  replace (0 + k)%nat with k by lia. set (j := k).
  assert (Hj : (j < Z.to_nat (bv_unsigned (vr_len r)))%nat) by exact Hk.
  apply cache_view_miss.
  (* the byte's sector is the [j / 512]th of the request's span *)
  assert (Hsec : (bv_unsigned (vr_sector r) * virtio_sector_size + Z.of_nat j)
                 `div` virtio_sector_size
                 = vreq_key r (j `div` 512)%nat).
  { unfold vreq_key, virtio_sector_size.
    rewrite Z.div_add_l by lia.
    rewrite Nat2Z.inj_div. change (Z.of_nat 512) with 512. reflexivity. }
  rewrite Hsec.
  apply not_elem_of_dom. intro Hc.
  assert (Hin : vreq_key r (j `div` 512)%nat ∈ vreq_touch r).
  { apply vreq_touch_spec. exists (j `div` 512)%nat. split; [| reflexivity ].
    unfold vreq_span, virtio_sector_bytes.
    apply Nat.div_lt_upper_bound; [lia|].
    pose proof (sector_count_cover (Z.to_nat (bv_unsigned (vr_len r)))) as Hcov.
    unfold virtio_sector_bytes in Hcov. lia. }
  assert (Hne : vreq_key r (j `div` 512)%nat ∈ vreq_touch r ∩ dom (v_cache v))
    by (apply elem_of_intersection; split; [exact Hin | exact Hc]).
  rewrite Hdisj in Hne. by apply elem_of_empty in Hne.
Qed.

(* a request that is not a disk WRITE touches no sector at all *)
Lemma vreq_sectors_in (r : vio_req) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out -> vreq_sectors r = ∅.
Proof.
  intro H. unfold vreq_sectors. by rewrite (vreq_nsectors_in r H).
Qed.


(* THE DRAIN'S IMAGE MOVE, in the request's own vocabulary: writing sector
   [i]'s cached bytes at key [vreq_key r i] IS the [wr_sector] piece. *)
Lemma vreq_sector_write (mv : vmem) (r : vio_req) (i : nat) (dk : Z -> bv 8) :
  bv_unsigned (vr_type r) = virtio_blk_t_out ->
  disk_write dk (virtio_sector_size * vreq_key r i)
    (wr_sector_bytes (vreq_wr mv r) i)
  = wr_apply (wr_sector (vreq_wr mv r) i) dk.
Proof.
  intro Hout. unfold vreq_wr. rewrite Hout, Z.eqb_refl.
  replace (virtio_sector_size * vreq_key r i)
    with (bv_unsigned (vr_sector r) * virtio_sector_size
          + virtio_sector_size * Z.of_nat i)
    by (unfold vreq_key; lia).
  exact (wr_sector_write _ _ i dk).
Qed.

(* Completing ONE parsed request.  The completion touches NEITHER the disk
   image NOR the cache: an OUT request's data was CAPTURED into the cache
   earlier ([virtio_capture_step], section 6a) and drains to the image at
   steps of the device's own choosing ([virtio_drain_step], section 6b), so
   all this step does is the status byte, the used-ring element, the used
   index and the interrupt -- and clear [v_taken] for the next request.  A
   disk READ transfers in one step, through the CACHE-OVERLAID image
   ([cache_view]): the device must report its own latest bytes, cached or
   durable.  VIRTIO_BLK_T_FLUSH is recognised (status OK, no data); TOTAL as
   before -- an unrecognised type is reported back with status UNSUPP and no
   data transfer, exactly as a real block device does.  WHEN the completion
   is ENABLED is [virtio_complete_ok] below; that is where the cache mode
   shows up. *)
Definition virtio_complete (v : virtio_state) (mv : vmem) (r : vio_req)
    (i : bv 16) : virtio_state * gmap Arch.pa (bv 8) :=
  let n := Z.to_nat (bv_unsigned (vr_len r)) in
  let doff := bv_unsigned (vr_sector r) * virtio_sector_size in
  let st := if (bv_unsigned (vr_type r) =? virtio_blk_t_in)
               || (bv_unsigned (vr_type r) =? virtio_blk_t_out)
               || (bv_unsigned (vr_type r) =? virtio_blk_t_flush)
            then virtio_blk_s_ok else virtio_blk_s_unsupp in
  let ws := <[ vr_status r := Z_to_bv 8 st ]>
              (virtio_used_writes (v_cfg v) (v_used_idx v) r) in
  (* the request leaves the in-flight set; the POP index does not move -- it
     is advanced only by [virtio_pop], and only by one *)
  let fl := v_inflight v ∖ {[ i ]} in
  (* THE LATCH IS RELEASED ONLY BY THE REQUEST THAT HOLDS IT: completing some
     OTHER position leaves another request's payload exactly where it was. *)
  let tk := if bool_decide (v_taken v = Some i) then None else v_taken v in
  let vd := VirtioState (v_cfg v)
              (bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer))
              (v_seen v) fl
              (bv_add (v_used_idx v) (Z_to_bv 16 1)) (v_disk v)
              (v_cache v) tk (v_cap v) in
  if bv_unsigned (vr_type r) =? virtio_blk_t_in then
    (* read the disk: the device WRITES the driver's buffer, READ-YOUR-WRITES *)
    (vd, write_byte_list ws (vr_buf r) (disk_read (cache_view v) doff n))
  else
    (* write the disk, a flush, or an unsupported type: the status byte and
       the used-ring report, nothing else *)
    (vd, ws).

(* The completion is now VIEW-INDEPENDENT -- a strengthening of the model:
   whatever the device reads off the bus, it has already committed. *)

(* ...and it does not move the disk image. *)

(* ...and it does not move the CACHE either: the drains own that. *)
Lemma virtio_complete_cache (v : virtio_state) (mv : vmem) (r : vio_req) (i : bv 16) :
  v_cache (virtio_complete v mv r i).1 = v_cache v.
Proof.
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in); reflexivity.
Qed.

(* it does clear the capture flag, so the NEXT request starts untaken *)


(* ====================================================================== *)
(* THE POP.  The device takes the entry at [v_seen] and advances by ONE.    *)
(* This is the phase QEMU does strictly in order, and the phase xv6's ring  *)
(* -slot reuse depends on: the driver overwrites [avail->ring[idx % NUM]],  *)
(* and that entry is dead precisely because the device is past it.  The pop *)
(* reads no memory the model tracks and writes none: it only moves the      *)
(* index and remembers that the position is now in flight.                  *)
(* ====================================================================== *)

(* there is an entry to take: the driver has published past the pop index *)
Definition virtio_pop_ok (v : virtio_state) (mv : vmem) : bool :=
  virtio_live (v_cfg v)
  && negb (bool_decide (v_seen v = avail_idx_at (v_cfg v) mv)).

(* the pop READS the ring entry: what it takes away is the descriptor HEAD
   the driver put there, which is what it will report back in the used ring *)
Definition virtio_pop (v : virtio_state) (mv : vmem) : virtio_state :=
  VirtioState (v_cfg v) (v_isr v)
    (bv_add (v_seen v) one16)
    ({[ avail_ring_at (v_cfg v) mv (v_seen v) ]} ∪ v_inflight v)
    (v_used_idx v) (v_disk v) (v_cache v) (v_taken v) (v_cap v).

Definition virtio_pop_step (v : virtio_state) (mv : vmem) : option virtio_state :=
  if virtio_pop_ok v mv then Some (virtio_pop v mv) else None.

Lemma virtio_pop_cfg (v : virtio_state) (mv : vmem) : v_cfg (virtio_pop v mv) = v_cfg v.
Proof. reflexivity. Qed.
Lemma virtio_pop_cache (v : virtio_state) (mv : vmem) : v_cache (virtio_pop v mv) = v_cache v.
Proof. reflexivity. Qed.
Lemma virtio_pop_taken (v : virtio_state) (mv : vmem) : v_taken (virtio_pop v mv) = v_taken v.
Proof. reflexivity. Qed.
Lemma virtio_pop_isr (v : virtio_state) (mv : vmem) : v_isr (virtio_pop v mv) = v_isr v.
Proof. reflexivity. Qed.
Lemma virtio_pop_uidx (v : virtio_state) (mv : vmem) : v_used_idx (virtio_pop v mv) = v_used_idx v.
Proof. reflexivity. Qed.
Lemma virtio_pop_seen (v : virtio_state) (mv : vmem) :
  v_seen (virtio_pop v mv) = bv_add (v_seen v) one16.
Proof. reflexivity. Qed.
Lemma virtio_pop_inflight (v : virtio_state) (mv : vmem) :
  v_inflight (virtio_pop v mv) = {[ avail_ring_at (v_cfg v) mv (v_seen v) ]} ∪ v_inflight v.
Proof. reflexivity. Qed.

Lemma virtio_pop_step_shape (v : virtio_state) (mv : vmem) (v' : virtio_state) :
  virtio_pop_step v mv = Some v' ->
  virtio_pop_ok v mv = true /\ v' = virtio_pop v mv.
Proof.
  unfold virtio_pop_step. destruct (virtio_pop_ok v mv) eqn:Hp; [|discriminate].
  intro H. injection H as <-. split; reflexivity.
Qed.

Lemma virtio_pop_step_disk (v : virtio_state) (mv : vmem) (v' : virtio_state) :
  virtio_pop_step v mv = Some v' -> v_disk v' = v_disk v.
Proof.
  intro H. destruct (virtio_pop_step_shape _ _ _ H) as [_ ->]. reflexivity.
Qed.


Lemma virtio_pop_step_not_live (v : virtio_state) (mv : vmem) :
  virtio_live (v_cfg v) = false -> virtio_pop_step v mv = None.
Proof.
  intro Hl. unfold virtio_pop_step, virtio_pop_ok. by rewrite Hl.
Qed.

(* the device has work to do: it can pop, or it can answer something it has
   already popped *)
Definition virtio_pending (v : virtio_state) (mv : vmem) : bool :=
  virtio_live (v_cfg v)
  && (negb (bool_decide (v_seen v = avail_idx_at (v_cfg v) mv))
      || negb (bool_decide (v_inflight v = ∅))).

(* A position may be answered exactly when the device has POPPED it and not
   yet completed it.  Which of those it picks is free -- that is finding 5 --
   but it can only pick from the ones it took, and it took them in order. *)
Definition virtio_serve_ok (v : virtio_state) (mv : vmem) (i : bv 16) : bool :=
  virtio_live (v_cfg v) && bool_decide (i ∈ v_inflight v).

(* a servable position is work to do *)

Lemma virtio_serve_live (v : virtio_state) (mv : vmem) (i : bv 16) :
  virtio_serve_ok v mv i = true -> virtio_live (v_cfg v) = true.
Proof. intro H. by apply andb_prop in H as [Hl _]. Qed.

Lemma virtio_serve_in (v : virtio_state) (mv : vmem) (i : bv 16) :
  virtio_serve_ok v mv i = true -> i ∈ v_inflight v.
Proof.
  intro H. apply andb_prop in H as [_ Hf].
  by apply bool_decide_eq_true in Hf.
Qed.

(* the device has work exactly when it can pop or SOME position is servable *)

(* THE COMPLETION GATE, and the ONE place the cache mode is visible to the
   driver (claude-notes/projects/async-disk.md §1):
   - a disk WRITE may complete once ITS OWN data has been CAPTURED -- the
     latch names the position, so a write cannot ride out on another
     request's capture -- and -- if the
     driver DECLINED the cache ([virtio_wce] false, i.e. writeTHROUGH) -- only
     once none of its sectors is still cached, i.e. once every one of them has
     drained to the durable image;
   - a FLUSH completes when the cache is EMPTY, which is what makes it a
     barrier;
   - a READ (and an unrecognised type) is never gated: the read is served from
     [cache_view], so it is already read-your-writes.
   With [virtio_wce] TRUE the write completes right after the capture and the
   drains happen whenever -- that is the write-BACK behaviour, and it is what
   a driver that negotiates FLUSH buys. *)
Definition virtio_complete_ok (v : virtio_state) (r : vio_req) (i : bv 16)
  : bool :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    bool_decide (v_taken v = Some i)
    && (virtio_wce (v_cfg v)
        || bool_decide (vreq_touch r ∩ dom (v_cache v) = ∅))
  else if bv_unsigned (vr_type r) =? virtio_blk_t_flush then
    bool_decide (v_cache v = ∅)
  else
    (* A READ IS SERVED FROM THE DEVICE'S LATEST BYTES ([cache_view]), so it
       is not gated on the cache DRAINING -- but in writethrough it does wait
       for its OWN sectors to leave the cache.  What that costs is a driver
       that reads a sector it is concurrently writing: such a driver cannot
       exist in this development (the disk points-to for a sector is
       exclusive, so two in-flight requests never share one), and admitting
       the read-your-writes execution for it would mean carrying the
       overlap-freedom of every pair of in-flight requests through the queue
       protocol.  Recorded in claude-notes/design/virtio-driver.md. *)
    virtio_wce (v_cfg v)
    || bool_decide (vreq_touch r ∩ dom (v_cache v) = ∅).

(* a READ and an unrecognised type are completable at once *)

(* ...and the gate read back: a read that completed had its own sectors off
   the cache, so the bytes it reported are the DURABLE ones *)
Lemma virtio_complete_ok_read (v : virtio_state) (r : vio_req) (i : bv 16) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  virtio_complete_ok v r i = true ->
  virtio_wce (v_cfg v) = true \/ vreq_touch r ∩ dom (v_cache v) = ∅.
Proof.
  intros H1 H2 Hok. unfold virtio_complete_ok in Hok.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2) in Hok.
  apply orb_prop in Hok as [Hw|Hd]; [by left|].
  right. by apply bool_decide_eq_true in Hd.
Qed.

(* the OUT gate, read back *)
Lemma virtio_complete_ok_out (v : virtio_state) (r : vio_req) (i : bv 16) :
  bv_unsigned (vr_type r) = virtio_blk_t_out ->
  virtio_complete_ok v r i = true ->
  v_taken v = Some i
  /\ (virtio_wce (v_cfg v) = true \/ vreq_touch r ∩ dom (v_cache v) = ∅).
Proof.
  intros Hout Hok. unfold virtio_complete_ok in Hok.
  rewrite Hout, Z.eqb_refl in Hok.
  apply andb_prop in Hok as [Ht Hd].
  split; [exact (proj1 (bool_decide_eq_true _) Ht)|].
  apply orb_prop in Hd as [Hd|Hd]; [by left|].
  right. by apply bool_decide_eq_true in Hd.
Qed.

(* ...and the FLUSH gate *)
Lemma virtio_complete_ok_flush (v : virtio_state) (r : vio_req) (i : bv 16) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) = virtio_blk_t_flush ->
  virtio_complete_ok v r i = true -> v_cache v = ∅.
Proof.
  intros H1 H2 Hok. unfold virtio_complete_ok in Hok.
  rewrite (proj2 (Z.eqb_neq _ _) H1), H2, Z.eqb_refl in Hok.
  by apply bool_decide_eq_true in Hok.
Qed.

Definition virtio_req_step (v : virtio_state) (mv : vmem) (i : bv 16)
  : option (virtio_state * gmap Arch.pa (bv 8)) :=
  if negb (virtio_serve_ok v mv i) then None
  else match req_from (v_cfg v) mv i with
       | None => None
       | Some r =>
           if negb (virtio_complete_ok v r i) then None
           else Some (virtio_complete v mv r i)
       end.

(* the request the completion answered, and its gate -- the inversion the
   protocol layer runs on *)
Lemma virtio_req_step_shape (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_req_step v mv i = Some (v', w) ->
  exists r, req_from (v_cfg v) mv i = Some r
    /\ virtio_serve_ok v mv i = true /\ virtio_complete_ok v r i = true
    /\ (v', w) = virtio_complete v mv r i.
Proof.
  unfold virtio_req_step.
  destruct (virtio_serve_ok v mv i) eqn:Hp; [|discriminate].
  destruct (req_from (v_cfg v) mv i) as [r|] eqn:Hr; [|discriminate].
  destruct (virtio_complete_ok v r i) eqn:Hg; [|discriminate].
  intro Hs. exists r. split_and!; [reflexivity|reflexivity|exact Hg|].
  injection Hs as Hc. symmetry. exact Hc.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6a. THE CAPTURE STEP: the head write request's data enters the CACHE.   *)
(*                                                                        *)
(*    Enabled while the device has work to do, the published chain is well *)
(*    formed, the request is a disk WRITE, and its data has not been taken *)
(*    yet.  It reads the driver's buffer through the bus view ONCE and     *)
(*    deposits every sector of it in the cache, OVERWRITING whatever was   *)
(*    cached for those sectors (the latest write to a sector wins).        *)
(*    Nothing else moves: no memory write, no used-ring entry, no          *)
(*    interrupt, and -- the point -- no DURABLE disk byte.                 *)
(*                                                                        *)
(*    Why a separate step rather than reading the buffer at drain time:    *)
(*    in write-back mode the buffer is the DRIVER's again the moment the   *)
(*    request completes, so the device must own the bytes before it says   *)
(*    so.  The cache is the honest object, and it makes the drain step     *)
(*    memory-free (claude-notes/projects/async-disk.md §1).                *)
(* ---------------------------------------------------------------------- *)

Definition virtio_capture_step (v : virtio_state) (mv : vmem) (i : bv 16)
  : option virtio_state :=
  if negb (virtio_serve_ok v mv i) then None
  else match req_from (v_cfg v) mv i with
       | None => None
       | Some r =>
           if negb (bv_unsigned (vr_type r) =? virtio_blk_t_out) then None
           else if bool_decide (v_taken v = None) then
             Some (VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v)
                     (v_used_idx v) (v_disk v) (vreq_cache mv r ∪ v_cache v)
                     (Some i) (v_cap v))
           else None
       end.

(* THE inversion the field lemmas run on. *)
Lemma virtio_capture_step_shape (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (i : bv 16) :
  virtio_capture_step v mv i = Some v' ->
  exists r, req_from (v_cfg v) mv i = Some r
    /\ v' = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v)
              (v_used_idx v) (v_disk v) (vreq_cache mv r ∪ v_cache v)
              (Some i) (v_cap v).
Proof.
  unfold virtio_capture_step.
  destruct (negb (virtio_serve_ok v mv i)); [discriminate|].
  destruct (req_from (v_cfg v) mv i) as [r|] eqn:Hr; [|discriminate].
  destruct (negb (bv_unsigned (vr_type r) =? virtio_blk_t_out)); [discriminate|].
  destruct (bool_decide (v_taken v = None)); [|discriminate].
  intro Hs. injection Hs as <-. by exists r.
Qed.


(* the device does NOT advance to the next available-ring entry: the request
   is still in flight until its completion *)



(* NO interrupt: the driver is woken by the completion, not by a capture *)
Lemma virtio_capture_step_isr (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (i : bv 16) :
  virtio_capture_step v mv i = Some v' -> v_isr v' = v_isr v.
Proof.
  intro Hs. destruct (virtio_capture_step_shape _ _ _ _ Hs) as (r & _ & ->).
  reflexivity.
Qed.


(* THE DURABLE IMAGE DOES NOT MOVE.  A capture is invisible to a crash. *)
Lemma virtio_capture_step_disk (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (i : bv 16) :
  virtio_capture_step v mv i = Some v' -> v_disk v' = v_disk v.
Proof.
  intro Hs. destruct (virtio_capture_step_shape _ _ _ _ Hs) as (r & _ & ->).
  reflexivity.
Qed.


(* THE CACHE MOVE: exactly the request's own sectors, overwriting. *)

(* the enabling conditions, read back *)
Lemma virtio_capture_step_enabled (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (r : vio_req) (i : bv 16) :
  req_from (v_cfg v) mv i = Some r ->
  virtio_capture_step v mv i = Some v' ->
  virtio_serve_ok v mv i = true
  /\ bv_unsigned (vr_type r) = virtio_blk_t_out
  /\ v_taken v = None.
Proof.
  intros Hr Hs. unfold virtio_capture_step in Hs.
  destruct (virtio_serve_ok v mv i) eqn:Hp; [|by cbn in Hs].
  rewrite Hr in Hs. cbn [negb] in Hs.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out) eqn:Ho;
    [|by cbn in Hs]. cbn [negb] in Hs.
  destruct (bool_decide (v_taken v = None)) eqn:Ht; [|discriminate].
  apply Z.eqb_eq in Ho. apply bool_decide_eq_true in Ht. by split_and!.
Qed.

(* ...in particular the request is a disk WRITE: nothing else is captured *)

Lemma virtio_capture_step_not_live (v : virtio_state) (mv : vmem) (i : bv 16) :
  virtio_live (v_cfg v) = false -> virtio_capture_step v mv i = None.
Proof.
  intro H. unfold virtio_capture_step, virtio_serve_ok. by rewrite H.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6b. THE DRAIN STEP: one cached sector reaches the DURABLE image.        *)
(*                                                                        *)
(*    Enabled for ANY cached sector, of ANY request, in ANY order, at any  *)
(*    time -- and, crucially, WITHOUT a memory view: the bytes are the     *)
(*    device's own, so the drain reads nothing off the bus.  That is what  *)
(*    makes the Iris drain arm need no DMA lease, and it is what a crash   *)
(*    between two drains means: whatever had drained is on the disk, the   *)
(*    rest is gone with the cache ([virtio_reset_cache]).                  *)
(*                                                                        *)
(*    A 512-byte sector lands atomically and a 1024-byte block does not    *)
(*    (claude-notes/completed/sector-atomic-disk.md): this step is where    *)
(*    that tearing now lives.                                             *)
(* ---------------------------------------------------------------------- *)

Definition virtio_drain_step (v : virtio_state) (s : Z) : option virtio_state :=
  match v_cache v !! s with
  | None => None
  | Some bs =>
      Some (VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v) (v_used_idx v) (disk_write (v_disk v) (virtio_sector_size * s) bs) (delete s (v_cache v)) (v_taken v) (v_cap v))
  end.

Lemma virtio_drain_step_shape (v : virtio_state) (s : Z) (v' : virtio_state) :
  virtio_drain_step v s = Some v' ->
  exists bs, v_cache v !! s = Some bs
    /\ v' = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v) (v_used_idx v) (disk_write (v_disk v) (virtio_sector_size * s) bs) (delete s (v_cache v)) (v_taken v) (v_cap v).
Proof.
  unfold virtio_drain_step.
  destruct (v_cache v !! s) as [bs|] eqn:Hbs; [|discriminate].
  intro Hs. injection Hs as <-. by exists bs.
Qed.





(* NO interrupt: a drain is invisible to the driver *)
Lemma virtio_drain_step_isr (v : virtio_state) (s : Z) (v' : virtio_state) :
  virtio_drain_step v s = Some v' -> v_isr v' = v_isr v.
Proof.
  intro Hs. destruct (virtio_drain_step_shape _ _ _ Hs) as (bs & _ & ->).
  reflexivity.
Qed.




(* THE IMAGE MOVE: the cached sector's own bytes, at its own offset. *)

Lemma virtio_drain_step_enabled (v : virtio_state) (s : Z) (v' : virtio_state) :
  virtio_drain_step v s = Some v' -> s ∈ dom (v_cache v).
Proof.
  intro Hs. destruct (virtio_drain_step_shape _ _ _ Hs) as (bs & Hbs & _).
  apply elem_of_dom. by exists bs.
Qed.

(* a sector nobody cached does not drain *)
Lemma virtio_drain_step_none (v : virtio_state) (s : Z) :
  v_cache v !! s = None -> virtio_drain_step v s = None.
Proof. intro H. unfold virtio_drain_step. by rewrite H. Qed.

Lemma virtio_drain_step_empty (v : virtio_state) (s : Z) :
  v_cache v = ∅ -> virtio_drain_step v s = None.
Proof. intro H. apply virtio_drain_step_none. rewrite H. apply lookup_empty. Qed.

(* THE hole this model must not have.  [virtio_stalled] is "the device owes
   an answer and this model does not have one": it has work to do, and the
   step above produced nothing.  By construction that happens for exactly one
   reason -- the published chain is malformed ([virtio_stalled_chain]) -- and
   RiscvLang gives that case a step that may write anything anywhere, so a
   driver must PROVE it does not happen rather than benefit from it. *)
Definition virtio_stalled (v : virtio_state) (mv : vmem) : bool :=
  virtio_live (v_cfg v)
  && existsb (fun p => negb (virtio_chain_ok (v_cfg v) mv p))
       (elements (v_inflight v)).

(* A MALFORMED CHAIN IS A DEAD POSITION: neither half of the request
   protocol has a transition for it.  Stated at the position rather than at
   the watermark, since the device chooses which position it looks at. *)

(* the stalled device has work to do -- it is the device that CANNOT answer,
   not the device with nothing to answer *)

(* ...and the position it stalled AT: some servable one whose chain is bad *)

(* ...and neither does it have a CAPTURE step: a malformed chain names no
   request at all.  (A DRAIN is a different matter: it reads nothing off the
   bus, so it is enabled by the cache alone and a malformed queue cannot
   prevent it.  That is why [virtio_stalled] -- and hence [DiskStepWild]'s
   enabling condition -- is UNCHANGED by the cache: the wild step is still
   exactly "pending, and the published chain is malformed".) *)


(* THE DEVICE ALWAYS HAS SOMETHING TO DO.  "Pending and well formed" means
   one of the THREE autonomous actions is enabled:
   - the head request is an untaken WRITE: CAPTURE it;
   - it is a taken write in writeTHROUGH mode with sectors still cached, or a
     FLUSH with a non-empty cache: DRAIN one of them;
   - otherwise the COMPLETION is enabled -- immediately for a read, right
     after the capture in write-BACK mode, and after the last drain in
     writethrough.
   This is the liveness half of the model that [wp_disk_loop]'s not-stuck
   obligation discharges. *)
(* THE LATCH NAMES A LIVE POSITION.  Every reachable state has it -- a
   capture latches a position it is allowed to serve, a completion clears the
   latch, and publishing only ever widens the window -- but the state alone
   does not say so, so PROGRESS takes it as a hypothesis. *)

(* every servable position with a well-formed chain is a request the model
   can answer -- possibly after a drain, or after the request already in the
   latch gets out of the way *)

(* -- what a step does and does not touch -- *)

(* THE structural fact about an autonomous step, and the reason [virtio_cfg]
   is a separate record: the device never writes its own configuration. *)
Lemma virtio_req_step_cfg (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_req_step v mv i = Some (v', w) -> v_cfg v' = v_cfg v.
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_serve_ok v mv i)); [discriminate|].
  destruct (req_from (v_cfg v) mv i) as [r|]; [|discriminate].
  destruct (negb (virtio_complete_ok v r i)); [discriminate|].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* THE POP INDEX DOES NOT MOVE AT A COMPLETION.  It is advanced only by
   [virtio_pop], by exactly one -- which is what keeps the entries the device
   has not taken a contiguous interval below it. *)
Lemma virtio_req_step_seen (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_req_step v mv i = Some (v', w) ->
  v_seen v' = v_seen v.
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_serve_ok v mv i)); [discriminate|].
  destruct (req_from (v_cfg v) mv i) as [r|]; [|discriminate].
  destruct (negb (virtio_complete_ok v r i)); [discriminate|].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* ...and the completing request LEAVES the in-flight set *)
Lemma virtio_req_step_inflight (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_req_step v mv i = Some (v', w) ->
  v_inflight v' = v_inflight v ∖ {[ i ]}.
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_serve_ok v mv i)); [discriminate|].
  destruct (req_from (v_cfg v) mv i) as [r|]; [|discriminate].
  destruct (negb (virtio_complete_ok v r i)); [discriminate|].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* The used-buffer bit of the interrupt-status register goes UP on completion,
   and only the driver's INTERRUPT_ACK can bring it down again. *)
Lemma virtio_req_step_isr (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_req_step v mv i = Some (v', w) ->
  v_isr v' = bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer).
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_serve_ok v mv i)); [discriminate|].
  destruct (req_from (v_cfg v) mv i) as [r|]; [|discriminate].
  destruct (negb (virtio_complete_ok v r i)); [discriminate|].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* THE COMPLETION NO LONGER MOVES THE IMAGE: the data went into the CACHE at
   the capture (section 6a) and reached the image at the drains (section 6b);
   in writethrough all of that happened before this step was enabled. *)

(* ...and it does not move the CACHE either: only a drain does. *)

(* it does clear the capture flag for the next request *)


(* A step always raises the interrupt line. *)

Lemma virtio_req_step_not_live (v : virtio_state) (mv : vmem) (i : bv 16) :
  virtio_live (v_cfg v) = false -> virtio_req_step v mv i = None.
Proof.
  intro H. unfold virtio_req_step, virtio_serve_ok. by rewrite H.
Qed.

Lemma virtio_not_live_not_stalled (v : virtio_state) (mv : vmem) :
  virtio_live (v_cfg v) = false -> virtio_stalled v mv = false.
Proof.
  intro H. unfold virtio_stalled. by rewrite H.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6c. THE WRITETHROUGH INVARIANT (claude-notes/projects/async-disk.md §2). *)
(*                                                                        *)
(*    A driver that DECLINED the cache ([virtio_wce] false -- xv6) keeps    *)
(*    the device in a discipline that is visible in the state alone:       *)
(*                                                                        *)
(*      - nothing is cached but sectors of the HEAD request, and           *)
(*      - nothing is cached at all before the head request is taken.       *)
(*                                                                        *)
(*    Together those two say the cache is EMPTY at every instant between   *)
(*    requests -- so nothing a completion reported can ever be lost by     *)
(*    [virtio_reset]'s cache drop, which is what "writethrough" means at   *)
(*    the crash layer.  The head request has to be PARSED out of memory,   *)
(*    so its sector set rides as a parameter rather than being recomputed  *)
(*    here (the state alone does not know it).                             *)
(* ---------------------------------------------------------------------- *)

Definition virtio_wt_inv (v : virtio_state) (S : gset Z) : Prop :=
  dom (v_cache v) ⊆ S /\ (v_taken v = None -> v_cache v = ∅).

(* an empty cache satisfies it whatever the head request is *)
Lemma virtio_wt_inv_nil (v : virtio_state) (S : gset Z) :
  v_cache v = ∅ -> virtio_wt_inv v S.
Proof.
  intro H. split; [| by intros _]. rewrite H, dom_empty_L. apply empty_subseteq.
Qed.

(* the invariant is monotone in the sector set it is stated against *)

(* POWER-ON and POWER-CYCLE: the cache is gone, so the invariant holds *)

(* A CONFIGURATION WRITE LEAVES THE CACHE ALONE (or is the reset command,
   which empties it), so the invariant survives any MMIO store. *)

(* A CAPTURE re-establishes it AT THE REQUEST IT CAPTURED: the cache was
   empty (the head was untaken), so afterwards it is exactly that request's
   sectors. *)

(* A DRAIN only removes an entry, so it keeps the invariant at the same
   sector set. *)

(* THE PAYOFF.  In writethrough a completion FINDS THE CACHE EMPTY: for a
   disk WRITE because the gate demands that none of its sectors is still
   cached and the invariant says nothing else is; for every other request
   type because the invariant's sector set is empty to begin with (only an
   OUT has sectors).  So the completed request is DURABLE. *)

(* ...and so the invariant survives the completion, at ANY sector set: the
   next request starts from an empty cache and an untaken head. *)

(* ...and the cache mode itself is preserved by every device action, since
   none of them touches the configuration. *)



(* ---------------------------------------------------------------------- *)
(* 6d. REASSEMBLY: draining every captured sector IS the request's write.  *)
(*                                                                        *)
(*    The analogue of [wr_fold_all] for the cache: after a capture, running *)
(*    one drain per sector -- IN ANY ORDER -- moves the durable image by    *)
(*    exactly [wr_apply (vreq_wr mv r)], which is the [disk_wr] the client's *)
(*    crash permit is indexed at.  This is what lets a request slot keep    *)
(*    the whole BLOCK write as its recorded datum while the permits fire    *)
(*    one sector at a time.                                               *)
(* ---------------------------------------------------------------------- *)

Fixpoint virtio_drains (v : virtio_state) (l : list Z) : option virtio_state :=
  match l with
  | [] => Some v
  | s :: l' => match virtio_drain_step v s with
               | Some v1 => virtio_drains v1 l'
               | None => None
               end
  end.

(* draining a captured sub-list, one entry at a time *)

(* THE REASSEMBLY.  Every sector, in any order: the image moves by the whole
   write and the cache is emptied.  ([wr_foldl_all] is where "any order"
   actually happens -- distinct sectors commute.) *)

(* ...and the cache the capture deposited is exactly what a capture leaves
   behind when it starts from an empty one -- the premise above. *)

(* ---------------------------------------------------------------------- *)
(* 7. The queue obligation: what a driver owes the device.                 *)
(*                                                                        *)
(*    The device thread has to justify two things at the Iris level, and   *)
(*    neither is a property of the device: that it never takes the         *)
(*    write-anything step, and that when it does take a real step the      *)
(*    bytes it writes are ones it owns.  Both are consequences of ONE      *)
(*    positive obligation on the driver, and the word POSITIVE is the      *)
(*    whole point: an earlier version stated it as an implication -- if a   *)
(*    step happens then its writes are inside the lease -- which a driver   *)
(*    could satisfy vacuously by arranging for the device to stall.         *)
(*                                                                        *)
(*    [ctl] is the CONTROL region: bytes the claimant OWNS and the device  *)
(*    only ever READS -- the descriptor table and the available ring.      *)
(*    Pinning their contents is what makes the queue's shape and footprint *)
(*    predictable at all; the [## dom ctl] conjunct is what keeps them     *)
(*    pinned across the device's own writes.                               *)
(*                                                                        *)
(*    [S] is the set of available-ring positions the device may still      *)
(*    reach, and the obligation asks the driver to COVER the model's own   *)
(*    free set with it ([vfree lo ai ah], section 5b) rather than to close *)
(*    [S] under advancing by one: the device serves in whatever order it   *)
(*    likes, so "the next position" is not a thing the driver can name.    *)
(*    The covering direction is what makes the obligation POSITIVE, and it *)
(*    survives a serve for free -- a serve only ever SHRINKS the free set  *)
(*    ([vserve_free]).                                                     *)
(*                                                                         *)
(*    [S] is importantly NOT all of [bv 16]: a driver cannot maintain      *)
(*    well-formedness of ring slots it has not published, since xv6 leaves *)
(*    the stale entries of completed requests lying in the ring.           *)
(* ---------------------------------------------------------------------- *)

(* the request published at position [i] is well formed, and writes only
   inside the lease [D] and never over the control region.  Quantified over
   the WHOLE dynamic state -- watermark, served set and latch included --
   because the position the device serves is now its own choice: the slot's
   obligation cannot be stated at "the state whose mark is [i]" any more. *)
Definition virtio_slot_ok (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (i : bv 16) : Prop :=
  forall mv : vmem, mem_view ctl mv ->
    virtio_chain_ok c mv i = true
    /\ forall (isr : bv 32) (lo : bv 16) (ah : gset (bv 16)) (ui : bv 16)
              (dk : Z -> bv 8) (ca : gmap Z (list (bv 8)))
              (tk : option (bv 16)) (cp : bv 64)
              (v' : virtio_state) (w : gmap Arch.pa (bv 8)),
         virtio_req_step (VirtioState c isr lo ah ui dk ca tk cp) mv i
         = Some (v', w) ->
         dom w ⊆ D /\ dom w ## dom ctl.

Definition virtio_queue_ok (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai lo : bv 16)
    (ah : gset (bv 16)) : Prop :=
  virtio_live c = true ->
    (* the published index is itself pinned: the device and the claimant agree
       on how far the driver has got *)
    read_bytes ctl (pa_off (vc_avail c) vq_idx_off) 2 = Some ai
    (* EVERY POSITION THE DEVICE MAY LOOK AT is one the claimant has
       accounted for, and after the pop/complete split there are two kinds:
       the entries it has not taken yet -- the interval [[lo, ai)] -- and the
       ones it took and has not finished ([ah]). *)
    /\ (forall p, vpos_pub lo ai p = true ->
          forall mv : vmem, mem_view ctl mv -> avail_ring_at c mv p ∈ S)
    /\ (forall h, h ∈ ah -> h ∈ S)
    (* ...and each of those is a well-formed request that writes inside the
       lease.  [S] is NOT all of [bv 16]: a driver cannot maintain
       well-formedness of ring slots it has not published, since xv6 leaves
       the stale entries of completed requests lying in the ring. *)
    /\ forall i, i ∈ S -> virtio_slot_ok c ctl D i.

(* Before the driver has made the queue live it owes nothing -- the device
   cannot even look at the ring.  This is what the power-on state (and hence
   whole-system adequacy) needs. *)
Lemma virtio_queue_ok_not_live (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai lo : bv 16)
    (ah : gset (bv 16)) :
  virtio_live c = false -> virtio_queue_ok c ctl D S ai lo ah.
Proof. intros Hlive Hl. rewrite Hlive in Hl. discriminate. Qed.

(* the pinned published index is the one the device reads *)
Lemma avail_idx_pinned (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (mv : vmem) (ai : bv 16) :
  mem_view ctl mv ->
  read_bytes ctl (pa_off (vc_avail c) vq_idx_off) 2 = Some ai ->
  avail_idx_at c mv = ai.
Proof.
  intros Hv Hr. unfold avail_idx_at. exact (view_word_read _ _ _ 2 ai Hv Hr).
Qed.

(* PAYOFF 1: the obligation rules out the write-anything step -- at EVERY
   position the device may serve, not just at the watermark. *)
Lemma virtio_queue_not_stalled (v : virtio_state) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai : bv 16) (mv : vmem) :
  virtio_queue_ok (v_cfg v) ctl D S ai (v_seen v) (v_inflight v) ->
  mem_view ctl mv ->
  virtio_stalled v mv = false.
Proof.
  intros Hok Hv.
  destruct (virtio_live (v_cfg v)) eqn:Hlive;
    [| exact (virtio_not_live_not_stalled v mv Hlive) ].
  destruct (Hok Hlive) as (Hai & Hcov & Hcovf & HS).
  (* the stall is looked for among the IN-FLIGHT positions now, and the
     obligation covers every one of them *)
  unfold virtio_stalled. rewrite Hlive.
  cbn [andb]. apply not_true_is_false. intro Hex.
  apply existsb_exists in Hex as (p & Hin & Hbad).
  apply elem_of_list_In, elem_of_elements in Hin.
  destruct (HS p (Hcovf p Hin) mv Hv) as [Hchain _].
  rewrite Hchain in Hbad. discriminate.
Qed.

(* PAYOFF 2: a real step writes inside the lease, misses the control region,
   and leaves the obligation standing over the positions that are left. *)
Lemma virtio_queue_ok_step (v : virtio_state) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai : bv 16) (mv : vmem)
    (i : bv 16) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_queue_ok (v_cfg v) ctl D S ai (v_seen v) (v_inflight v) ->
  mem_view ctl mv ->
  virtio_req_step v mv i = Some (v', w) ->
  dom w ⊆ D /\ dom w ## dom ctl
  /\ virtio_queue_ok (v_cfg v') ctl D S ai (v_seen v') (v_inflight v').
Proof.
  intros Hok Hv Hstep.
  destruct (virtio_req_step_shape _ _ _ _ _ Hstep) as (r & Hr & Hserve & _ & Hcomp).
  pose proof (virtio_serve_live _ _ _ Hserve) as Hlive.
  destruct (Hok Hlive) as (Hai & Hcov & Hcovf & HS).
  pose proof (virtio_serve_in _ _ _ Hserve) as Hin.
  (* re-index the step at the split state, so the slot obligation applies *)
  assert (Hsplit : virtio_req_step
                     (VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_inflight v)
                                  (v_used_idx v) (v_disk v) (v_cache v)
                                  (v_taken v) (v_cap v)) mv i
                   = Some (v', w)).
  { rewrite <- virtio_state_eta. exact Hstep. }
  destruct (proj2 (HS i (Hcovf i Hin) mv Hv) (v_isr v) (v_seen v) (v_inflight v)
              (v_used_idx v) (v_disk v) (v_cache v) (v_taken v) (v_cap v) v' w
              Hsplit) as [Hdw Hdisj].
  split; [exact Hdw|]. split; [exact Hdisj|].
  rewrite (virtio_req_step_cfg _ _ _ _ _ Hstep).
  (* THE COMPLETION ONLY SHRINKS THE IN-FLIGHT SET.  The pop index and the
     published index are both untouched, so the interval half of the
     obligation is literally unchanged and the in-flight half is inherited. *)
  assert (Hseen : v_seen v' = v_seen v)
    by exact (virtio_req_step_seen _ _ _ _ _ Hstep).
  assert (Hfl : v_inflight v' = v_inflight v ∖ {[ i ]})
    by exact (virtio_req_step_inflight _ _ _ _ _ Hstep).
  rewrite Hseen, Hfl. intros _.
  split; [exact Hai|]. split; [exact Hcov|]. split; [|exact HS].
  intros q Hq. apply Hcovf. set_solver.
Qed.

(* PAYOFF 3: neither a CAPTURE nor a DRAIN writes any memory, and neither
   moves the configuration, the watermark or the served set, so the
   obligation is preserved for free -- the same reason [virtio_cfg] is a
   separate record. *)
(* the interval SHRINKS from the left as the device takes entries: anything
   still untaken after the pop was untaken before it *)

(* PAYOFF 2b: THE POP.  It takes the entry at the pop index and nothing else
   moves, so the obligation follows: the untaken interval shrinks by one from
   the left, and the entry it lost is exactly the one that joined the
   in-flight set -- which the interval half had already accounted for. *)



(* [ctl] stays inside the memory the step produced -- the fact that makes the
   lease re-usable at the next step. *)
Lemma virtio_ctl_union (ctl w mm : gmap Arch.pa (bv 8)) :
  dom w ## dom ctl -> ctl ⊆ mm -> ctl ⊆ w ∪ mm.
Proof.
  intros Hdisj Hsub. apply map_subseteq_spec. intros a b Ha.
  assert (Hw : w !! a = None).
  { apply not_elem_of_dom. intro Hin.
    apply (Hdisj a Hin), elem_of_dom. by exists b. }
  rewrite (lookup_union_r w mm a Hw).
  exact (lookup_weaken _ _ _ _ Ha Hsub).
Qed.

(* ---------------------------------------------------------------------- *)
(* 8. Power-on state: reset configuration, empty interrupt, blank disk.    *)
(* ---------------------------------------------------------------------- *)

(* THE CAPACITY THE BOARD ATTACHES, in 512-byte sectors, and the one number
   in this file that is a property of the MACHINE rather than of the device:
   the model's [v_disk] is a total function, so the medium's size has to come
   from outside it.  This is the size of the image the conformance harness's
   `-drive` presents (tools/vtest/vtest.py, 64 KB); a machine that attaches a
   different image sets the field, which is what [set_vcap] is for.  No proof
   reads it -- xv6's driver never asks the device how big the disk is. *)
Definition virtio_capacity0 : Z := 128.

Definition virtio0_state : virtio_state :=
  VirtioState virtio_cfg0 zero32 zero16 ∅ zero16 (fun _ => byte_zero) ∅ None (Z_to_bv 64 virtio_capacity0).





(* the power-on device caches nothing, so the writethrough invariant holds *)


(* ---------------------------------------------------------------------- *)
(* 9. The driver's own sequence, run against this model.                   *)
(*                                                                        *)
(*    These are not lemmas anything else needs; they are a CHECK that the  *)
(*    register model matches kernel/virtio_disk.c -- the cheap way to      *)
(*    catch a wrong offset, a missing register or a mis-ordered status     *)
(*    bit, since every one of them closes by computation.  Keep them, and  *)
(*    extend them, when the modelled register set changes.                 *)
(* ---------------------------------------------------------------------- *)

(* the identification and capability reads [virtio_disk_init] insists on *)

(* "check maximum queue size": the capability read reports on the SELECTED
   queue, and the driver has selected queue 0 by then. *)

(* "ensure queue 0 is not in use": after the reset command it is not *)

(* "re-read status to ensure FEATURES_OK is set": a status write reads back *)


(* Exactly the writes [virtio_disk_init] performs, in order: reset,
   ACKNOWLEDGE, +DRIVER, the (empty) feature negotiation, +FEATURES_OK,
   select queue 0, size it at NUM = 8, the three ring addresses in low/high
   halves, QUEUE_READY, +DRIVER_OK. *)


(* The same configuration with the queue addresses named DIRECTLY.  The driver
   programs each as two 32-bit halves, and [set_lo_hi_id] reassembles them, so a
   driver spec can say "the queue is at the page I allocated" instead of leaking
   the half-splitting into its postcondition. *)
Definition virtio_init_cfg (pd pav pu : Arch.pa) : virtio_cfg :=
  VirtioCfg (Z_to_bv 32 15) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 8) true
            pd pav pu zero32 zero32 zero32 zero32.


Lemma virtio_init_cfg_live (pd pav pu : Arch.pa) :
  virtio_live (virtio_init_cfg pd pav pu) = true.
Proof. reflexivity. Qed.

(* THE THEOREM XV6'S INIT BUYS: the configuration the driver reaches has
   DECLINED the cache, so its disk is writeTHROUGH -- a write completes only
   once it is durable ([virtio_complete_ok]'s OUT arm).  That is a property
   of the DRIVER's negotiation, not a modelling assumption
   (claude-notes/projects/async-disk.md §2). *)
Lemma virtio_init_cfg_wce (pd pav pu : Arch.pa) :
  virtio_wce (virtio_init_cfg pd pav pu) = false.
Proof. by vm_compute. Qed.


(* No write in the sequence is refused, and the state it reaches is exactly
   the one above -- whatever the device was doing before. *)

(* ... and that state is one the device will actually serve requests from. *)

(* The interrupt line is still low when init finishes: the driver leaves no
   spurious completion behind for its first [virtio_disk_intr] to trip on. *)

(* -- the interrupt-status register only ever holds the two defined bits --

   [virtio_disk_intr] acknowledges with the mask 0x3, and for that to actually
   drop the line the PLIC gateway is watching, the register must not be holding
   anything else.  It never is: reset zeroes it and a completion only ever ORs
   in bit 0.  Stating that as an invariant is what makes the acknowledgement
   provably effective. *)

Definition virtio_isr_ok (v : virtio_state) : Prop :=
  Z.land (bv_unsigned (v_isr v)) 3 = bv_unsigned (v_isr v).

(* the two directions of "only bits 0..1", at the Z level *)
Lemma land3_bit_high (x i : Z) :
  Z.land x 3 = x -> 2 <= i -> Z.testbit x i = false.
Proof.
  intros Hx Hi. rewrite <- Hx, Z.land_spec.
  rewrite (Z.bits_above_log2 3 i); [ apply andb_false_r | lia | ].
  change (Z.log2 3) with 1. lia.
Qed.

Lemma land3_intro (x : Z) :
  (forall i, 2 <= i -> Z.testbit x i = false) -> Z.land x 3 = x.
Proof.
  intro Hhi. apply Z.bits_inj_iff'. intros i Hi. rewrite Z.land_spec.
  destruct (decide (2 <= i)) as [Hi2|Hi2].
  - rewrite (Hhi i Hi2). reflexivity.
  - assert (Hb : Z.testbit 3 i = true).
    { destruct (decide (i = 0)) as [->|Hne]; [reflexivity|].
      assert (i = 1) as -> by lia. reflexivity. }
    rewrite Hb. apply andb_true_r.
Qed.


(* ...and of a RESET device, whose ISR [virtio_reset] zeroes: the fourth of the
   reset facts above (stated here because [virtio_isr_ok] is defined here). *)
Lemma virtio_isr_ok_reset (v : virtio_state) : virtio_isr_ok (virtio_reset v).
Proof. by vm_compute. Qed.

(* a completion ORs in bit 0, which keeps the invariant *)
Lemma virtio_req_step_isr_ok (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) (i : bv 16) :
  virtio_isr_ok v -> virtio_req_step v mv i = Some (v', w) -> virtio_isr_ok v'.
Proof.
  intros Hok H. unfold virtio_isr_ok.
  rewrite (virtio_req_step_isr _ _ _ _ _ H), bv_or_unsigned.
  assert (Hone : bv_unsigned (Z_to_bv 32 vio_isr_used_buffer) = 1)
    by (by vm_compute).
  rewrite Hone. apply land3_intro. intros k Hk.
  rewrite Z.lor_spec, (land3_bit_high _ k Hok Hk).
  rewrite (Z.bits_above_log2 1 k); [ reflexivity | lia | ].
  change (Z.log2 1) with 0. lia.
Qed.

(* neither a capture nor a drain touches the interrupt-status register *)
Lemma virtio_pop_step_isr_ok (v : virtio_state) (mv : vmem) (v' : virtio_state) :
  virtio_isr_ok v -> virtio_pop_step v mv = Some v' -> virtio_isr_ok v'.
Proof.
  intros Hok H. destruct (virtio_pop_step_shape _ _ _ H) as [_ ->].
  unfold virtio_isr_ok in *. by rewrite virtio_pop_isr.
Qed.

Lemma virtio_capture_step_isr_ok (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (i : bv 16) :
  virtio_isr_ok v -> virtio_capture_step v mv i = Some v' -> virtio_isr_ok v'.
Proof.
  intros Hok Hs. unfold virtio_isr_ok.
  by rewrite (virtio_capture_step_isr _ _ _ _ Hs).
Qed.

Lemma virtio_drain_step_isr_ok (v : virtio_state) (s : Z)
    (v' : virtio_state) :
  virtio_isr_ok v -> virtio_drain_step v s = Some v' -> virtio_isr_ok v'.
Proof.
  intros Hok Hs. unfold virtio_isr_ok.
  by rewrite (virtio_drain_step_isr _ _ _ Hs).
Qed.

(* And so the acknowledgement [virtio_disk_intr] writes really does drop the
   line (0x3 = both defined ISR bits, which is the mask xv6 uses). *)
