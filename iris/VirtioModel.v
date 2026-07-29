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

(* This device offers NO optional features: the driver's negotiation clears
   every bit it knows about anyway, so the recorded driver-features word is
   only ever compared against the empty offer. *)
Definition virtio_device_features : Z := 0.

(* The largest queue this device supports.  The driver rejects 0 and anything
   below its own NUM (= 8), and programs exactly 8. *)
Definition virtio_queue_num_max : Z := 8.

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

(* device-status bits (virtio_config.h) *)
Definition vio_status_acknowledge : Z := 1.
Definition vio_status_driver : Z := 2.
Definition vio_status_driver_ok : Z := 4.
Definition vio_status_features_ok : Z := 8.

(* descriptor flags *)
Definition vring_desc_f_next : Z := 1.
Definition vring_desc_f_write : Z := 2.

(* block-request types (virtio spec §5.2) *)
Definition virtio_blk_t_in : Z := 0.    (* read the disk *)
Definition virtio_blk_t_out : Z := 1.   (* write the disk *)

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
Definition vq_size_ok (n : Z) : bool :=
  (n =? 1) || (n =? 2) || (n =? 4) || (n =? 8).

(* ---------------------------------------------------------------------- *)
(* 1. The device state.                                                    *)
(* ---------------------------------------------------------------------- *)

(* The DRIVER-OWNED half: written only by MMIO stores, never by the device.
   Everything the DMA footprint of a request depends on lives here, which is
   what makes [virtio_dma_ok] (§6) survive an autonomous step for free. *)
Record virtio_cfg := VirtioCfg {
  vc_status : bv 32;      (* device status (ACKNOWLEDGE/DRIVER/FEATURES_OK/DRIVER_OK) *)
  vc_dfeat  : bv 32;      (* the driver-features word, recorded and unused *)
  vc_qsel   : bv 32;      (* selected queue (only queue 0 exists) *)
  vc_qnum   : bv 32;      (* driver-programmed queue size *)
  vc_ready  : bool;       (* queue 0 ready *)
  vc_desc   : Arch.pa;    (* descriptor table base *)
  vc_avail  : Arch.pa;    (* available ring base (driver -> device) *)
  vc_used   : Arch.pa;    (* used ring base (device -> driver) *)
}.

Record virtio_state := VirtioState {
  v_cfg      : virtio_cfg;
  v_isr      : bv 32;        (* interrupt status; nonzero drives the irq line *)
  v_seen     : bv 16;        (* available-ring index consumed so far *)
  v_used_idx : bv 16;        (* used-ring index produced so far *)
  v_disk     : Z -> bv 8;    (* the disk image, byte-addressed *)
}.

(* replace the dynamic part, keeping the configuration *)
Definition set_vcfg (v : virtio_state) (c : virtio_cfg) : virtio_state :=
  VirtioState c (v_isr v) (v_seen v) (v_used_idx v) (v_disk v).

Definition zero32 : bv 32 := Z_to_bv 32 0.
Definition zero16 : bv 16 := Z_to_bv 16 0.
Definition zero64 : Arch.pa := Z_to_bv 64 0.

(* the queue is live: the driver has published addresses, sized the queue,
   flipped QUEUE_READY and set DRIVER_OK. *)
Definition virtio_driver_ok (c : virtio_cfg) : bool :=
  Z.testbit (bv_unsigned (vc_status c)) 2.

Definition virtio_live (c : virtio_cfg) : bool :=
  vc_ready c && virtio_driver_ok c && vq_size_ok (bv_unsigned (vc_qnum c)).

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
  else if off =? vio_off_device_features then Some (Z_to_bv 32 virtio_device_features)
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
  VirtioCfg zero32 zero32 zero32 zero32 false zero64 zero64 zero64.

Definition virtio_reset (v : virtio_state) : virtio_state :=
  VirtioState virtio_cfg0 zero32 zero16 zero16 (v_disk v).

Definition virtio_write (v : virtio_state) (off : Z) (w : bv 32)
  : option virtio_state :=
  let c := v_cfg v in
  if off =? vio_off_status then
    (* writing 0 is the reset command *)
    if bv_unsigned w =? 0 then Some (virtio_reset v)
    else Some (set_vcfg v (VirtioCfg w (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                     (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_driver_features then
    Some (set_vcfg v (VirtioCfg (vc_status c) w (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_sel then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) w (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)))
  (* -- the per-queue registers.  All of them address the SELECTED queue, and
        queue 0 is the only one that exists, so a write with any other
        selection is REFUSED: the machine is stuck, and a driver proof has to
        show it selected queue 0 first.  Same for an illegal queue size and a
        notification naming a queue that does not exist.  Refusing at the
        write is what keeps the queue geometry legal by construction, instead
        of leaving the device to cope with a configuration no real one
        would accept. -- *)
  else if off =? vio_off_queue_num then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    if negb (vq_size_ok (bv_unsigned w)) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) w
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_ready then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (negb (bv_unsigned w =? 0))
                                (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_notify then
    (* a hint only: this device polls the available ring itself.  The value is
       the queue number, so only 0 is meaningful. *)
    if negb (bv_unsigned w =? 0) then None else Some v
  else if off =? vio_off_interrupt_ack then
    Some (VirtioState c (Z_to_bv 32 (Z.land (bv_unsigned (v_isr v))
                                            (Z.lnot (bv_unsigned w))))
                      (v_seen v) (v_used_idx v) (v_disk v))
  else if off =? vio_off_queue_desc_low then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_lo (vc_desc c) w)
                                (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_desc_high then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_hi (vc_desc c) w)
                                (vc_avail c) (vc_used c)))
  else if off =? vio_off_driver_desc_low then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_lo (vc_avail c) w) (vc_used c)))
  else if off =? vio_off_driver_desc_high then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_hi (vc_avail c) w) (vc_used c)))
  else if off =? vio_off_device_desc_low then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c)
                                (set_lo (vc_used c) w)))
  else if off =? vio_off_device_desc_high then
    if negb (bv_unsigned (vc_qsel c) =? 0) then None else
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c)
                                (set_hi (vc_used c) w)))
  else None.

(* -- MMIO totality, for the offsets the xv6 driver names --

   [virtio_disk_init] reads MAGIC/VERSION/DEVICE_ID/VENDOR_ID/
   DEVICE_FEATURES/STATUS/QUEUE_READY/QUEUE_NUM_MAX and [virtio_disk_intr]
   reads INTERRUPT_STATUS; those nine are exactly the reads this device
   services.  A driver proof under a contents-agnostic device invariant
   cannot supply the result equation itself, so it needs these to conjure
   one. *)
Definition vio_readable (off : Z) : bool :=
  (off =? vio_off_magic_value) || (off =? vio_off_version)
  || (off =? vio_off_device_id) || (off =? vio_off_vendor_id)
  || (off =? vio_off_device_features) || (off =? vio_off_queue_num_max)
  || (off =? vio_off_queue_ready) || (off =? vio_off_interrupt_status)
  || (off =? vio_off_status).

(* A write is accepted when the register exists AND the driver has put the
   device in a state where the write means something: the per-queue registers
   need queue 0 selected, QUEUE_NUM needs a legal size, QUEUE_NOTIFY needs an
   existing queue number.  Anything else is stuck -- deliberately, so that a
   driver proof has to establish these rather than have the device paper over
   them (see the header). *)
Definition vio_write_ok (c : virtio_cfg) (off : Z) (w : bv 32) : bool :=
  (off =? vio_off_status) || (off =? vio_off_driver_features)
  || (off =? vio_off_queue_sel) || (off =? vio_off_interrupt_ack)
  || ((off =? vio_off_queue_notify) && (bv_unsigned w =? 0))
  || ((off =? vio_off_queue_num) && (bv_unsigned (vc_qsel c) =? 0)
      && vq_size_ok (bv_unsigned w))
  || ((off =? vio_off_queue_ready) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_queue_desc_low) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_queue_desc_high) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_driver_desc_low) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_driver_desc_high) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_device_desc_low) && (bv_unsigned (vc_qsel c) =? 0))
  || ((off =? vio_off_device_desc_high) && (bv_unsigned (vc_qsel c) =? 0)).

Lemma virtio_read_total (v : virtio_state) (off : Z) :
  vio_readable off = true -> exists w, virtio_read v off = Some w.
Proof.
  unfold vio_readable. intro H.
  repeat (apply orb_prop in H as [H|H]);
    apply Z.eqb_eq in H; subst off; unfold virtio_read;
    eexists; reflexivity.
Qed.

Lemma virtio_write_total (v : virtio_state) (off : Z) (w : bv 32) :
  vio_write_ok (v_cfg v) off w = true -> exists v', virtio_write v off w = Some v'.
Proof.
  unfold vio_write_ok. intro H.
  repeat (apply orb_prop in H as [H|H]);
    repeat (apply andb_prop in H as [H ?]);
    apply Z.eqb_eq in H; subst off;
    unfold virtio_write; cbv zeta;
    repeat (match goal with
            | Hx : (_ =? _) = true |- _ => rewrite Hx; clear Hx
            | Hx : vq_size_ok _ = true |- _ => rewrite Hx; clear Hx
            end);
    destruct (bv_unsigned w =? 0); eexists; reflexivity.
Qed.

(* The two MMIO writes the driver performs while the queue is LIVE -- the
   completion acknowledgement in [virtio_disk_intr] and the queue kick in
   [virtio_disk_rw] -- leave the configuration alone.  So they cannot
   invalidate a DMA lease (WpVirtio.virtio_lease_cfg), which is what lets the
   steady-state driver path run without re-establishing one. *)
Definition vio_cfg_stable (off : Z) : bool :=
  (off =? vio_off_queue_notify) || (off =? vio_off_interrupt_ack).

Lemma virtio_write_seen (v : virtio_state) (off : Z) (w : bv 32)
    (v' : virtio_state) :
  vio_cfg_stable off = true ->
  virtio_write v off w = Some v' -> v_seen v' = v_seen v.
Proof.
  unfold vio_cfg_stable. intro H.
  apply orb_prop in H as [H|H]; apply Z.eqb_eq in H; subst off;
    unfold virtio_write; cbv zeta.
  - destruct (negb (bv_unsigned w =? 0)); [discriminate|].
    intro He; injection He as <-; reflexivity.
  - intro He; injection He as <-; reflexivity.
Qed.

Lemma virtio_write_cfg_stable (v : virtio_state) (off : Z) (w : bv 32)
    (v' : virtio_state) :
  vio_cfg_stable off = true ->
  virtio_write v off w = Some v' -> v_cfg v' = v_cfg v.
Proof.
  unfold vio_cfg_stable. intro H.
  apply orb_prop in H as [H|H]; apply Z.eqb_eq in H; subst off;
    unfold virtio_write; cbv zeta.
  - destruct (negb (bv_unsigned w =? 0)); [discriminate|].
    intro He; injection He as <-; reflexivity.
  - intro He; injection He as <-; reflexivity.
Qed.

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
  v = VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_used_idx v) (v_disk v).
Proof. by destruct v. Qed.

(* No MMIO write touches the disk image -- not even the reset command. *)
Lemma virtio_write_disk (v : virtio_state) (off : Z) (w : bv 32) (v' : virtio_state) :
  virtio_write v off w = Some v' -> v_disk v' = v_disk v.
Proof.
  unfold virtio_write. cbv zeta.
  destruct (off =? vio_off_status).
  { destruct (bv_unsigned w =? 0); intro H; injection H as <-; reflexivity. }
  repeat (destruct (off =? _);
          [ repeat (destruct (negb _); [discriminate|]);
            intro H; injection H as <-; reflexivity |]).
  discriminate.
Qed.

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
Definition rd16 (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) : option (bv 16) :=
  read_bytes mm a 2.
Definition rd32 (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) : option (bv 32) :=
  read_bytes mm a 4.
Definition rd64 (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) : option (bv 64) :=
  read_bytes mm a 8.

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
Definition chain_at (c : virtio_cfg) (mv : vmem) (i : bv 16)
  : option (bv 16 * vq_desc * vq_desc * vq_desc) :=
  let qnum := bv_unsigned (vc_qnum c) in
  let h := avail_ring_at c mv i in
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

Definition virtio_chain_ok (c : virtio_cfg) (mv : vmem) (i : bv 16) : bool :=
  match chain_at c mv i with Some _ => true | None => false end.

(* the decoded request: what the chain says to do, and where to report it *)
Record vio_req := VioReq {
  vr_head   : bv 16;    (* head descriptor index -- goes in the used ring *)
  vr_type   : bv 32;    (* VIRTIO_BLK_T_IN / _OUT, or anything else *)
  vr_sector : bv 64;
  vr_buf    : Arch.pa;  (* data buffer *)
  vr_len    : bv 32;    (* data length *)
  vr_status : Arch.pa;  (* the one-byte status the device must write *)
}.

Definition req_at (c : virtio_cfg) (mv : vmem) (i : bv 16) : option vio_req :=
  match chain_at c mv i with
  | None => None
  | Some (h, d0, d1, d2) =>
      (* the header: type:4 reserved:4 sector:8 *)
      Some (VioReq h (view_word mv (vd_addr d0) 4)
                     (view_word mv (pa_off (vd_addr d0) 8) 8)
                     (vd_addr d1) (vd_len d1) (vd_addr d2))
  end.

Lemma req_at_chain (c : virtio_cfg) (mv : vmem) (i : bv 16) :
  virtio_chain_ok c mv i = true -> exists r, req_at c mv i = Some r.
Proof.
  unfold virtio_chain_ok, req_at.
  destruct (chain_at c mv i) as [[[[h d0] d1] d2]|]; [|discriminate].
  intros _. by eexists.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. The autonomous request step: the device's own execution context.     *)
(* ---------------------------------------------------------------------- *)

(* Completing a request writes, in one transition: the transferred data (for
   a disk READ), the status byte, the used-ring element, and the used index.
   Ordering the index bump last is what the driver's completion test relies
   on, and doing it all atomically gives exactly that. *)
Definition virtio_used_writes (c : virtio_cfg) (ui : bv 16) (r : vio_req)
  : gmap Arch.pa (bv 8) :=
  let qnum := bv_unsigned (vc_qnum c) in
  let slot := bv_unsigned ui mod qnum in
  let elem := pa_off (vc_used c) (vq_used_ring_off + vq_used_elem_size * slot) in
  let m1 := write_bytes ∅ elem 4 (Z_to_bv 32 (bv_unsigned (vr_head r))) in
  let m2 := write_bytes m1 (pa_off elem 4) 4 (vr_len r) in
  write_bytes m2 (pa_off (vc_used c) vq_idx_off) 2 (bv_add ui (Z_to_bv 16 1)).

Definition byte_zero : bv 8 := Z_to_bv 8 0.

(* Completing ONE parsed request.  TOTAL: there is no request the device
   refuses to answer.  An unrecognised type is reported back with status
   UNSUPP and no data transfer, exactly as a real block device does. *)
Definition virtio_complete (v : virtio_state) (mv : vmem) (r : vio_req)
  : virtio_state * gmap Arch.pa (bv 8) :=
  let n := Z.to_nat (bv_unsigned (vr_len r)) in
  let doff := bv_unsigned (vr_sector r) * virtio_sector_size in
  let st := if (bv_unsigned (vr_type r) =? virtio_blk_t_in)
               || (bv_unsigned (vr_type r) =? virtio_blk_t_out)
            then virtio_blk_s_ok else virtio_blk_s_unsupp in
  let ws := <[ vr_status r := Z_to_bv 8 st ]>
              (virtio_used_writes (v_cfg v) (v_used_idx v) r) in
  let vd := fun dk => VirtioState (v_cfg v)
                        (bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer))
                        (bv_add (v_seen v) (Z_to_bv 16 1))
                        (bv_add (v_used_idx v) (Z_to_bv 16 1)) dk in
  if bv_unsigned (vr_type r) =? virtio_blk_t_in then
    (* read the disk: the device WRITES the driver's buffer *)
    (vd (v_disk v), write_byte_list ws (vr_buf r) (disk_read (v_disk v) doff n))
  else if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    (* write the disk: the device READS the driver's buffer *)
    (vd (disk_write (v_disk v) doff (view_bytes mv (vr_buf r) n)), ws)
  else
    (* unsupported: the status byte and the used-ring report, nothing else *)
    (vd (v_disk v), ws).

(* the device has work to do: the queue is live and the driver has published
   an entry the device has not taken yet *)
Definition virtio_pending (v : virtio_state) (mv : vmem) : bool :=
  virtio_live (v_cfg v)
  && negb (bv_unsigned (avail_idx_at (v_cfg v) mv) =? bv_unsigned (v_seen v)).

Definition virtio_req_step (v : virtio_state) (mv : vmem)
  : option (virtio_state * gmap Arch.pa (bv 8)) :=
  if negb (virtio_pending v mv) then None
  else match req_at (v_cfg v) mv (v_seen v) with
       | None => None
       | Some r => Some (virtio_complete v mv r)
       end.

(* THE hole this model must not have.  [virtio_stalled] is "the device owes
   an answer and this model does not have one": it has work to do, and the
   step above produced nothing.  By construction that happens for exactly one
   reason -- the published chain is malformed ([virtio_stalled_chain]) -- and
   RiscvLang gives that case a step that may write anything anywhere, so a
   driver must PROVE it does not happen rather than benefit from it. *)
Definition virtio_stalled (v : virtio_state) (mv : vmem) : bool :=
  virtio_pending v mv && negb (virtio_chain_ok (v_cfg v) mv (v_seen v)).

Lemma virtio_stalled_step (v : virtio_state) (mv : vmem) :
  virtio_stalled v mv = true ->
  virtio_pending v mv = true /\ virtio_req_step v mv = None.
Proof.
  unfold virtio_stalled, virtio_req_step, virtio_chain_ok, req_at.
  intro H. apply andb_prop in H as [Hp Hc]. rewrite Hp. cbn [negb].
  destruct (chain_at (v_cfg v) mv (v_seen v)) as [[[[h d0] d1] d2]|];
    [ discriminate | ].
  split; reflexivity.
Qed.

Lemma virtio_not_stalled_step (v : virtio_state) (mv : vmem) :
  virtio_pending v mv = true -> virtio_stalled v mv = false ->
  exists v' w, virtio_req_step v mv = Some (v', w).
Proof.
  intros Hp Hs. unfold virtio_stalled in Hs. rewrite Hp in Hs. cbn [andb] in Hs.
  apply negb_false_iff in Hs.
  destruct (req_at_chain _ _ _ Hs) as [r Hr].
  unfold virtio_req_step. rewrite Hp. cbn [negb]. rewrite Hr.
  destruct (virtio_complete v mv r) as [v' w]. exists v', w. reflexivity.
Qed.

(* -- what a step does and does not touch -- *)

(* THE structural fact about an autonomous step, and the reason [virtio_cfg]
   is a separate record: the device never writes its own configuration. *)
Lemma virtio_req_step_cfg (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) -> v_cfg v' = v_cfg v.
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_pending v mv)); [discriminate|].
  destruct (req_at (v_cfg v) mv (v_seen v)) as [r|]; [|discriminate].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    [ intro H; injection H as H1 H2; by subst v' | ].
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* the device takes the entries in order, one per step *)
Lemma virtio_req_step_seen (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) ->
  v_seen v' = bv_add (v_seen v) (Z_to_bv 16 1).
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_pending v mv)); [discriminate|].
  destruct (req_at (v_cfg v) mv (v_seen v)) as [r|]; [|discriminate].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    [ intro H; injection H as H1 H2; by subst v' | ].
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out);
    intro H; injection H as H1 H2; by subst v'.
Qed.

(* The used-buffer bit of the interrupt-status register goes UP on completion,
   and only the driver's INTERRUPT_ACK can bring it down again. *)
Lemma virtio_req_step_isr (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) ->
  v_isr v' = bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer).
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_pending v mv)); [discriminate|].
  destruct (req_at (v_cfg v) mv (v_seen v)) as [r|]; [|discriminate].
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in);
    [ intro H; injection H as H1 H2; by subst v' | ].
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out);
    intro H; injection H as H1 H2; by subst v'.
Qed.

Lemma bv_or_bit0_irq (x : bv 32) :
  bv_unsigned (bv_or x (Z_to_bv 32 vio_isr_used_buffer)) =? 0 = false.
Proof.
  apply Z.eqb_neq. rewrite bv_or_unsigned.
  assert (Hone : bv_unsigned (Z_to_bv 32 vio_isr_used_buffer) = 1)
    by (by vm_compute).
  intro Hz.
  assert (Hbit0 : Z.testbit (Z.lor (bv_unsigned x)
                     (bv_unsigned (Z_to_bv 32 vio_isr_used_buffer))) 0 = true).
  { rewrite Z.lor_spec, Hone. apply orb_true_r. }
  rewrite Hz in Hbit0. by cbn in Hbit0.
Qed.

(* A step always raises the interrupt line. *)
Lemma virtio_req_step_irq (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) -> virtio_irq v' = true.
Proof.
  intro H. unfold virtio_irq. rewrite (virtio_req_step_isr _ _ _ _ H).
  by rewrite bv_or_bit0_irq.
Qed.

Lemma virtio_req_step_not_live (v : virtio_state) (mv : vmem) :
  virtio_live (v_cfg v) = false -> virtio_req_step v mv = None.
Proof.
  intro H. unfold virtio_req_step, virtio_pending. by rewrite H.
Qed.

Lemma virtio_not_live_not_stalled (v : virtio_state) (mv : vmem) :
  virtio_live (v_cfg v) = false -> virtio_stalled v mv = false.
Proof.
  intro H. unfold virtio_stalled, virtio_pending. by rewrite H.
Qed.

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
(*    reach.  It is closed under advancing by one UNTIL the position       *)
(*    reaches the published index [ai], which is exactly the reachable set *)
(*    without any 16-bit window arithmetic -- and, importantly, NOT all of  *)
(*    [bv 16]: a driver cannot maintain well-formedness of ring slots it   *)
(*    has not published, since xv6 leaves the stale entries of completed   *)
(*    requests lying in the ring.                                          *)
(* ---------------------------------------------------------------------- *)

(* the request published at position [i] is well formed, and writes only
   inside the lease [D] and never over the control region *)
Definition virtio_slot_ok (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (i : bv 16) : Prop :=
  forall mv : vmem, mem_view ctl mv ->
    virtio_chain_ok c mv i = true
    /\ forall (isr : bv 32) (ui : bv 16) (dk : Z -> bv 8)
              (v' : virtio_state) (w : gmap Arch.pa (bv 8)),
         virtio_req_step (VirtioState c isr i ui dk) mv = Some (v', w) ->
         dom w ⊆ D /\ dom w ## dom ctl.

Definition virtio_queue_ok (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai sn : bv 16) : Prop :=
  virtio_live c = true ->
    (* the published index is itself pinned: the device and the claimant agree
       on how far the driver has got *)
    read_bytes ctl (pa_off (vc_avail c) vq_idx_off) 2 = Some ai
    /\ (sn = ai \/ sn ∈ S)
    /\ forall i, i ∈ S ->
         virtio_slot_ok c ctl D i
         /\ (bv_add i (Z_to_bv 16 1) = ai \/ bv_add i (Z_to_bv 16 1) ∈ S).

(* Before the driver has made the queue live it owes nothing -- the device
   cannot even look at the ring.  This is what the power-on state (and hence
   whole-system adequacy) needs. *)
Lemma virtio_queue_ok_not_live (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai sn : bv 16) :
  virtio_live c = false -> virtio_queue_ok c ctl D S ai sn.
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

(* PAYOFF 1: the obligation rules out the write-anything step. *)
Lemma virtio_queue_not_stalled (v : virtio_state) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai : bv 16) (mv : vmem) :
  virtio_queue_ok (v_cfg v) ctl D S ai (v_seen v) ->
  mem_view ctl mv ->
  virtio_stalled v mv = false.
Proof.
  intros Hok Hv.
  destruct (virtio_live (v_cfg v)) eqn:Hlive;
    [| exact (virtio_not_live_not_stalled v mv Hlive) ].
  destruct (Hok Hlive) as (Hai & Hpos & HS).
  unfold virtio_stalled, virtio_pending. rewrite Hlive. cbn [andb].
  destruct (bv_unsigned (avail_idx_at (v_cfg v) mv) =? bv_unsigned (v_seen v))
    eqn:Heq; [reflexivity|].
  cbn [negb andb].
  assert (Hin : v_seen v ∈ S).
  { destruct Hpos as [Hpos|Hpos]; [|exact Hpos].
    exfalso. rewrite (avail_idx_pinned _ _ _ _ Hv Hai), <- Hpos in Heq.
    by rewrite Z.eqb_refl in Heq. }
  destruct (HS _ Hin) as [Hslot _].
  rewrite (proj1 (Hslot mv Hv)). reflexivity.
Qed.

(* PAYOFF 2: a real step writes inside the lease, misses the control region,
   and leaves the obligation standing at the position it advanced to. *)
Lemma virtio_queue_ok_step (v : virtio_state) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (S : gset (bv 16)) (ai : bv 16) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_queue_ok (v_cfg v) ctl D S ai (v_seen v) ->
  mem_view ctl mv ->
  virtio_req_step v mv = Some (v', w) ->
  dom w ⊆ D /\ dom w ## dom ctl
  /\ virtio_queue_ok (v_cfg v') ctl D S ai (v_seen v').
Proof.
  intros Hok Hv Hstep.
  (* the step happened, so the queue is live and an entry is published *)
  assert (Hp : virtio_pending v mv = true).
  { unfold virtio_req_step in Hstep.
    destruct (virtio_pending v mv) eqn:Hp; [reflexivity|]. by cbn in Hstep. }
  assert (Hlive : virtio_live (v_cfg v) = true).
  { unfold virtio_pending in Hp. by apply andb_prop in Hp as [? _]. }
  destruct (Hok Hlive) as (Hai & Hpos & HS).
  assert (Hin : v_seen v ∈ S).
  { destruct Hpos as [Hpos|Hpos]; [|exact Hpos].
    exfalso. unfold virtio_pending in Hp. apply andb_prop in Hp as [_ Hne].
    apply negb_true_iff, Z.eqb_neq in Hne.
    rewrite (avail_idx_pinned _ _ _ _ Hv Hai), <- Hpos in Hne. exact (Hne eq_refl). }
  destruct (HS _ Hin) as [Hslot Hnext].
  (* re-index the step at the split state, so the slot obligation applies *)
  assert (Hsplit : virtio_req_step
                     (VirtioState (v_cfg v) (v_isr v) (v_seen v)
                                  (v_used_idx v) (v_disk v)) mv = Some (v', w)).
  { rewrite <- virtio_state_eta. exact Hstep. }
  destruct (proj2 (Hslot mv Hv) (v_isr v) (v_used_idx v) (v_disk v) v' w Hsplit)
    as [Hdw Hdisj].
  split; [exact Hdw|]. split; [exact Hdisj|].
  rewrite (virtio_req_step_cfg _ _ _ _ Hstep),
          (virtio_req_step_seen _ _ _ _ Hstep).
  intros _. split; [exact Hai|]. split; [|exact HS].
  destruct Hnext as [Hnext|Hnext]; [left|right]; exact Hnext.
Qed.

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

Definition virtio0_state : virtio_state :=
  VirtioState virtio_cfg0 zero32 zero16 zero16 (fun _ => byte_zero).

Lemma virtio0_not_live : virtio_live (v_cfg virtio0_state) = false.
Proof. reflexivity. Qed.

Lemma virtio0_queue_ok ctl D S ai sn :
  virtio_queue_ok (v_cfg virtio0_state) ctl D S ai sn.
Proof. apply virtio_queue_ok_not_live, virtio0_not_live. Qed.

Lemma virtio0_irq : virtio_irq virtio0_state = false.
Proof. reflexivity. Qed.

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
Lemma virtio_ident_reads (v : virtio_state) :
  virtio_read v vio_off_magic_value = Some (Z_to_bv 32 0x74726976)
  /\ virtio_read v vio_off_version = Some (Z_to_bv 32 2)
  /\ virtio_read v vio_off_device_id = Some (Z_to_bv 32 2)
  /\ virtio_read v vio_off_vendor_id = Some (Z_to_bv 32 0x554d4551).
Proof. repeat split; reflexivity. Qed.

(* "check maximum queue size": the capability read reports on the SELECTED
   queue, and the driver has selected queue 0 by then. *)
Lemma virtio_queue_num_max_read (v : virtio_state) :
  bv_unsigned (vc_qsel (v_cfg v)) = 0 ->
  virtio_read v vio_off_queue_num_max = Some (Z_to_bv 32 8).
Proof. intro H. unfold virtio_read. cbv zeta. rewrite H. reflexivity. Qed.

(* "ensure queue 0 is not in use": after the reset command it is not *)
Lemma virtio_reset_not_ready (v : virtio_state) :
  virtio_read (virtio_reset v) vio_off_queue_ready = Some (Z_to_bv 32 0).
Proof. reflexivity. Qed.

(* "re-read status to ensure FEATURES_OK is set": a status write reads back *)
Lemma virtio_status_readback (v : virtio_state) (w : bv 32) (v' : virtio_state) :
  bv_unsigned w <> 0 ->
  virtio_write v vio_off_status w = Some v' ->
  virtio_read v' vio_off_status = Some w.
Proof.
  intros Hnz. unfold virtio_write. cbv zeta. cbn [Z.eqb].
  destruct (bv_unsigned w =? 0) eqn:E; [ by apply Z.eqb_eq in E | ].
  intro H. injection H as <-. reflexivity.
Qed.

Definition virtio_writes (v : virtio_state) (ws : list (Z * bv 32))
  : option virtio_state :=
  fold_left (fun ov p => match ov with
                         | Some v0 => virtio_write v0 (fst p) (snd p)
                         | None => None
                         end) ws (Some v).

(* Exactly the writes [virtio_disk_init] performs, in order: reset,
   ACKNOWLEDGE, +DRIVER, the (empty) feature negotiation, +FEATURES_OK,
   select queue 0, size it at NUM = 8, the three ring addresses in low/high
   halves, QUEUE_READY, +DRIVER_OK. *)
Definition virtio_init_seq (dl dh al ah ul uh : bv 32) : list (Z * bv 32) :=
  [ (vio_off_status, Z_to_bv 32 0);
    (vio_off_status, Z_to_bv 32 1);                 (* ACKNOWLEDGE *)
    (vio_off_status, Z_to_bv 32 3);                 (* + DRIVER *)
    (vio_off_driver_features, Z_to_bv 32 0);
    (vio_off_status, Z_to_bv 32 11);                (* + FEATURES_OK *)
    (vio_off_queue_sel, Z_to_bv 32 0);
    (vio_off_queue_num, Z_to_bv 32 8);
    (vio_off_queue_desc_low, dl); (vio_off_queue_desc_high, dh);
    (vio_off_driver_desc_low, al); (vio_off_driver_desc_high, ah);
    (vio_off_device_desc_low, ul); (vio_off_device_desc_high, uh);
    (vio_off_queue_ready, Z_to_bv 32 1);
    (vio_off_status, Z_to_bv 32 15) ].              (* + DRIVER_OK *)

Definition virtio_init_post (v : virtio_state) (dl dh al ah ul uh : bv 32)
  : virtio_state :=
  VirtioState (VirtioCfg (Z_to_bv 32 15) (Z_to_bv 32 0) (Z_to_bv 32 0)
                         (Z_to_bv 32 8) true
                         (set_hi (set_lo zero64 dl) dh)
                         (set_hi (set_lo zero64 al) ah)
                         (set_hi (set_lo zero64 ul) uh))
              zero32 zero16 zero16 (v_disk v).

(* The same configuration with the queue addresses named DIRECTLY.  The driver
   programs each as two 32-bit halves, and [set_lo_hi_id] reassembles them, so a
   driver spec can say "the queue is at the page I allocated" instead of leaking
   the half-splitting into its postcondition. *)
Definition virtio_init_cfg (pd pav pu : Arch.pa) : virtio_cfg :=
  VirtioCfg (Z_to_bv 32 15) (Z_to_bv 32 0) (Z_to_bv 32 0) (Z_to_bv 32 8) true
            pd pav pu.

Lemma virtio_init_post_cfg (v : virtio_state) (pd pav pu : Arch.pa) :
  virtio_init_post v (lo32 pd) (hi32 pd) (lo32 pav) (hi32 pav) (lo32 pu) (hi32 pu)
  = VirtioState (virtio_init_cfg pd pav pu) zero32 zero16 zero16 (v_disk v).
Proof.
  unfold virtio_init_post, virtio_init_cfg. by rewrite !set_lo_hi_id.
Qed.

Lemma virtio_init_cfg_live (pd pav pu : Arch.pa) :
  virtio_live (virtio_init_cfg pd pav pu) = true.
Proof. reflexivity. Qed.

(* No write in the sequence is refused, and the state it reaches is exactly
   the one above -- whatever the device was doing before. *)
Lemma virtio_init_seq_post (v : virtio_state) (dl dh al ah ul uh : bv 32) :
  virtio_writes v (virtio_init_seq dl dh al ah ul uh)
  = Some (virtio_init_post v dl dh al ah ul uh).
Proof. reflexivity. Qed.

(* ... and that state is one the device will actually serve requests from. *)
Lemma virtio_init_post_live (v : virtio_state) (dl dh al ah ul uh : bv 32) :
  virtio_live (v_cfg (virtio_init_post v dl dh al ah ul uh)) = true.
Proof. reflexivity. Qed.

(* The interrupt line is still low when init finishes: the driver leaves no
   spurious completion behind for its first [virtio_disk_intr] to trip on. *)
Lemma virtio_init_post_irq (v : virtio_state) (dl dh al ah ul uh : bv 32) :
  virtio_irq (virtio_init_post v dl dh al ah ul uh) = false.
Proof. reflexivity. Qed.

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

Lemma virtio_isr_ok0 : virtio_isr_ok virtio0_state.
Proof. by vm_compute. Qed.

(* a completion ORs in bit 0, which keeps the invariant *)
Lemma virtio_req_step_isr_ok (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_isr_ok v -> virtio_req_step v mv = Some (v', w) -> virtio_isr_ok v'.
Proof.
  intros Hok H. unfold virtio_isr_ok.
  rewrite (virtio_req_step_isr _ _ _ _ H), bv_or_unsigned.
  assert (Hone : bv_unsigned (Z_to_bv 32 vio_isr_used_buffer) = 1)
    by (by vm_compute).
  rewrite Hone. apply land3_intro. intros i Hi.
  rewrite Z.lor_spec, (land3_bit_high _ i Hok Hi).
  rewrite (Z.bits_above_log2 1 i); [ reflexivity | lia | ].
  change (Z.log2 1) with 0. lia.
Qed.

(* And so the acknowledgement [virtio_disk_intr] writes really does drop the
   line (0x3 = both defined ISR bits, which is the mask xv6 uses). *)
Lemma virtio_ack_clears (v : virtio_state) (v' : virtio_state) :
  virtio_isr_ok v ->
  virtio_write v vio_off_interrupt_ack (Z_to_bv 32 3) = Some v' ->
  virtio_irq v' = false.
Proof.
  intro Hok. unfold virtio_write. cbv zeta. cbn [Z.eqb].
  intro H. injection H as <-. unfold virtio_irq. cbn [v_isr].
  apply negb_false_iff, Z.eqb_eq.
  assert (Hthree : bv_unsigned (Z_to_bv 32 3) = 3) by (by vm_compute).
  rewrite Hthree.
  assert (Hz : Z.land (bv_unsigned (v_isr v)) (Z.lnot 3) = 0).
  { apply Z.bits_inj_iff'. intros i Hi.
    rewrite Z.bits_0, Z.land_spec, Z.lnot_spec by lia.
    destruct (decide (2 <= i)) as [Hi2|Hi2].
    - rewrite (land3_bit_high _ i Hok Hi2). reflexivity.
    - assert (Hb : Z.testbit 3 i = true).
      { destruct (decide (i = 0)) as [->|Hne]; [reflexivity|].
        assert (i = 1) as -> by lia. reflexivity. }
      rewrite Hb. apply andb_false_r. }
  rewrite Hz. by vm_compute.
Qed.
