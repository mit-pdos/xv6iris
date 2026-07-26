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
(*     mem_writes)], and hence RiscvLang's [dev_step] carries the memory.   *)
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
  vc_ready c && virtio_driver_ok c.

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
  else if off =? vio_off_queue_num_max then Some (Z_to_bv 32 virtio_queue_num_max)
  else if off =? vio_off_queue_ready then
    Some (Z_to_bv 32 (if vc_ready c then 1 else 0))
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
  else if off =? vio_off_queue_num then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) w
                                (vc_ready c) (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_ready then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (negb (bv_unsigned w =? 0))
                                (vc_desc c) (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_notify then
    (* a hint only: this device polls the available ring itself *)
    Some v
  else if off =? vio_off_interrupt_ack then
    Some (VirtioState c (Z_to_bv 32 (Z.land (bv_unsigned (v_isr v))
                                            (Z.lnot (bv_unsigned w))))
                      (v_seen v) (v_used_idx v) (v_disk v))
  else if off =? vio_off_queue_desc_low then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_lo (vc_desc c) w)
                                (vc_avail c) (vc_used c)))
  else if off =? vio_off_queue_desc_high then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (set_hi (vc_desc c) w)
                                (vc_avail c) (vc_used c)))
  else if off =? vio_off_driver_desc_low then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_lo (vc_avail c) w) (vc_used c)))
  else if off =? vio_off_driver_desc_high then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c)
                                (set_hi (vc_avail c) w) (vc_used c)))
  else if off =? vio_off_device_desc_low then
    Some (set_vcfg v (VirtioCfg (vc_status c) (vc_dfeat c) (vc_qsel c) (vc_qnum c)
                                (vc_ready c) (vc_desc c) (vc_avail c)
                                (set_lo (vc_used c) w)))
  else if off =? vio_off_device_desc_high then
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

Definition vio_writable (off : Z) : bool :=
  (off =? vio_off_status) || (off =? vio_off_driver_features)
  || (off =? vio_off_queue_sel) || (off =? vio_off_queue_num)
  || (off =? vio_off_queue_ready) || (off =? vio_off_queue_notify)
  || (off =? vio_off_interrupt_ack)
  || (off =? vio_off_queue_desc_low) || (off =? vio_off_queue_desc_high)
  || (off =? vio_off_driver_desc_low) || (off =? vio_off_driver_desc_high)
  || (off =? vio_off_device_desc_low) || (off =? vio_off_device_desc_high).

Lemma virtio_read_total (v : virtio_state) (off : Z) :
  vio_readable off = true -> exists w, virtio_read v off = Some w.
Proof.
  unfold vio_readable. intro H.
  repeat (apply orb_prop in H as [H|H]);
    apply Z.eqb_eq in H; subst off; unfold virtio_read;
    eexists; reflexivity.
Qed.

Lemma virtio_write_total (v : virtio_state) (off : Z) (w : bv 32) :
  vio_writable off = true -> exists v', virtio_write v off w = Some v'.
Proof.
  unfold vio_writable. intro H.
  repeat (apply orb_prop in H as [H|H]);
    apply Z.eqb_eq in H; subst off; unfold virtio_write; cbv zeta;
    destruct (bv_unsigned w =? 0); eexists; reflexivity.
Qed.

(* The two MMIO writes the driver performs while the queue is LIVE -- the
   completion acknowledgement in [virtio_disk_intr] and the queue kick in
   [virtio_disk_rw] -- leave the configuration alone.  So they cannot
   invalidate a DMA lease (WpVirtio.virtio_lease_cfg), which is what lets the
   steady-state driver path run without re-establishing one. *)
Definition vio_cfg_stable (off : Z) : bool :=
  (off =? vio_off_queue_notify) || (off =? vio_off_interrupt_ack).

Lemma virtio_write_cfg_stable (v : virtio_state) (off : Z) (w : bv 32)
    (v' : virtio_state) :
  vio_cfg_stable off = true ->
  virtio_write v off w = Some v' -> v_cfg v' = v_cfg v.
Proof.
  unfold vio_cfg_stable. intro H.
  apply orb_prop in H as [H|H]; apply Z.eqb_eq in H; subst off;
    unfold virtio_write; cbv zeta;
    intro He; injection He as <-; reflexivity.
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
  repeat (destruct (off =? _); [ intro H; injection H as <-; reflexivity |]).
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
(* 4. Reading a request out of the virtqueue.                              *)
(*                                                                         *)
(*    xv6's disk transfers always use the legacy three-descriptor chain of  *)
(*    spec §5.2: a device-readable 16-byte header (type/reserved/sector), a *)
(*    data descriptor whose direction follows the request type, and a       *)
(*    device-writable one-byte status.  This is what the device parses.     *)
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

Definition read_desc (mm : gmap Arch.pa (bv 8)) (dtab : Arch.pa) (i : Z)
  : option vq_desc :=
  let base := pa_off dtab (vq_desc_size * i) in
  match rd64 mm base, rd32 mm (pa_off base 8),
        rd16 mm (pa_off base 12), rd16 mm (pa_off base 14) with
  | Some a, Some l, Some f, Some nx => Some (VqDesc a l f nx)
  | _, _, _, _ => None
  end.

(* the available ring: [flags:2 idx:2 ring[qnum]:2each] *)
Definition read_avail_idx (mm : gmap Arch.pa (bv 8)) (av : Arch.pa) : option (bv 16) :=
  rd16 mm (pa_off av vq_idx_off).
Definition read_avail_ring (mm : gmap Arch.pa (bv 8)) (av : Arch.pa)
    (qnum : Z) (i : bv 16) : option (bv 16) :=
  if qnum <=? 0 then None
  else rd16 mm (pa_off av (vq_avail_ring_off + 2 * (bv_unsigned i mod qnum))).

(* the decoded request: what the chain says to do, and where to report it *)
Record vio_req := VioReq {
  vr_head   : bv 16;    (* head descriptor index -- goes in the used ring *)
  vr_type   : bv 32;    (* VIRTIO_BLK_T_IN / _OUT *)
  vr_sector : bv 64;
  vr_buf    : Arch.pa;  (* data buffer *)
  vr_len    : bv 32;    (* data length *)
  vr_status : Arch.pa;  (* the one-byte status the device must write *)
}.

Definition read_req (mm : gmap Arch.pa (bv 8)) (c : virtio_cfg) (i : bv 16)
  : option vio_req :=
  let qnum := bv_unsigned (vc_qnum c) in
  match read_avail_ring mm (vc_avail c) qnum i with
  | None => None
  | Some h =>
    if negb (bv_unsigned h <? qnum) then None else
    match read_desc mm (vc_desc c) (bv_unsigned h) with
    | None => None
    | Some d0 =>
      if negb (vd_has d0 vring_desc_f_next) then None else
      if vd_has d0 vring_desc_f_write then None else
      if negb (bv_unsigned (vd_next d0) <? qnum) then None else
      match read_desc mm (vc_desc c) (bv_unsigned (vd_next d0)) with
      | None => None
      | Some d1 =>
        if negb (vd_has d1 vring_desc_f_next) then None else
        if negb (bv_unsigned (vd_next d1) <? qnum) then None else
        match read_desc mm (vc_desc c) (bv_unsigned (vd_next d1)) with
        | None => None
        | Some d2 =>
          if negb (vd_has d2 vring_desc_f_write) then None else
          if negb (bv_unsigned (vd_len d2) =? 1) then None else
          (* the header: type:4 reserved:4 sector:8 *)
          match rd32 mm (vd_addr d0), rd64 mm (pa_off (vd_addr d0) 8) with
          | Some ty, Some sec =>
            (* the data descriptor's direction must match the request type *)
            let wr := vd_has d1 vring_desc_f_write in
            if (bv_unsigned ty =? virtio_blk_t_in) && wr then
              Some (VioReq h ty sec (vd_addr d1) (vd_len d1) (vd_addr d2))
            else if (bv_unsigned ty =? virtio_blk_t_out) && negb wr then
              Some (VioReq h ty sec (vd_addr d1) (vd_len d1) (vd_addr d2))
            else None
          | _, _ => None
          end
        end
      end
    end
  end.

(* ---------------------------------------------------------------------- *)
(* 5. The autonomous request step: the device's own execution context.     *)
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

(* Completing ONE parsed request: the data transfer in whichever direction the
   request asked for, the success status byte, and the used-ring report.  The
   dynamic half of the device state advances; the configuration does not. *)
Definition virtio_complete (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (r : vio_req) : option (virtio_state * gmap Arch.pa (bv 8)) :=
  let n := Z.to_nat (bv_unsigned (vr_len r)) in
  let doff := bv_unsigned (vr_sector r) * virtio_sector_size in
  (* status byte 0 = success; this device never fails a transfer *)
  let ws := <[ vr_status r := byte_zero ]>
              (virtio_used_writes (v_cfg v) (v_used_idx v) r) in
  let vd := fun dk => VirtioState (v_cfg v)
                        (bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer))
                        (bv_add (v_seen v) (Z_to_bv 16 1))
                        (bv_add (v_used_idx v) (Z_to_bv 16 1)) dk in
  if bv_unsigned (vr_type r) =? virtio_blk_t_in then
    (* read the disk: the device WRITES the driver's buffer *)
    Some (vd (v_disk v),
          write_byte_list ws (vr_buf r) (disk_read (v_disk v) doff n))
  else
    (* write the disk: the device READS the driver's buffer *)
    match read_byte_list mm (vr_buf r) n with
    | None => None
    | Some bs => Some (vd (disk_write (v_disk v) doff bs), ws)
    end.

Definition virtio_req_step (v : virtio_state) (mm : gmap Arch.pa (bv 8))
  : option (virtio_state * gmap Arch.pa (bv 8)) :=
  if negb (virtio_live (v_cfg v)) then None else
  match read_avail_idx mm (vc_avail (v_cfg v)) with
  | None => None
  | Some ai =>
    (* nothing published since the last entry the device took *)
    if bv_unsigned ai =? bv_unsigned (v_seen v) then None else
    match read_req mm (v_cfg v) (v_seen v) with
    | None => None
    | Some r => virtio_complete v mm r
    end
  end.

(* Peel [virtio_req_step] down to its completion, once: every fact below is a
   fact about [virtio_complete]. *)
Lemma virtio_req_step_complete (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mm = Some (v', w) ->
  exists r, read_req mm (v_cfg v) (v_seen v) = Some r /\
            virtio_complete v mm r = Some (v', w).
Proof.
  unfold virtio_req_step.
  destruct (negb (virtio_live (v_cfg v))); [discriminate|].
  destruct (read_avail_idx mm (vc_avail (v_cfg v))) as [ai|]; [|discriminate].
  destruct (bv_unsigned ai =? bv_unsigned (v_seen v)); [discriminate|].
  destruct (read_req mm (v_cfg v) (v_seen v)) as [r|] eqn:Hr; [|discriminate].
  intro H. exists r. split; [reflexivity|exact H].
Qed.

(* THE structural fact about an autonomous step, and the reason [virtio_cfg]
   is a separate record: the device never writes its own configuration.
   Everything the DMA footprint of the NEXT request depends on is therefore
   untouched by this one -- see [virtio_dma_ok_step] below. *)
Lemma virtio_complete_cfg (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (r : vio_req) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_complete v mm r = Some (v', w) -> v_cfg v' = v_cfg v.
Proof.
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in).
  - intro H. injection H as H1 H2. by subst v'.
  - destruct (read_byte_list mm (vr_buf r) (Z.to_nat (bv_unsigned (vr_len r))))
      as [bs|]; [|discriminate].
    intro H. injection H as H1 H2. by subst v'.
Qed.

Lemma virtio_req_step_cfg (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mm = Some (v', w) -> v_cfg v' = v_cfg v.
Proof.
  intro H. destruct (virtio_req_step_complete _ _ _ _ H) as (r & _ & Hc).
  exact (virtio_complete_cfg _ _ _ _ _ Hc).
Qed.

(* The used-buffer bit of the interrupt-status register goes UP on completion,
   and only the driver's INTERRUPT_ACK can bring it down again. *)
Lemma virtio_complete_isr (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (r : vio_req) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_complete v mm r = Some (v', w) ->
  v_isr v' = bv_or (v_isr v) (Z_to_bv 32 vio_isr_used_buffer).
Proof.
  unfold virtio_complete. cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in).
  - intro H. injection H as H1 H2. by subst v'.
  - destruct (read_byte_list mm (vr_buf r) (Z.to_nat (bv_unsigned (vr_len r))))
      as [bs|]; [|discriminate].
    intro H. injection H as H1 H2. by subst v'.
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
Lemma virtio_req_step_irq (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mm = Some (v', w) -> virtio_irq v' = true.
Proof.
  intro H. destruct (virtio_req_step_complete _ _ _ _ H) as (r & _ & Hc).
  unfold virtio_irq. rewrite (virtio_complete_isr _ _ _ _ _ Hc).
  by rewrite bv_or_bit0_irq.
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. The DMA-footprint obligation.                                        *)
(*                                                                         *)
(*    A device that writes into the harts' memory can only be given an      *)
(*    Iris rule if the device thread OWNS the bytes it writes.  What it     *)
(*    owns is a LEASE -- a set [D] of addresses whose points-to the device  *)
(*    invariant holds (WpVirtio.v) -- and this predicate is the obligation  *)
(*    that the lease is big enough:                                        *)
(*                                                                         *)
(*      whatever the rest of memory says, a device step from this           *)
(*      CONFIGURATION writes only inside [D], and never over [ctl].         *)
(*                                                                         *)
(*    [ctl] is the CONTROL part of the lease -- the descriptor table and    *)
(*    the available ring, the bytes the device reads to decide WHERE to     *)
(*    write.  Pinning their contents is what makes the footprint a          *)
(*    function of the configuration at all; the second conjunct is what     *)
(*    keeps them pinned, since it says a request never writes over them.    *)
(*                                                                         *)
(*    Note what is NOT quantified: the configuration.  A device step        *)
(*    preserves it ([virtio_req_step_cfg]), so the obligation survives      *)
(*    every autonomous step by construction ([virtio_dma_ok_step]).  Only   *)
(*    the DRIVER, by an MMIO write, can invalidate it -- which is exactly   *)
(*    where the lease should have to be re-established.                     *)
(* ---------------------------------------------------------------------- *)

Definition virtio_dma_ok (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) : Prop :=
  forall (isr : bv 32) (sn ui : bv 16) (dk : Z -> bv 8)
         (mm : gmap Arch.pa (bv 8)) (v' : virtio_state) (w : gmap Arch.pa (bv 8)),
    ctl ⊆ mm ->
    virtio_req_step (VirtioState c isr sn ui dk) mm = Some (v', w) ->
    dom w ⊆ D /\ dom w ## dom ctl.

(* The obligation is preserved by an autonomous step, at the lease the step
   itself leaves behind ([w ∪ ctl] is [ctl] again, since a step never writes
   over the control region).  This is the whole payoff of §1's split. *)
Lemma virtio_dma_ok_step (v : virtio_state) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) (mm : gmap Arch.pa (bv 8))
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_dma_ok (v_cfg v) ctl D ->
  virtio_req_step v mm = Some (v', w) ->
  virtio_dma_ok (v_cfg v') ctl D.
Proof. intros Hok Hstep. by rewrite (virtio_req_step_cfg _ _ _ _ Hstep). Qed.

(* [ctl] stays inside the memory the step produced -- the fact that makes the
   lease re-usable at the next step. *)
Lemma virtio_dma_ctl_union (ctl w mm : gmap Arch.pa (bv 8)) :
  dom w ## dom ctl -> ctl ⊆ mm -> ctl ⊆ w ∪ mm.
Proof.
  intros Hdisj Hsub. apply map_subseteq_spec. intros a b Ha.
  assert (Hw : w !! a = None).
  { apply not_elem_of_dom. intro Hin.
    apply (Hdisj a Hin), elem_of_dom. by exists b. }
  rewrite (lookup_union_r w mm a Hw).
  exact (lookup_weaken _ _ _ _ Ha Hsub).
Qed.

(* Before the driver has made the queue ready the device cannot step at all,
   so the empty lease already satisfies the obligation.  This is what the
   power-on device state (and hence the whole-system adequacy statement)
   needs. *)
Lemma virtio_req_step_not_live (v : virtio_state) (mm : gmap Arch.pa (bv 8)) :
  virtio_live (v_cfg v) = false -> virtio_req_step v mm = None.
Proof.
  intro H. unfold virtio_req_step. by rewrite H.
Qed.

Lemma virtio_dma_ok_not_live (c : virtio_cfg) (ctl : gmap Arch.pa (bv 8))
    (D : gset Arch.pa) :
  virtio_live c = false -> virtio_dma_ok c ctl D.
Proof.
  intros Hlive isr sn ui dk mm v' w _ Hstep.
  rewrite (virtio_req_step_not_live (VirtioState c isr sn ui dk) mm Hlive) in Hstep.
  discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. Power-on state: reset configuration, empty interrupt, blank disk.    *)
(* ---------------------------------------------------------------------- *)

Definition virtio0_state : virtio_state :=
  VirtioState virtio_cfg0 zero32 zero16 zero16 (fun _ => byte_zero).

Lemma virtio0_not_live : virtio_live (v_cfg virtio0_state) = false.
Proof. reflexivity. Qed.

Lemma virtio0_dma_ok ctl D : virtio_dma_ok (v_cfg virtio0_state) ctl D.
Proof. apply virtio_dma_ok_not_live, virtio0_not_live. Qed.

Lemma virtio0_irq : virtio_irq virtio0_state = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 8. The driver's own sequence, run against this model.                   *)
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
  /\ virtio_read v vio_off_vendor_id = Some (Z_to_bv 32 0x554d4551)
  /\ virtio_read v vio_off_queue_num_max = Some (Z_to_bv 32 8).
Proof. repeat split; reflexivity. Qed.

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
Lemma virtio_complete_isr_ok (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (r : vio_req) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_isr_ok v -> virtio_complete v mm r = Some (v', w) -> virtio_isr_ok v'.
Proof.
  intros Hok Hc. unfold virtio_isr_ok.
  rewrite (virtio_complete_isr _ _ _ _ _ Hc), bv_or_unsigned.
  assert (Hone : bv_unsigned (Z_to_bv 32 vio_isr_used_buffer) = 1)
    by (by vm_compute).
  rewrite Hone. apply land3_intro. intros i Hi.
  rewrite Z.lor_spec, (land3_bit_high _ i Hok Hi).
  rewrite (Z.bits_above_log2 1 i); [ reflexivity | lia | ].
  change (Z.log2 1) with 0. lia.
Qed.

Lemma virtio_req_step_isr_ok (v : virtio_state) (mm : gmap Arch.pa (bv 8))
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_isr_ok v -> virtio_req_step v mm = Some (v', w) -> virtio_isr_ok v'.
Proof.
  intros Hok H. destruct (virtio_req_step_complete _ _ _ _ H) as (r & _ & Hc).
  exact (virtio_complete_isr_ok _ _ _ _ _ Hok Hc).
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
