(* DiskErr.v -- THE ERROR PATHS OF THE REQUEST PROTOCOL, and they AGREE.

   Source: tools/vtest/tests/disk_err.S.  Capture: DiskErrGen.v.

   [VirtioModel.virtio_complete] is TOTAL -- there is no request the device
   refuses to answer -- and two of its branches had never been run by
   anything in this tree:

     - an UNRECOGNISED request type, which must complete with status
       VIRTIO_BLK_S_UNSUPP (2) and move no data at all;
     - VIRTIO_BLK_T_FLUSH (4), which the model RECOGNISES (status OK, no
       data) rather than reporting UNSUPP, and gates on the write cache
       being empty -- that gate is what makes a flush a barrier.

   THE FLUSH IS THE INTERESTING ONE.  The driver in this test declines
   VIRTIO_BLK_F_FLUSH during negotiation, exactly as xv6's does, so the
   question the test actually asks is whether QEMU still serves a type-4
   request from a driver that never negotiated the feature.  IT DOES: status
   0, a normal used-ring entry.  So the model's decision to recognise type 4
   unconditionally -- rather than making it depend on the negotiated feature
   word -- matches the hardware.  That is not obvious and it is now tested.

   The three requests are a WRITE of sector 5, then the unknown type NAMING
   SECTOR 5 with a 512-byte device-writable buffer INSIDE THE RESULT REGION
   prefilled with 0xaa, then the FLUSH.  So "no data transfer" is a
   CHANNEL and not an inference: a stray DMA in either direction would show
   up either in the 0xaa prefill or in the disk capture. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list gmap bitvector.definitions.
Require Import VTest DiskErrGen.
Local Open Scope Z_scope.

Definition err_run : option mstate := run_until 50000 (start_dma disk_err_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_err.S *)
Definition err_agree_offs : list nat :=
  [4;   (* progress marker: 3 = all three requests completed *)
   8;   (* the WRITE's status byte              0 = OK *)
   12;  (* used.ring[0].id                      0 *)
   16;  (* THE UNKNOWN TYPE's status byte       2 = UNSUPP *)
   20;  (* used.ring[1].id                      3 *)
   28;  (* THE FLUSH's status byte              0 = OK *)
   32;  (* used.ring[2].id                      0 *)
   40;  (* used.idx after all three             3 *)
   44;  (* InterruptStatus                      1 *)
   48]%nat. (* the 0xaa marker, UNTOUCHED *)

Definition err_len_offs : list nat := [24; 36]%nat.  (* the two used.len *)

(* ---------------------------------------------------------------------- *)
(* 1. Everything the error paths turn on agrees, on all three channels.    *)
(*                                                                         *)
(*    The words above, the 16 bytes of the 0xaa prefill the unsupported     *)
(*    request's data descriptor pointed AT (result+0x200 = offset 512), and *)
(*    the disk -- which holds sector 5 as the WRITE left it and not as the  *)
(*    unknown-type request naming the same sector might have.               *)
(*                                                                         *)
(*    ONE lemma, one evaluation; the RHS is a [Definition] over the capture *)
(*    so naming it in [solve_vtest] does not cost a second run.             *)
(* ---------------------------------------------------------------------- *)

Definition err_expect :=
  ((fun o => cap_word disk_err_qemu_result o) <$> err_agree_offs,
   cap_bytes disk_err_qemu_result 512 16,
   disk_err_qemu_disk).

Lemma disk_err_agrees :
  ((fun o => res_word err_run o) <$> err_agree_offs,
   res_bytes err_run 512 16,
   disk_like err_run disk_err_qemu_disk) = err_expect.
Proof. solve_vtest err_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE USED ELEMENT'S [len] on two paths that write no data at all --   *)
(*    which is where finding 4's fix had to be got right rather than       *)
(*    merely made.                                                         *)
(*                                                                         *)
(*    Both requests here ride a READ-SHAPED chain: the data descriptor is   *)
(*    marked WRITABLE by the driver, and the 0xaa prefill above proves the  *)
(*    device never filled it (an unrecognised type transfers nothing, and   *)
(*    neither does a flush).  So the two candidate rules disagree exactly   *)
(*    here.  The spec's wording -- "the number of bytes WRITTEN into the    *)
(*    device-writable part of the chain" -- says 1, the status byte alone.  *)
(*    The hardware says 513, and every real device does: what is reported   *)
(*    is the writable SEGMENT, not the transfer.                            *)
(*                                                                         *)
(*    The model follows the hardware, and the reason is the suite's own     *)
(*    question.  A model that answered 1 here would produce a value the     *)
(*    machine does not, and would have no execution matching what the       *)
(*    machine did -- which is the shape of finding 4 itself, merely moved   *)
(*    from the read path to the error paths.  So [vreq_used_len] keys off   *)
(*    the descriptor's WRITE flag, not the request type, and these two      *)
(*    fields are what force that distinction: keying off the type would     *)
(*    pass DiskRw.v and fail here.                                         *)
(* ---------------------------------------------------------------------- *)

Definition err_lens : list Z := [513; 513].

Lemma disk_err_model_lens :
  (fun o => res_word err_run o) <$> err_len_offs = err_lens.
Proof. solve_vtest err_lens. Qed.

Lemma disk_err_qemu_lens :
  (fun o => cap_word disk_err_qemu_result o) <$> err_len_offs = err_lens.
Proof. solve_vtest err_lens. Qed.



(* ---------------------------------------------------------------------- *)
(* 3. The two branches, off the model rather than off this test.           *)
(*                                                                         *)
(*    The test exhibits ONE execution; these say what the model does in     *)
(*    general, which is what makes the agreement above mean something.      *)
(* ---------------------------------------------------------------------- *)

(* an unrecognised type is answered, and answered with UNSUPP *)
Lemma model_unknown_type_is_unsupp (v : virtio_state) (mv : vmem) (r : vio_req) :
  bv_unsigned (vr_type r) <> virtio_blk_t_in ->
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  (virtio_complete v mv r).2 !! vr_status r
  = Some (Z_to_bv 8 virtio_blk_s_unsupp).
Proof.
  intros Hi Ho Hf. unfold virtio_complete. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.eqb_neq _ _) Ho),
          (proj2 (Z.eqb_neq _ _) Hf).
  cbn [orb snd]. by rewrite lookup_insert.
Qed.

(* ...and it is never GATED: unlike a write it does not wait for anything,
   which is why the eager schedule serves it in one step *)
Lemma model_unknown_type_not_gated (v : virtio_state) (r : vio_req) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  virtio_complete_ok v r = true.
Proof. exact (virtio_complete_ok_in v r). Qed.

(* THE FLUSH IS A BARRIER, and this is the whole of what that means in the
   model: the completion is enabled only once the volatile write cache has
   drained to the durable image.  In this test the driver is writethrough,
   so the cache was already empty and the flush completed at once -- the
   test therefore confirms the OK status but not the barrier.  The barrier
   is the statement below. *)
Lemma model_flush_needs_empty_cache (v : virtio_state) (r : vio_req) :
  bv_unsigned (vr_type r) = virtio_blk_t_flush ->
  virtio_complete_ok v r = true -> v_cache v = ∅.
Proof.
  intros Hf Hok. apply (virtio_complete_ok_flush v r); [| exact Hf | exact Hok].
  rewrite Hf. unfold virtio_blk_t_flush, virtio_blk_t_out. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. What this file CONFIRMS.                                             *)
(*                                                                         *)
(*  - An unrecognised request type completes with UNSUPP = 2 on both        *)
(*    machines, and consumes a used-ring slot like any other request        *)
(*    (id 3, used.idx advanced): it is an ANSWER, not a silence.  A device  *)
(*    that dropped the request would leave the driver blocked forever, and  *)
(*    that is a behaviour neither machine has.                              *)
(*                                                                         *)
(*  - It transfers NOTHING.  Its data descriptor was device-writable and    *)
(*    pointed into the result region; the 0xaa prefill is intact on both    *)
(*    sides.  And it named the sector the preceding WRITE had just filled,  *)
(*    so the disk capture would have moved had either machine treated an    *)
(*    unknown type as a write.  It did not.                                 *)
(*                                                                         *)
(*  - VIRTIO_BLK_T_FLUSH completes OK on both machines FROM A DRIVER THAT   *)
(*    DECLINED VIRTIO_BLK_F_FLUSH.  This was the open question; the model's *)
(*    unconditional recognition of type 4 is faithful.  (What the feature   *)
(*    bit does control in the model is the CACHE MODE -- [virtio_wce] reads *)
(*    it off the recorded driver-features word -- and not whether a flush   *)
(*    is understood.  QEMU is the same shape.)                              *)
(*                                                                         *)
(*  - The interrupt status is 1 after three completions, not 3 or 2: the    *)
(*    used-buffer bit is a bit and not a count, on both machines.           *)
(* ---------------------------------------------------------------------- *)
