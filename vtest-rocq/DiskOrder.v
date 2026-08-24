(* DiskOrder.v -- TWO requests in one batch, and the order they complete in.
   THIS FILE RECORDS THE SUITE'S FIRST UNSOUNDNESS.

   Source: tools/vtest/tests/disk_order.S.  Capture: DiskOrderGen.v.
   215 instructions on the model side.

   The test publishes two write requests at once, deliberately lopsided --
   request A is eight sectors at 100, request B is one sector at 5 -- with a
   single notify, and records which descriptor id landed in which used-ring
   slot.

   QEMU HAS TWO EXECUTIONS HERE.  Over 40 runs the capture contains both
   [0;3] (A completed first) and [3;0] (B OVERTOOK A).  The proportion
   depends on the backend: with the default cache=writeback the reorder
   showed up 6 times in 25, and with cache=none,aio=native it was 25 out of
   25.  Nothing about it is exotic -- it is what a device with more than one
   request in flight does.

   THE MODEL HAS ONLY ONE, and cannot be scheduled into the other.  That is
   [model_serves_head_only] in section 3: it is not a statement about this
   test's schedule but about [virtio_req_step] itself. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list gmap bitvector.definitions.
Require Import VTest DiskOrderGen.
Local Open Scope Z_scope.

Definition ord_run : option mstate := run_until 30000 (start_dma disk_order_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_order.S *)
Definition ord_agree_offs : list nat :=
  [4;   (* progress marker: 2 = both requests completed *)
   8;   (* used.ring[0].id -- WHICH REQUEST FINISHED FIRST *)
   16;  (* used.ring[1].id *)
   24; 28;  (* the two status bytes *)
   32; 36]%nat. (* used.idx, InterruptStatus *)

Definition ord_len_offs : list nat := [12; 20]%nat.  (* the two used.len *)

(* ---------------------------------------------------------------------- *)
(* 1. The model reproduces ONE of QEMU's two executions: the in-order one.  *)
(*    Both ids, both status bytes, the used index, the interrupt status,    *)
(*    and all nine sectors of the disk.                                     *)
(* ---------------------------------------------------------------------- *)

Definition ord_expect :=
  ((fun o => cap_word disk_order_qemu_result o) <$> ord_agree_offs,
   disk_order_qemu_disk).

Lemma disk_order_admits_inorder :
  ((fun o => res_word ord_run o) <$> ord_agree_offs,
   disk_like ord_run disk_order_qemu_disk) = ord_expect.
Proof. solve_vtest ord_expect. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and QEMU has a SECOND one, which differs in exactly the two ids.   *)
(*    Cheap: these read the capture, not the model.                        *)
(* ---------------------------------------------------------------------- *)

Definition ord_ids (c : list Z) : list Z := [cap_word c 8; cap_word c 16].
Definition ord_qemu_orders : list (list Z) := [[0; 3]; [3; 0]].

Lemma disk_order_qemu_has_both :
  ord_ids <$> disk_order_qemu_results = ord_qemu_orders.
Proof. solve_vtest ord_qemu_orders. Qed.

Lemma disk_order_orders_differ : [0; 3] <> [3; 0].
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE FINDING: the model cannot produce the second one, under ANY       *)
(*    schedule.  Not a fact about this test -- a fact about the device.     *)
(*                                                                         *)
(*    [virtio_req_step] reads the chain at position [v_seen] and hands back *)
(*    a state whose [v_seen] is one greater.  So the sequence of positions  *)
(*    the device serves is 0,1,2,... with no freedom at all, the used-ring  *)
(*    entry for position i is written before the one for position i+1, and  *)
(*    the used ring can only ever come out in PUBLICATION ORDER.  No choice *)
(*    of [sitem] list changes that: the arms a schedule may pick between    *)
(*    (capture, drain, complete) do not include "serve a different one".    *)
(* ---------------------------------------------------------------------- *)

Lemma model_serves_head_only (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) ->
  (exists r, req_at (v_cfg v) mv (v_seen v) = Some r)
  /\ v_seen v' = bv_add (v_seen v) (Z_to_bv 16 1).
Proof.
  intro H. split.
  - destruct (virtio_req_step_shape _ _ _ _ H) as (r & Hr & _). by exists r.
  - exact (virtio_req_step_seen _ _ _ _ H).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. What this costs the development.                                     *)
(*                                                                         *)
(*    UNSOUNDNESS, not incompleteness.  The other divergences the suite has *)
(*    found so far are the model being STRICTER than the hardware, which    *)
(*    limits which drivers can be verified but cannot make a proof wrong.   *)
(*    This one is the other direction: the hardware has a behaviour the     *)
(*    model has no transition for, so a theorem proved against the model    *)
(*    does not cover the machine it claims to.                              *)
(*                                                                         *)
(*    And it is live in xv6, not hypothetical.  [virtio_disk_rw] sleeps     *)
(*    with its request outstanding, so up to NUM = 8 can be in flight at    *)
(*    once; and [virtio_disk_intr] walks the used ring reading each         *)
(*    element's ID and waking [disk.info[id]] -- it is written that way     *)
(*    precisely because completions need not come back in order.  Under     *)
(*    this model that code is only ever exercised on the in-order case, so  *)
(*    the reason it reads the id at all is never tested by the proof.       *)
(*                                                                         *)
(*    The fix is not local, which is why this file only records it.  The    *)
(*    device would need to serve any PUBLISHED-but-unserved position rather *)
(*    than [v_seen] alone -- so [v_seen : bv 16] becomes a set of           *)
(*    outstanding positions, [virtio_pending] and the completion gate move  *)
(*    with it, and [VirtioQueue]'s slot protocol and the DMA lease's        *)
(*    reachable-window argument ([virtio_queue_ok]'s [S], closed under      *)
(*    advancing by one until it reaches [ai]) are stated against exactly    *)
(*    the assumption this breaks.  See                                      *)
(*    claude-notes/completed/virtio-disk.md and design/virtio-driver.md.    *)
(* ---------------------------------------------------------------------- *)

Definition ord_model_lens : list Z := [4096; 512].
Definition ord_qemu_lens  : list Z := [1; 1].

(* the used.len defect of DiskRw section 3 again, on a multi-sector request:
   the model reports the data descriptor's length, QEMU the one status byte *)
Lemma disk_order_model_lens :
  (fun o => res_word ord_run o) <$> ord_len_offs = ord_model_lens.
Proof. solve_vtest ord_model_lens. Qed.

Lemma disk_order_qemu_lens :
  (fun o => cap_word disk_order_qemu_result o) <$> ord_len_offs = ord_qemu_lens.
Proof. solve_vtest ord_qemu_lens. Qed.
