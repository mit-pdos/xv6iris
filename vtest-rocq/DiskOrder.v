(* DiskOrder.v -- TWO requests in one batch, and the order they complete in.
   BOTH OF QEMU's EXECUTIONS ARE THE MODEL'S; this file used to record the
   suite's only unsoundness (finding 5).

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

   THE MODEL USED TO HAVE ONLY ONE.  [virtio_req_step] read the chain at
   [v_seen] and handed back a state whose [v_seen] was one greater, so the
   sequence of positions the device served was 0,1,2,... with no freedom at
   all and the used ring could only ever come out in PUBLICATION ORDER.  No
   choice of [sitem] list changed that: the arms a schedule could pick
   between (capture, drain, complete) did not include "serve a different
   one".  That was UNSOUNDNESS -- a hardware behaviour with no model
   execution -- and the reason it mattered is that xv6 depends on the
   freedom: [virtio_disk_intr] walks the used ring reading each element's ID
   and waking [disk.info[id]], written that way precisely because
   completions need not come back in order.

   THE FIX (claude-notes/design/virtio-driver.md) is QEMU's own two-phase
   lifecycle.  The device POPS available-ring entries strictly in order
   ([virtio_pop_step]: [v_seen] is the pop index, and what a pop takes is
   the DESCRIPTOR HEAD the entry names), and it COMPLETES the heads it holds
   in any order: [v_inflight] is the set of heads popped and not yet
   completed, and every step that answers a request -- capture, completion
   -- takes the HEAD as a parameter, enabled exactly when that head is in
   flight.  The used ring reports the head back, which is why the ids the
   test records ARE the heads: 0 for A, 3 for B.  Both executions below run
   the SAME program on the same machine and pop both requests before
   completing either; they differ only in which in-flight head the device
   completes first ([VTest.run_until] takes the lowest, [VTest.run_until_rev]
   the highest). *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list gmap bitvector.definitions.
Require Import VTest DiskOrderGen.
Local Open Scope Z_scope.

Definition ord_run : option mstate := run_until 30000 (start_dma disk_order_text).

(* the same program, served by a device that finishes the SECOND request
   first -- the execution the model used to be missing *)
Definition ord_run_rev : option mstate :=
  run_until_rev 30000 (start_dma disk_order_text).

(* result-region offsets, mirroring tools/vtest/tests/disk_order.S *)
Definition ord_agree_offs : list nat :=
  [4;   (* progress marker: 2 = both requests completed *)
   8;   (* used.ring[0].id -- WHICH REQUEST FINISHED FIRST *)
   16;  (* used.ring[1].id *)
   24; 28;  (* the two status bytes *)
   32; 36]%nat. (* used.idx, InterruptStatus *)

Definition ord_len_offs : list nat := [12; 20]%nat.  (* the two used.len *)

(* ---------------------------------------------------------------------- *)
(* 1. The model reproduces QEMU's IN-ORDER execution, whole.  Both ids,     *)
(*    both status bytes, the used index, the interrupt status, and all      *)
(*    nine sectors of the disk.                                            *)
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
(* 3. AND THE MODEL PRODUCES IT TOO.  Same program, same start state, a     *)
(*    device that picks up the SECOND outstanding request first: B's id     *)
(*    lands in used.ring[0] and A's in used.ring[1], which is QEMU's other  *)
(*    capture.  Everything else -- both status bytes, the used index, the    *)
(*    interrupt status and all nine sectors of the disk -- is unchanged,     *)
(*    which is the point: the two executions differ in the ORDER and in     *)
(*    nothing else.                                                        *)
(* ---------------------------------------------------------------------- *)

Definition ord_ids_of (r : option mstate) : list Z :=
  [res_word r 8; res_word r 16].

Lemma disk_order_admits_reordered :
  (ord_ids_of ord_run_rev,
   (fun o => res_word ord_run_rev o) <$> [24; 28; 32; 36]%nat,
   disk_like ord_run_rev disk_order_qemu_disk)
  = ([3; 0],
     (fun o => cap_word disk_order_qemu_result o) <$> [24; 28; 32; 36]%nat,
     disk_order_qemu_disk).
Proof.
  solve_vtest ([3; 0],
               (fun o => cap_word disk_order_qemu_result o) <$> [24; 28; 32; 36]%nat,
               disk_order_qemu_disk).
Qed.

(* ...and the two model runs really are the two QEMU captures, not one run
   read twice: the ids differ, and between them they are exactly the set of
   orders the hardware produced. *)
Lemma disk_order_model_has_both :
  [ord_ids_of ord_run; ord_ids_of ord_run_rev] = ord_qemu_orders.
Proof. solve_vtest ord_qemu_orders. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. Stated off the MODEL rather than off this program: the completion     *)
(*    order is FREE and the pop order is NOT.  A completion answers the     *)
(*    head it is given, and the only condition on that head is that the     *)
(*    device has popped it and not yet completed it -- there is nothing in  *)
(*    the model that prefers one in-flight head to another.  This is the    *)
(*    property whose absence was the finding.  The pop, by contrast, takes  *)
(*    the entry at [v_seen] and nothing else, and moves [v_seen] by one:    *)
(*    that is the half QEMU does in order, and the half xv6's ring-slot     *)
(*    reuse depends on.                                                    *)
(* ---------------------------------------------------------------------- *)

Lemma model_completes_any_inflight_head (v : virtio_state) (mv : vmem)
    (i : bv 16) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv i = Some (v', w) ->
  (* it answered the head it was handed... *)
  (exists r, req_from (v_cfg v) mv i = Some r)
  (* ...which was in flight, and nothing more was asked of it *)
  /\ i ∈ v_inflight v
  (* ...and afterwards exactly that head is gone from the in-flight set,
     while the pop index has not moved *)
  /\ v_inflight v' = v_inflight v ∖ {[ i ]}
  /\ v_seen v' = v_seen v.
Proof.
  intro H.
  destruct (virtio_req_step_shape _ _ _ _ _ H) as (r & Hr & Hserve & _ & _).
  split; [by exists r|].
  split; [exact (virtio_serve_in _ _ _ Hserve)|].
  split; [exact (virtio_req_step_inflight _ _ _ _ _ H)|].
  exact (virtio_req_step_seen _ _ _ _ _ H).
Qed.

Lemma model_pops_in_order (v : virtio_state) (mv : vmem) (v' : virtio_state) :
  virtio_pop_step v mv = Some v' ->
  (* the entry taken is the one at the pop index, and only that one... *)
  v_inflight v' = {[ avail_ring_at (v_cfg v) mv (v_seen v) ]} ∪ v_inflight v
  (* ...and the index advances by exactly one *)
  /\ v_seen v' = bv_add (v_seen v) one16.
Proof.
  intro H. destruct (virtio_pop_step_shape _ _ _ H) as [_ ->].
  split; reflexivity.
Qed.

Definition ord_lens : list Z := [1; 1].

(* THE USED ELEMENT'S [len], which used to be finding 4 here too: both these
   requests are WRITES, so the device-writable part of each chain is the
   status byte alone and both report 1 -- on a multi-sector request as much
   as on a single-sector one, since what is counted is the writable segment
   and not the transfer.  The model used to report the data descriptor's
   length, 4096 and 512. *)
Lemma disk_order_model_lens :
  (fun o => res_word ord_run o) <$> ord_len_offs = ord_lens.
Proof. solve_vtest ord_lens. Qed.

Lemma disk_order_qemu_lens :
  (fun o => cap_word disk_order_qemu_result o) <$> ord_len_offs = ord_lens.
Proof. solve_vtest ord_lens. Qed.
