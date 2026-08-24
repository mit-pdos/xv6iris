(* DiskChain.v -- A CHAIN THAT IS NOT EXACTLY THREE DESCRIPTORS.  The device
   STALLS; the hardware serves it normally.

   Source: tools/vtest/tests/disk_chain.S.  Capture: DiskChainGen.v.

   [VirtioModel.chain_at] accepts one shape and one only -- d0 with NEXT, d1
   with NEXT, d2 WITHOUT -- and this test publishes four descriptors: a
   header, TWO data descriptors of 256 bytes each, and a status byte.  That
   is ordinary scatter-gather, what a driver does when its payload is not
   physically contiguous, and QEMU serves it: 512 bytes land on sector 7,
   status OK, one used-ring entry.

   The model cannot.  [chain_at] returns None, so [req_at] is None, so
   [virtio_req_step] and [virtio_capture_step] are both None while
   [virtio_pending] stays true -- which is exactly [virtio_stalled].  The
   guest's poll loop then spins, and the model side runs out of BUDGET
   rather than getting STUCK.  That distinction is the point of recording it
   this way: a stuck machine is a missing transition at a named pc
   (DiskIdent*.v); a stalled device is a machine that keeps stepping
   perfectly happily and never makes progress.

   WHY THIS IS NOT SIMPLY AN UNSOUNDNESS.  A stalled queue ENABLES
   [RiscvLang.DevStepDiskWild] -- when the published chain is malformed the
   device may write ANYTHING ANYWHERE -- so in principle the model DOES have
   an execution matching QEMU here, reached by taking the wild arm with the
   write set read off the capture.  Section 4 says what that would take and
   why this file does not do it. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list gmap bitvector.definitions.
Require Import VTest DiskChainGen.
Local Open Scope Z_scope.

Definition chain_start : mstate := start_dma disk_chain_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model never finishes: BUDGET, not STUCK.                         *)
(*                                                                         *)
(*    549 instructions get the guest to its poll loop (7 of prologue, 101   *)
(*    of body, and 63 extra trips round the payload loop); the budget here  *)
(*    is 1000, so the last 450 instructions are the loop going round and    *)
(*    round.  [VBudget] and not [VStuck] is the whole observation: the      *)
(*    machine has a transition at every step, it just never reaches the     *)
(*    DONE handshake.                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma disk_chain_model_never_completes :
  run_status 1000 chain_start = VBudget.
Proof. solve_vtest VBudget. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ...and WHY: the device is [virtio_stalled] at that point.            *)
(*                                                                         *)
(*    Without this, "the budget ran out" would be indistinguishable from    *)
(*    "the budget was too small", which the README calls a broken test      *)
(*    rather than a finding.  700 instructions is well past the notify, so  *)
(*    the request is published and the device has seen it.                 *)
(* ---------------------------------------------------------------------- *)

Definition chain_after_notify : option mstate := srun [SCpu 700] chain_start.

Definition stalled_of (o : option mstate) : bool :=
  match o with
  | None => false
  | Some s => virtio_stalled (dvirtio (mdev s)) (view_of (mem s))
  end.

Lemma disk_chain_device_stalled : stalled_of chain_after_notify = true.
Proof. solve_vtest true. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. What QEMU did with the same four descriptors.                        *)
(*                                                                         *)
(*    Off the capture, so it costs no model evaluation:                    *)
(*      +4  progress marker            2  = the completion was observed    *)
(*      +8  status byte                0  = OK                            *)
(*      +12 used.ring[0].id            0                                  *)
(*      +16 used.ring[0].len           1  = the status byte alone          *)
(*      +20 used.idx                   1                                  *)
(*      +24 InterruptStatus            1                                  *)
(*    ...and sector 7 of the disk holds the whole 512-byte payload,        *)
(*    reassembled from the two 256-byte descriptors.                       *)
(* ---------------------------------------------------------------------- *)

Definition chain_qemu : list Z :=
  (fun o => cap_word disk_chain_qemu_result o) <$> [4; 8; 12; 16; 20; 24]%nat.

Definition chain_qemu_expect : list Z := [2; 0; 0; 1; 1; 1].

Lemma disk_chain_qemu_serves_it : chain_qemu = chain_qemu_expect.
Proof. solve_vtest chain_qemu_expect. Qed.

Lemma disk_chain_qemu_wrote_a_sector : (fst <$> disk_chain_qemu_disk) = [7].
Proof. solve_vtest [7]. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The finding, off the model rather than off this test.                *)
(* ---------------------------------------------------------------------- *)

(* EXACTLY THREE, and the third must END the chain: if the descriptor that
   would be the status descriptor carries NEXT -- i.e. the chain is longer
   than three -- [chain_at] has no parse at all.  That is the whole reason a
   four-descriptor chain stalls this device. *)
Lemma model_refuses_longer_chains (c : virtio_cfg) (mv : vmem) (i : bv 16) :
  vd_has (desc_at c mv (bv_unsigned (vd_next
            (desc_at c mv (bv_unsigned (vd_next
              (desc_at c mv (bv_unsigned (avail_ring_at c mv i)))))))))
         vring_desc_f_next = true ->
  chain_at c mv i = None.
Proof.
  intro H3. unfold chain_at. cbv zeta.
  set (h := avail_ring_at c mv i) in *.
  set (e0 := desc_at c mv (bv_unsigned h)) in *.
  set (e1 := desc_at c mv (bv_unsigned (vd_next e0))) in *.
  set (e2 := desc_at c mv (bv_unsigned (vd_next e1))) in *.
  destruct (negb (bv_unsigned h <? bv_unsigned (vc_qnum c))); [reflexivity|].
  destruct (negb (vd_has e0 vring_desc_f_next)); [reflexivity|].
  destruct (negb (bv_unsigned (vd_next e0) <? bv_unsigned (vc_qnum c)));
    [reflexivity|].
  destruct (negb (vd_has e1 vring_desc_f_next)); [reflexivity|].
  destruct (negb (bv_unsigned (vd_next e1) <? bv_unsigned (vc_qnum c)));
    [reflexivity|].
  by rewrite H3.
Qed.

(* ...and once the device is stalled, NEITHER ordinary arm is enabled: the
   completion and the capture are both None while the request stays
   published.  So there is no schedule of ordinary steps -- no [sitem] list
   built from [SDiskDma], [SDiskCapture] and [SDiskDrain] -- that gets the
   used ring moving.  Only [SDiskWild] is left. *)
Lemma model_stalled_leaves_only_wild (v : virtio_state) (mv : vmem) :
  virtio_stalled v mv = true ->
  virtio_pending v mv = true
  /\ virtio_req_step v mv = None
  /\ virtio_capture_step v mv = None.
Proof.
  intro H. destruct (virtio_stalled_step v mv H) as [Hp Hr].
  split_and!; [exact Hp | exact Hr | exact (virtio_stalled_capture_step v mv H)].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. Classified, and what would close it.                                 *)
(*                                                                         *)
(* INCOMPLETENESS IN PRACTICE, not unsoundness in principle -- and the      *)
(* distinction is exactly the wild arm.                                    *)
(*                                                                         *)
(* Not unsoundness: [DevStepDiskWild] is enabled precisely when             *)
(* [virtio_stalled] holds, and it lets the device write anything anywhere.  *)
(* So the 512 bytes QEMU put on sector 7, the status byte, the used-ring    *)
(* entry and the interrupt are all inside the model's transition relation;  *)
(* a theorem proved against the model still covers this machine.  That is   *)
(* the "model UB as ANYTHING, never as NOTHING" design paying off, and it   *)
(* is why this file does not sit next to DiskOrder.v's finding 5.           *)
(*                                                                         *)
(* But in practice: the wild arm is useless to a driver proof.  A driver    *)
(* that publishes a four-descriptor chain gets a device that may scribble   *)
(* over its whole address space, so nothing can be proved about it -- which *)
(* is the same coverage loss as a stuck machine, arrived at from the other  *)
(* direction.  Scatter-gather is not exotic: it is what any driver whose    *)
(* payload spans two pages must do.                                        *)
(*                                                                         *)
(* WHAT THIS FILE DOES NOT DO, deliberately.  There IS a model execution    *)
(* matching QEMU here -- [srun] with an [SDiskWild w] whose write list [w]  *)
(* is read off the capture -- and exhibiting it would be the suite's first  *)
(* demonstration that the wild arm actually earns its keep.  It is not here *)
(* because [VSched.settle] never picks [SDiskWild] (the eager scheduler     *)
(* stops at the first enabled ordinary arm and the wild arm is not one of   *)
(* the six it tries), so the witness would have to be a hand-written        *)
(* [sitem] list that interleaves several hundred [SCpu] steps around one    *)
(* [SDiskWild] carrying ~530 (address, byte) pairs -- the payload, the      *)
(* status byte, the used-ring element and the used index.  Building the     *)
(* write list mechanically from the capture is HARNESS work, not test work. *)
(* Until that lands, sections 1 and 2 record what is observable: the eager  *)
(* schedule does not complete, and the device is stalled when it stops.     *)
(*                                                                         *)
(* THE CHEAP FIX, if the model is to serve these chains rather than declare *)
(* them undefined, is to let [chain_at] walk the NEXT list instead of       *)
(* unrolling it three times: collect descriptors until one without NEXT,    *)
(* take the last as the status descriptor and the middle ones as the data,  *)
(* with a bound (the queue size) to keep the walk terminating and a check   *)
(* that the data descriptors are contiguous or a [vio_req] that carries a   *)
(* LIST of buffers rather than one.  That second half is the real cost: it  *)
(* changes [vio_req], hence [vreq_wr], hence the crash-permit indexing in   *)
(* [vreq_cache].  It is a bigger change than finding 4's and a smaller one  *)
(* than finding 5's.                                                       *)
(* ---------------------------------------------------------------------- *)
