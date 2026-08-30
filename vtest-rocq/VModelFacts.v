(* ====================================================================== *)
(* VModelFacts.v -- what is TRUE OF THE MODEL, independently of any run.   *)
(*                                                                        *)
(* The run framework (VRun.v) can say only one kind of thing: that the     *)
(* model exhibits what some platform observed.  These are the other kind   *)
(* -- universally quantified statements about the model's own definitions, *)
(* with no capture and no platform anywhere in them.                       *)
(*                                                                        *)
(* THEY ARE WHY A NULL RESULT IS EVER MEANINGFUL.  "The model has no       *)
(* execution for this" is a claim about the relation, and no comparison    *)
(* against a capture can make it.  These can.  They were the only content  *)
(* of the retired per-test files that a Pass module does not subsume,      *)
(* which is why they are here rather than deleted with the rest.           *)
(* ====================================================================== *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list option gmap bitvector.definitions.
Import ListNotations.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec VirtioModel DevModel.
Require Import VTest VConc.
Local Open Scope Z_scope.

(* ---- from the retired DiskChain.v ---- *)

(* EXACTLY THREE, and the third must END the chain: if the descriptor that
   would be the status descriptor carries NEXT -- i.e. the chain is longer
   than three -- [chain_from] has no parse at all, at the HEAD the device
   popped.  That is the whole reason a four-descriptor chain stalls this
   device. *)
Lemma model_refuses_longer_chains (c : virtio_cfg) (mv : vmem) (h : bv 16) :
  vd_has (desc_at c mv (bv_unsigned (vd_next
            (desc_at c mv (bv_unsigned (vd_next
              (desc_at c mv (bv_unsigned h))))))))
         vring_desc_f_next = true ->
  chain_from c mv h = None.
Proof.
  intro H3. unfold chain_from. cbv zeta.
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
   completion and the capture are both None at the head it stalled on,
   while that head stays in flight.  So there is no schedule of ordinary
   steps -- no [sitem] list built from [SDiskPop], [SDiskDma],
   [SDiskCapture] and [SDiskDrain] -- that gets the used ring moving.  Only
   [SDiskWild] is left. *)
Lemma model_stalled_leaves_only_wild (v : virtio_state) (mv : vmem) :
  virtio_stalled v mv = true ->
  virtio_pending v mv = true
  /\ exists i, virtio_req_step v mv i = None
               /\ virtio_capture_step v mv i = None.
Proof.
  intro H. split; [ exact (virtio_stalled_pending v mv H) | ].
  destruct (virtio_stalled_pos v mv H) as (i & _ & Hbad).
  exists i. exact (virtio_chain_bad_no_step v mv i Hbad).
Qed.

(* ---- from the retired DiskOrder.v ---- *)

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

(* ---- from the retired DiskErr.v ---- *)

(* an unrecognised type is answered, and answered with UNSUPP *)
Lemma model_unknown_type_is_unsupp (v : virtio_state) (mv : vmem) (r : vio_req)
    (i : bv 16) :
  bv_unsigned (vr_type r) <> virtio_blk_t_in ->
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  (virtio_complete v mv r i).2 !! vr_status r
  = Some (Z_to_bv 8 virtio_blk_s_unsupp).
Proof.
  intros Hi Ho Hf. unfold virtio_complete. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.eqb_neq _ _) Ho),
          (proj2 (Z.eqb_neq _ _) Hf).
  cbn [orb snd]. by rewrite lookup_insert.
Qed.

(* ...and it does not wait for the CACHE TO DRAIN the way a write does, only
   for its own sectors to be off the cache -- which in this test, and in every
   execution where nothing overlapping is in flight, is immediate.  (With the
   served order free the device may be holding SOME OTHER request's captured
   payload when this one completes, and a request is served from
   [VirtioModel.cache_view]; the gate is what makes the bytes it reports the
   durable ones.  See VirtioModel's [virtio_complete_ok].) *)
Lemma model_unknown_type_not_gated (v : virtio_state) (r : vio_req)
    (i : bv 16) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  vreq_touch r ∩ dom (v_cache v) = ∅ ->
  virtio_complete_ok v r i = true.
Proof. exact (virtio_complete_ok_in v r i). Qed.

(* ...and with an EMPTY cache -- the state this test's device is in -- it is
   not gated at all, which is why the eager schedule serves it in one step *)
Lemma model_unknown_type_empty_cache (v : virtio_state) (r : vio_req)
    (i : bv 16) :
  bv_unsigned (vr_type r) <> virtio_blk_t_out ->
  bv_unsigned (vr_type r) <> virtio_blk_t_flush ->
  v_cache v = ∅ ->
  virtio_complete_ok v r i = true.
Proof.
  intros H1 H2 Hc. apply (virtio_complete_ok_in v r i H1 H2).
  rewrite Hc, dom_empty_L. set_solver.
Qed.

(* THE FLUSH IS A BARRIER, and this is the whole of what that means in the
   model: the completion is enabled only once the volatile write cache has
   drained to the durable image.  In this test the driver is writethrough,
   so the cache was already empty and the flush completed at once -- the
   test therefore confirms the OK status but not the barrier.  The barrier
   is the statement below. *)
Lemma model_flush_needs_empty_cache (v : virtio_state) (r : vio_req)
    (i : bv 16) :
  bv_unsigned (vr_type r) = virtio_blk_t_flush ->
  virtio_complete_ok v r i = true -> v_cache v = ∅.
Proof.
  intros Hf Hok. apply (virtio_complete_ok_flush v r i); [| exact Hf | exact Hok].
  rewrite Hf. unfold virtio_blk_t_flush, virtio_blk_t_out. lia.
Qed.

(* ---- from the retired ConcSb.v ---- *)

(* ---------------------------------------------------------------------- *)

Lemma model_hart_sees_the_one_memory : forall g c, mem (ghart g c) = gmem g.
Proof. reflexivity. Qed.

Lemma model_store_is_immediately_global : forall g c s, gmem (gput g c s) = mem s.
Proof. reflexivity. Qed.

(* ---- from the retired PtTlb.v ---- *)

(* the Sv39 virtual page number, the width [tlb_hash] indexes on *)
Definition sv39_vpn (v : Z) :=
  SailStdpp.Values.mword_of_int (len := 39 - 12) v.

Lemma model_tlb_is_64_way_direct_mapped : num_tlb_entries_exp = 6.
Proof. reflexivity. Qed.

Lemma model_tlb_sets_collide :
  tlb_hash 39 (sv39_vpn 0x40000) = tlb_hash 39 (sv39_vpn 0x80000)
  /\ tlb_hash 39 (sv39_vpn 0x40000) = tlb_hash 39 (sv39_vpn 0x80100).
Proof. split; vm_compute; reflexivity. Qed.

Lemma model_tlb_set7_does_not :
  tlb_hash 39 (sv39_vpn 0x40007) <> tlb_hash 39 (sv39_vpn 0x80000).
Proof. vm_compute; discriminate. Qed.
