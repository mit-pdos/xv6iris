(* ====================================================================== *)
(* WpVirtio.v -- the Iris layer over the virtio disk (VirtioModel.v).      *)
(*                                                                         *)
(* Two things live here.                                                   *)
(*                                                                         *)
(* §1  The device-state ghost half, exactly like the UART's and the PLIC's: *)
(*     [virtio_auth] rides in [state_interp] (via [dev_interp]) and the     *)
(*     user-facing [virtio_frag] floats, so a driver borrows it by opening  *)
(*     the device invariant around an (atomic) MMIO access.                 *)
(*                                                                         *)
(* §2  The DMA LEASE -- the part that has no analogue among the other       *)
(*     devices, because the disk is the only BUS MASTER.  The device        *)
(*     thread's step overwrites bytes of the harts' memory                  *)
(*     (RiscvLang.DevStepDisk), so to justify that step at the Iris level   *)
(*     the thread must OWN those bytes.  What it owns is                    *)
(*                                                                         *)
(*       [virtio_lease v] = an existentially-quantified set of physical     *)
(*       bytes ([dma_own dma]) big enough for any request the CONFIGURATION *)
(*       of [v] can produce ([virtio_dma_ok], VirtioModel §6).              *)
(*                                                                         *)
(*     The lease's pure side condition is stated over the configuration     *)
(*     alone, which is why [virtio_lease_step] can hand it back after every *)
(*     autonomous step with nothing to re-prove: only a DRIVER's MMIO write *)
(*     can invalidate it, and re-establishing it there is precisely the     *)
(*     obligation: the descriptors a driver publishes must point into memory *)
(*     it has already handed to the device.  See                             *)
(*     claude-notes/projects/virtio-disk.md.                                 *)
(* ====================================================================== *)
(* IMPORTANT: do NOT add [SailStdpp.Base]/[SailStdpp.Values] here.  They leak
   the Sail key instances, and the [gmap Arch.pa (bv 8)] in this file's
   statements would then elaborate with a Countable instance different from the
   one [gen_heap_interp] (RiscvPtsto, which imports neither) was built with --
   "Could not find an instance for gen_heapGS".  Mirror RiscvPtsto's imports. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import DevModel.

Section WpVirtio.
  Context `{!riscvGS Σ}.

  (* ==================================================================== *)
  (* §1  the device-fabric ghost bridge for the disk                       *)
  (* ==================================================================== *)

  Lemma dev_interp_agree_virtio d v :
    dev_interp d -∗ virtio_frag v -∗ ⌜dvirtio d = v⌝.
  Proof.
    iIntros "(_ & _ & Hva) Hv".
    by iDestruct (virtio_agree with "Hva Hv") as %->.
  Qed.

  Lemma dev_interp_update_virtio d v v' :
    dev_interp d -∗ virtio_frag v ==∗ dev_interp (set_dvirtio d v') ∗ virtio_frag v'.
  Proof.
    iIntros "(Hua & Hpa & Hva) Hv".
    iMod (virtio_update with "Hva Hv") as "[$ $]".
    rewrite /set_dvirtio /dev_interp /=. by iFrame "Hua Hpa".
  Qed.

  (* ==================================================================== *)
  (* §2  the DMA lease                                                     *)
  (* ==================================================================== *)

  (* Ownership of a finite set of PHYSICAL bytes, as a map from address to
     current contents.  [↦ₚ] is the right points-to: DMA is a physical-address
     transaction, and it carries the [addr_is_ram] side condition, so a lease
     can never name a device register. *)
  Definition dma_own (dma : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ dma, phys_pointsto a (DfracOwn 1) b)%I.

  Global Instance phys_pointsto_timeless a dq b :
    Timeless (phys_pointsto a dq b).
  Proof. rewrite /phys_pointsto. apply _. Qed.

  Global Instance dma_own_timeless dma : Timeless (dma_own dma).
  Proof. rewrite /dma_own. apply big_sepM_timeless. apply _. Qed.

  (* The lease agrees with the real memory: it is a sub-map of it. *)
  Lemma dma_agree (m dma : gmap Arch.pa (bv 8)) :
    gen_heap_interp m -∗ dma_own dma -∗ ⌜dma ⊆ m⌝.
  Proof.
    revert m. induction dma as [|a b dma' Hnew IH] using map_ind; iIntros (m) "Hm Hd".
    { iPureIntro. apply map_empty_subseteq. }
    rewrite /dma_own big_sepM_insert; [|exact Hnew].
    iDestruct "Hd" as "[Hp Hd']".
    iEval (rewrite /phys_pointsto) in "Hp". iDestruct "Hp" as "[Hp _]".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hma.
    iDestruct (IH m with "Hm Hd'") as %Hsub.
    iPureIntro. by apply insert_subseteq_l.
  Qed.

  (* Overwrite the leased bytes the device just wrote.  The lease's DOMAIN is
     unchanged (a write set inside the lease), so the same lease is handed
     back with fresh contents. *)
  Lemma dma_update (w m dma : gmap Arch.pa (bv 8)) :
    dom w ⊆ dom dma ->
    gen_heap_interp m -∗ dma_own dma ==∗
      gen_heap_interp (w ∪ m) ∗ dma_own (w ∪ dma).
  Proof.
    revert m dma.
    induction w as [|a b w' Hnew IH] using map_ind; iIntros (m dma Hdom) "Hm Hd".
    { rewrite !left_id_L. by iFrame. }
    rewrite dom_insert_L in Hdom.
    assert (Hdw : dom w' ⊆ dom dma) by set_solver.
    assert (Ha : a ∈ dom dma) by set_solver.
    iMod (IH m dma Hdw with "Hm Hd") as "[Hm Hd]".
    assert (Ha' : a ∈ dom (w' ∪ dma)) by (rewrite dom_union_L; set_solver).
    apply elem_of_dom in Ha' as [b0 Hb0].
    rewrite /dma_own.
    iDestruct (big_sepM_insert_acc _ _ a b0 Hb0 with "Hd") as "[Hp Hback]".
    iEval (rewrite /phys_pointsto) in "Hp". iDestruct "Hp" as "[Hp %Hram]".
    iMod (gen_heap_update _ a b0 b with "Hm Hp") as "[Hm Hp]".
    iDestruct ("Hback" $! b with "[Hp]") as "Hd".
    { rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact Hram. }
    iModIntro. rewrite -!insert_union_l. iFrame "Hm Hd".
  Qed.

  (* -- the lease itself -- *)

  (* [ctl] is the CONTROL region of the lease: bytes the invariant owns and the
     device only ever READS -- the descriptor table and the available ring.
     [S] is the set of available-ring positions the device may still reach, and
     [ai] the published index.  The pure conjunct is POSITIVE: it asserts that
     every reachable entry really is a well-formed request writing only inside
     the lease, rather than merely constraining the writes of a step that
     happens.  That is what makes a misconfigured queue unverifiable instead of
     vacuously fine -- see VirtioModel section 7. *)
  Definition virtio_lease (v : virtio_state) : iProp Σ :=
    (∃ (ctl dma : gmap Arch.pa (bv 8)) (S : gset (bv 16)) (ai : bv 16),
       dma_own dma ∗ ⌜ctl ⊆ dma⌝ ∗
       ⌜virtio_queue_ok (v_cfg v) ctl (dom dma) S ai (v_seen v)⌝)%I.

  Global Instance virtio_lease_timeless v : Timeless (virtio_lease v).
  Proof. rewrite /virtio_lease. apply _. Qed.

  (* The lease depends on the queue CONFIGURATION and on how far the device has
     got, and on nothing else: it rides through any other change to the device
     state.  A driver's INTERRUPT_ACK and QUEUE_NOTIFY writes qualify
     ([virtio_write_cfg_stable] + [virtio_write_seen]). *)
  Lemma virtio_lease_stable (v v' : virtio_state) :
    v_cfg v' = v_cfg v -> v_seen v' = v_seen v ->
    virtio_lease v -∗ virtio_lease v'.
  Proof. intros Hc Hs. rewrite /virtio_lease Hc Hs. iIntros "$". Qed.

  (* Before the driver has made the queue live, the device cannot look at the
     ring at all, so the EMPTY lease is already good.  This is what the
     power-on device state (and hence whole-system adequacy) allocates. *)
  Lemma virtio_lease_init (v : virtio_state) :
    virtio_live (v_cfg v) = false -> ⊢ virtio_lease v.
  Proof.
    intro Hlive. rewrite /virtio_lease.
    iExists ∅, ∅, ∅, zero16. rewrite /dma_own big_sepM_empty.
    iSplit; [done|]. iSplit; [iPureIntro; apply map_empty_subseteq|].
    iPureIntro. by apply virtio_queue_ok_not_live.
  Qed.

  (* DEVICE-THREAD RULE 1.  The lease REFUTES the write-anything step: the
     queue the driver published is well formed, so the device is never in the
     position of owing an answer this model does not have.  Without this the
     wild step of [DevStepDiskWild] would make [wp_dev_loop] unprovable -- which
     is precisely the pressure that turns queue well-formedness into a driver
     obligation. *)
  Lemma virtio_lease_not_stalled (m : gmap Arch.pa (bv 8)) (v : virtio_state)
      (mv : vmem) :
    mem_view m mv ->
    gen_heap_interp m -∗ virtio_lease v -∗ ⌜virtio_stalled v mv = false⌝.
  Proof.
    iIntros (Hview) "Hm Hl".
    iDestruct "Hl" as (ctl dma S ai) "(Hd & %Hctl & %Hok)".
    iDestruct (dma_agree with "Hm Hd") as %Hsub.
    iPureIntro.
    apply (virtio_queue_not_stalled v ctl (dom dma) S ai mv Hok).
    apply (mem_view_subseteq ctl m mv); [| exact Hview].
    etransitivity; [exact Hctl|exact Hsub].
  Qed.

  (* DEVICE-THREAD RULE 2.  A real DMA step is justified entirely from the
     lease: the write set lands inside it (so the byte memory can be updated)
     and misses the control region (so the same control bytes are still pinned
     for the next request).  Nothing about the queue's contents is re-proved
     here -- that was discharged once, by the driver, when it took the lease. *)
  Lemma virtio_lease_step (v : virtio_state) (m : gmap Arch.pa (bv 8))
      (mv : vmem) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
    mem_view m mv ->
    virtio_req_step v mv = Some (v', w) ->
    gen_heap_interp m -∗ virtio_lease v ==∗
      gen_heap_interp (w ∪ m) ∗ virtio_lease v'.
  Proof.
    iIntros (Hview Hstep) "Hm Hl".
    iDestruct "Hl" as (ctl dma S ai) "(Hd & %Hctl & %Hok)".
    iDestruct (dma_agree with "Hm Hd") as %Hsub.
    assert (Hctlm : ctl ⊆ m) by (etransitivity; [exact Hctl|exact Hsub]).
    assert (Hvctl : mem_view ctl mv)
      by (apply (mem_view_subseteq ctl m mv Hctlm Hview)).
    destruct (virtio_queue_ok_step v ctl (dom dma) S ai mv v' w Hok Hvctl Hstep)
      as (Hdw & Hdisj & Hok').
    iMod (dma_update w m dma Hdw with "Hm Hd") as "[Hm Hd]".
    iModIntro. iFrame "Hm".
    iExists ctl, (w ∪ dma), S, ai.
    iFrame "Hd". iSplit.
    { iPureIntro. exact (virtio_ctl_union ctl w dma Hdisj Hctl). }
    iPureIntro.
    assert (Hde : dom (w ∪ dma) = dom dma).
    { rewrite dom_union_L. set_solver. }
    rewrite Hde. exact Hok'.
  Qed.

End WpVirtio.
