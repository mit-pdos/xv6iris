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
(*     (RiscvLang.DiskStepDma), so to justify that step at the Iris level   *)
(*     the thread must OWN those bytes.  What it owns is                    *)
(*                                                                         *)
(*       [virtio_lease v] = an existentially-quantified set of physical     *)
(*       bytes ([dma_own dma]) big enough for any request the CONFIGURATION *)
(*       of [v] can produce ([virtio_dma_ok], VirtioModel §6).              *)
(*                                                                         *)
(*     The lease's pure side condition is stated over the configuration     *)
(*     alone, which is why [virtio_lease_acc] can hand it back after every  *)
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
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.

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
     back with fresh contents.

     THE SC STORE GATE, AND IT IS THE PIECE THE CUTOVER DELETES
     (tso-machine-flip.md A6.48 ruling 4).  Post-flip a device write is an
     APPEND to the era log, and [TsoCtx.ledger_store_ok] moves
     [gen_heap_interp] and [tso_interp_at] TOGETHER -- the interpretation's
     own tie relates the flat cell to its timestamp element -- so the two
     authorities cannot be split across two lemmas and the lease may not
     perform its own write.  What survives the cutover is the ACCESSOR
     ([dma_acc] below) and the shape it forces on everything above it; this
     update and [phys_map_store] are its SC stand-ins, and at cutover the one
     caller ([WpUart]'s disk loop) calls [TsoCtx.ledger_store_ok] instead. *)
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

  (* THE STORE GATE, AT THE SHAPE THE CUTOVER WANTS: the caller hands in the
     write set's OLD bytes and takes the NEW ones back, and the heap moves
     with them.  Stated over a bare big-op (not [dma_own]) because that is
     what travels through [virtio_proto_step]'s accessor -- the lease itself
     is rebuilt by the wand, not by this lemma.  At cutover this is
     [TsoCtx.ledger_store_ok] and the bytes are [phys_ledger]s. *)
  Lemma phys_map_store (w old m : gmap Arch.pa (bv 8)) :
    dom old = dom w ->
    gen_heap_interp m -∗
    ([∗ map] a ↦ b ∈ old, phys_pointsto a (DfracOwn 1) b) ==∗
      gen_heap_interp (w ∪ m) ∗
      ([∗ map] a ↦ b ∈ w, phys_pointsto a (DfracOwn 1) b).
  Proof.
    intros Hdom. iIntros "Hm Hold".
    iMod (dma_update w m old ltac:(rewrite Hdom; reflexivity)
            with "Hm Hold") as "[Hm Hd]".
    iModIntro. iFrame "Hm".
    assert (Hwo : w ∪ old = w).
    { apply map_eq. intros a. destruct (w !! a) as [b|] eqn:Hw.
      - by rewrite (lookup_union_Some_l _ _ _ _ Hw).
      - rewrite (lookup_union_r _ _ _ Hw).
        apply not_elem_of_dom. rewrite Hdom.
        by apply not_elem_of_dom. }
    rewrite /dma_own Hwo. iFrame "Hd".
  Qed.

  (* THE LEASE IS AN ACCESSOR, NOT AN UPDATER (tso-machine-flip.md A6.48
     ruling 4, the INSIDE-OUT).  The lease hands its written-to bytes OUT,
     the CALLER performs the one store gate, and the wand takes the new bytes
     back.  The domain is unchanged (a write set inside the lease), so the
     same lease comes back with fresh contents.

     THE SHAPE IS THE POINT, not the tier: at SC the bytes are [↦ₚ] and the
     gate is [phys_map_store] above; post-flip the bytes carry their
     timestamp elements ([TsoCtx.phys_ledger]) and the gate is
     [TsoCtx.ledger_store_ok].  Turning the lemma inside out is what lets the
     ONE holder of both authorities do the write. *)
  Lemma dma_acc (w dma : gmap Arch.pa (bv 8)) :
    dom w ⊆ dom dma ->
    dma_own dma -∗
    ∃ old : gmap Arch.pa (bv 8), ⌜dom old = dom w⌝ ∗ ⌜old ⊆ dma⌝ ∗
      ([∗ map] a ↦ b ∈ old, phys_pointsto a (DfracOwn 1) b) ∗
      (([∗ map] a ↦ b ∈ w, phys_pointsto a (DfracOwn 1) b) -∗ dma_own (w ∪ dma)).
  Proof.
    intros Hdom. iIntros "Hd".
    iExists (filter (fun p => p.1 ∈ dom w) dma).
    assert (Hsub : filter (fun p : Arch.pa * bv 8 => p.1 ∈ dom w) dma ⊆ dma)
      by apply map_filter_subseteq.
    assert (Hdomf : dom (filter (fun p : Arch.pa * bv 8 => p.1 ∈ dom w) dma)
                    = dom w).
    { apply set_eq. intros a. rewrite elem_of_dom. split.
      - intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ Ha]. exact Ha.
      - intros Ha. apply Hdom in Ha as Hd'. apply elem_of_dom in Hd' as [b Hb].
        exists b. apply map_lookup_filter_Some. by split. }
    iSplit; [by iPureIntro|]. iSplit; [by iPureIntro|].
    rewrite /dma_own -{1}(map_filter_union_complement
              (fun p : Arch.pa * bv 8 => p.1 ∈ dom w) dma).
    rewrite big_sepM_union; last apply map_disjoint_filter_complement.
    iDestruct "Hd" as "[$ Hrest]".
    iIntros "Hnew". rewrite /dma_own.
    (* the new bytes replace the old ones pointwise: [w ∪ dma] is [w] over
       the filtered part and [dma] elsewhere *)
    assert (Hwd : w ∪ dma
              = w ∪ filter (fun p : Arch.pa * bv 8 => ¬ (p.1 ∈ dom w)) dma).
    { apply map_eq. intros a. destruct (w !! a) as [b|] eqn:Hw.
      - by rewrite !(lookup_union_Some_l _ _ _ _ Hw).
      - rewrite !(lookup_union_r _ _ _ Hw).
        assert (Hnin : ¬ (a ∈ dom w))
          by (rewrite not_elem_of_dom; exact Hw).
        destruct (dma !! a) as [b|] eqn:Hda.
        + symmetry. apply map_lookup_filter_Some. by split.
        + symmetry. apply map_lookup_filter_None. by left. }
    rewrite Hwd big_sepM_union; last first.
    { apply map_disjoint_dom. intros a Ha Hb.
      apply elem_of_dom in Hb as [b Hb'].
      apply map_lookup_filter_Some in Hb' as [_ Hnin]. exact (Hnin Ha). }
    iFrame "Hnew Hrest".
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
     wild step of [DiskStepWild] would make [wp_disk_loop] unprovable -- which
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
     here -- that was discharged once, by the driver, when it took the lease.

     ...and the same INSIDE OUT (A6.48 ruling 4): the lease no longer writes
     the memory, it hands the write set's OLD bytes out and takes the NEW
     ones back.  [gen_heap_interp] goes in for [dma_agree]'s pure fact and
     comes straight back untouched -- the one store gate that moves it (and,
     post-flip, the era log with it) belongs to the caller. *)
  Lemma virtio_lease_acc (v : virtio_state) (m : gmap Arch.pa (bv 8))
      (mv : vmem) (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
    mem_view m mv ->
    virtio_req_step v mv = Some (v', w) ->
    gen_heap_interp m -∗ virtio_lease v -∗
      gen_heap_interp m ∗
      ∃ old : gmap Arch.pa (bv 8), ⌜dom old = dom w⌝ ∗
        ([∗ map] a ↦ b ∈ old, phys_pointsto a (DfracOwn 1) b) ∗
        (([∗ map] a ↦ b ∈ w, phys_pointsto a (DfracOwn 1) b) -∗ virtio_lease v').
  Proof.
    iIntros (Hview Hstep) "Hm Hl".
    iDestruct "Hl" as (ctl dma S ai) "(Hd & %Hctl & %Hok)".
    iDestruct (dma_agree with "Hm Hd") as %Hsub.
    assert (Hctlm : ctl ⊆ m) by (etransitivity; [exact Hctl|exact Hsub]).
    assert (Hvctl : mem_view ctl mv)
      by (apply (mem_view_subseteq ctl m mv Hctlm Hview)).
    destruct (virtio_queue_ok_step v ctl (dom dma) S ai mv v' w Hok Hvctl Hstep)
      as (Hdw & Hdisj & Hok').
    iFrame "Hm".
    iDestruct (dma_acc w dma Hdw with "Hd")
      as (old) "(%Hdo & %Hos & Hold & Hback)".
    iExists old. iFrame "Hold". iSplit; [by iPureIntro|].
    iIntros "Hnew". iDestruct ("Hback" with "Hnew") as "Hd".
    iExists ctl, (w ∪ dma), S, ai.
    iFrame "Hd". iSplit.
    { iPureIntro. exact (virtio_ctl_union ctl w dma Hdisj Hctl). }
    iPureIntro.
    assert (Hde : dom (w ∪ dma) = dom dma).
    { rewrite dom_union_L. set_solver. }
    rewrite Hde. exact Hok'.
  Qed.

End WpVirtio.
