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
(* A6.48 ruling 4: the DMA lease is a LEDGER lease now -- the device's write
   set has to pay the era log's append, and the timestamp elements that pay it
   ride inside the bytes the lease holds. *)
Require Import TsoCtx.
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
     current contents.  The tier is [TsoCtx.phys_ledger] -- the physical byte
     WITH its latest-write timestamp element (A6.48 ruling 4).  A raw [↦ₚ]
     was right while the device's write was invisible to the memory model;
     post-flip the completion APPENDS to the era log, and the four ghost steps
     that append owes ([Wobl_ram]) need exactly those elements.  [phys_ledger]
     still carries [addr_is_ram] underneath, so a lease still cannot name a
     device register.  It licenses no plain LOAD (no clean/dirty bit, A6.20),
     which is correct: nothing reads a leased byte through the ledger -- the
     driver reads it back through its own ctx tier after reclaim. *)
  Definition dma_own (dma : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ dma, phys_ledger a (DfracOwn 1) b)%I.

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
    iDestruct "Hd" as "[Hl Hd']".
    iDestruct (phys_ledger_forget with "Hl") as "Hp".
    iEval (rewrite /phys_pointsto) in "Hp". iDestruct "Hp" as "[Hp _]".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hma.
    iDestruct (IH m with "Hm Hd'") as %Hsub.
    iPureIntro. by apply insert_subseteq_l.
  Qed.

  (* THE LEASE IS AN ACCESSOR NOW, NOT AN UPDATER (A6.48 ruling 4, the
     inside-out).  [dma_update] used to do the [gen_heap] write itself; it
     cannot any more, because a device write APPENDS to the era log and
     [TsoCtxStore.ledger_store_ok] moves [gen_heap_interp] and [tso_interp_at]
     TOGETHER -- the interpretation's own tie relates the flat cell and the
     timestamp element, so the two authorities cannot be split across two
     lemmas.  So the lease hands its written-to bytes OUT at the ledger tier,
     the CALLER performs the one store gate, and the wand takes the new bytes
     back.  The domain is unchanged (a write set inside the lease), so the
     same lease comes back with fresh contents. *)
  Lemma dma_acc (w dma : gmap Arch.pa (bv 8)) :
    dom w ⊆ dom dma ->
    dma_own dma -∗
    ∃ old : gmap Arch.pa (bv 8), ⌜dom old = dom w⌝ ∗ ⌜old ⊆ dma⌝ ∗
      ([∗ map] a ↦ b ∈ old, phys_ledger a (DfracOwn 1) b) ∗
      (([∗ map] a ↦ b ∈ w, phys_ledger a (DfracOwn 1) b) -∗ dma_own (w ∪ dma)).
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

  (* The unkeyed [virtio_lease] that used to live here is gone: the keyed
     driver protocol ([VirtioProto.virtio_proto]) is the only lease in the
     tree, and [dma_own] / [dma_acc] above are its base layer. *)

End WpVirtio.
