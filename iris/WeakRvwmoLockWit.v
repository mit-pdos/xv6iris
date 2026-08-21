(** * WeakRvwmoLockWit.v — THE LOCK-PROTOCOL KIT'S SATISFIABILITY WITNESS

    Design: [claude-notes/design/weak-memory-route-b.md] §4c (B2e-2); the kit
    itself is [WeakRvwmoLock.v].

    THE POINT.  [WeakRvwmoLock.cs_kill] is a KILL — its conclusion is [False],
    so nothing about its statement rules out the hypotheses being jointly
    contradictory, and a contradictory hypothesis set would make B2e-3's
    consumption of it worthless.  This file closes that gap with a concrete
    two-hart graph [lkg] on which every PROTOCOL and COVERAGE hypothesis of
    [cs_kill] holds simultaneously ([cs_kill_hyps_sat]).

    WHY THE K1 CONFIGURATION IS DELIBERATELY LEFT OUT of the conjunction.
    [cs_kill]'s remaining three hypotheses — [gviol G e w], [gmo_lt G w w0],
    [gmo_lt G w0 e] — are the rule-14 VIOLATION the kill exists to refute.  A
    graph satisfying those AND the protocol/coverage facts cannot exist:
    that is exactly what [cs_kill] proves.  So "satisfiable" can only ever
    mean the hypothesis set MINUS the configuration, and the meaningful check
    is that the protocol side alone is realizable — that the kill's antecedent
    is not being discharged by a contradiction hiding in the lock protocol,
    the CS structures, the aq bits or the release fences.  [lkg_no_viol]
    records the other half: this witness is rule-14 CLEAN, so [cs_kill] is
    silent on it rather than firing, which is the correct behavior.

    THE DESIGN CORRECTION THIS CHECK FOUND (and its fix, landed in
    [WeakRvwmoGraph.v]).  Written against the model as it stood at the B2e-2
    landing, [cs_kill_hyps_sat] IS UNPROVABLE — and not for want of a clever
    graph: the hypothesis set was jointly contradictory for EVERY graph.
    [gacq_po] (ppo⁻ rule 5) read

        gpo G e1 e2 ∧ glbl_is G e1 lb_is_r ∧ glbl_is G e1 lb_aq

    with the SUCCESSOR unconstrained, while [gmo] holds the memory events
    only ([gwf]'s second clause).  Every lock client has its acquire po-before
    the release FENCE, so [gppo_gmo] demanded a gmo position for a fence and
    [rvwmo_minus_consistent] became unsatisfiable there.  (Machine-checked
    before the fix, from [cs_kill]'s own hart-[h] coverage facts alone.)  The
    fix is riscv.cat's own side condition, [ppo ⊆ M × M]: [gacq_po] gained a
    [gmem G e2] conjunct — the other three arms pin both endpoints already.
    It WEAKENS [rvwmo_minus_consistent] (fewer ppo⁻ edges to justify, so more
    graphs are consistent), which is the safe direction for a safety theorem,
    and the arm's only consumers ([acq_gmo_after], [gviol_no_aq],
    [lin_acq_po_gmo]) apply it at memory events anyway.

    THE WITNESS.  One lock byte (address 0) and one data byte (address 8);
    hart 0 takes the lock first, hart 1's acquire reads hart 0's release.

      hart 0                                hart 1
      (0,0) ACQ  amoswap.aq  b:0 -> 1       (1,0) ACQ  amoswap.aq  b:0 -> 1
                 reads the image (t=0)                 reads (0,3) (t=2)
      (0,1) LOAD d  (the CS body)           (1,1) STORE d := 1  (the CS body)
      (0,2) FENCE rw,rw                     (1,2) FENCE rw,rw
      (0,3) REL  store b := 0               (1,3) REL  store b := 0

    gmo is program order per hart with hart 0's section first, so the two
    windows are [1,2] and [3,5] in write indices — disjoint, which is
    [win_excl_of_pattern]'s conclusion made concrete ([lkg_win_excl]).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakRvwmoGraph
     WeakRvwmoXchg WeakRvwmoLock.

(* ====================================================================== *)
(** * 1. The graph *)

Definition lkg : gexec :=
  GExec WeakLitmus.img0
        [[LRmw true false 0 [0%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl;
          LLoad false 8 [0%nat] [WeakLitmus.b0];
          LFence true true true true;
          LStore true 0 [WeakLitmus.b0] WCrel];
         [LRmw true false 0 [2%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl;
          LStore false 8 [WeakLitmus.b1] WCplain;
          LFence true true true true;
          LStore true 0 [WeakLitmus.b0] WCrel]]
        [(0%nat, 0%nat); (0%nat, 1%nat); (0%nat, 3%nat);
         (1%nat, 0%nat); (1%nat, 1%nat); (1%nat, 3%nat)].

(** Shorthands for the six memory events. *)
Local Notation ACQh := (0%nat, 0%nat).
Local Notation EVh  := (0%nat, 1%nat).
Local Notation RELh := (0%nat, 3%nat).
Local Notation ACQj := (1%nat, 0%nat).
Local Notation EVj  := (1%nat, 1%nat).
Local Notation RELj := (1%nat, 3%nat).

(* ====================================================================== *)
(** * 2. Inversions and the position/index arithmetic *)

Lemma lkg_nodup : NoDup (gx_gmo lkg).
Proof.
  repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
Qed.

Lemma lkg_gpos_of (n : nat) (e : geid) : gx_gmo lkg !! n = Some e → gpos lkg e = n.
Proof. apply gpos_of_lookup, lkg_nodup. Qed.

Lemma lkg_gwix_of (n : nat) (w : geid) :
  gwrites lkg !! n = Some w → gwix lkg w = S n.
Proof. apply gwix_of_lookup, lkg_nodup. Qed.

Lemma lkg_p00 : gpos lkg ACQh = 0%nat. Proof. by apply lkg_gpos_of. Qed.
Lemma lkg_p01 : gpos lkg EVh  = 1%nat. Proof. by apply lkg_gpos_of. Qed.
Lemma lkg_p03 : gpos lkg RELh = 2%nat. Proof. by apply lkg_gpos_of. Qed.
Lemma lkg_p10 : gpos lkg ACQj = 3%nat. Proof. by apply lkg_gpos_of. Qed.
Lemma lkg_p11 : gpos lkg EVj  = 4%nat. Proof. by apply lkg_gpos_of. Qed.
Lemma lkg_p13 : gpos lkg RELj = 5%nat. Proof. by apply lkg_gpos_of. Qed.

Lemma lkg_w00 : gwix lkg ACQh = 1%nat. Proof. by apply lkg_gwix_of; vm_compute. Qed.
Lemma lkg_w03 : gwix lkg RELh = 2%nat. Proof. by apply lkg_gwix_of; vm_compute. Qed.
Lemma lkg_w10 : gwix lkg ACQj = 3%nat. Proof. by apply lkg_gwix_of; vm_compute. Qed.
Lemma lkg_w11 : gwix lkg EVj  = 4%nat. Proof. by apply lkg_gwix_of; vm_compute. Qed.
Lemma lkg_w13 : gwix lkg RELj = 5%nat. Proof. by apply lkg_gwix_of; vm_compute. Qed.

(** The six memory events, and nothing else. *)
Lemma lkg_mem_inv (e : geid) :
  gmem lkg e →
  e = ACQh ∨ e = EVh ∨ e = RELh ∨ e = ACQj ∨ e = EVj ∨ e = RELj.
Proof.
  intros (l & Hl & Hm). destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=; naive_solver.
Qed.

Lemma lkg_gmo_mem (e : geid) : gmem lkg e → e ∈ gx_gmo lkg.
Proof.
  intros [->|[->|[->|[->|[->| ->]]]]]%lkg_mem_inv;
    rewrite /gx_gmo /= !elem_of_cons; naive_solver.
Qed.

Lemma lkg_mo (e1 e2 : geid) :
  gmem lkg e1 → gmem lkg e2 → (gpos lkg e1 < gpos lkg e2)%nat →
  gmo_lt lkg e1 e2.
Proof.
  intros H1 H2 Hlt.
  split_and!; [by apply lkg_gmo_mem|by apply lkg_gmo_mem|exact Hlt].
Qed.

(** THE SHAPE OF THIS EXECUTION: gmo IS per-hart program order (hart 0's
    section first), so every same-hart po-earlier memory event is gmo-earlier.
    Every ppo⁻ arm is same-hart, po-earlier and memory-to-memory, so this one
    lemma discharges [gppo_gmo] wholesale. *)
Lemma lkg_gmo_po (e1 e2 : geid) :
  gmem lkg e1 → gmem lkg e2 → e1.1 = e2.1 → (e1.2 < e2.2)%nat →
  gmo_lt lkg e1 e2.
Proof.
  intros Hm1 Hm2 Hag Hlt.
  split_and!; [by apply lkg_gmo_mem|by apply lkg_gmo_mem|].
  apply lkg_mem_inv in Hm1. apply lkg_mem_inv in Hm2.
  destruct Hm1 as [->|[->|[->|[->|[->| ->]]]]];
    destruct Hm2 as [->|[->|[->|[->|[->| ->]]]]];
    simpl in Hag, Hlt; try lia;
    rewrite ?lkg_p00 ?lkg_p01 ?lkg_p03 ?lkg_p10 ?lkg_p11 ?lkg_p13; lia.
Qed.

(** The write footprints. *)
Lemma lkg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte lkg e a v →
  (e = ACQh ∧ a = 0%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELh ∧ a = 0%Z ∧ v = WeakLitmus.b0) ∨
  (e = ACQj ∧ a = 0%Z ∧ v = WeakLitmus.b1) ∨
  (e = EVj  ∧ a = 8%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELj ∧ a = 0%Z ∧ v = WeakLitmus.b0).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

(** The read footprints. *)
Lemma lkg_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte lkg e a t v →
  (e = ACQh ∧ a = 0%Z ∧ t = 0%nat ∧ v = WeakLitmus.b0) ∨
  (e = EVh  ∧ a = 8%Z ∧ t = 0%nat ∧ v = WeakLitmus.b0) ∨
  (e = ACQj ∧ a = 0%Z ∧ t = 2%nat ∧ v = WeakLitmus.b0).
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

(** The two per-byte specializations the protocol proofs use. *)
Lemma lkg_wr_lock (w : geid) (v : bv 8) :
  gwrites_byte lkg w 0%Z v →
  (w = ACQh ∧ v = WeakLitmus.b1) ∨ (w = RELh ∧ v = WeakLitmus.b0) ∨
  (w = ACQj ∧ v = WeakLitmus.b1) ∨ (w = RELj ∧ v = WeakLitmus.b0).
Proof.
  intros [(->&_&->)|[(->&_&->)|[(->&_&->)|[(_&Hab&_)|(->&_&->)]]]]%lkg_wr;
    auto. discriminate Hab.
Qed.

Lemma lkg_wr_data (w : geid) (v : bv 8) :
  gwrites_byte lkg w 8%Z v → w = EVj ∧ v = WeakLitmus.b1.
Proof.
  intros [(_&Hab&_)|[(_&Hab&_)|[(_&Hab&_)|[(->&_&->)|(_&Hab&_)]]]]%lkg_wr;
    by [discriminate Hab|].
Qed.

(* ====================================================================== *)
(** * 3. [lkg] is RVWMO⁻-consistent *)

Theorem lkg_consistent : rvwmo_minus_consistent lkg.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + exact lkg_nodup.
    + intros e. split.
      * intros He. rewrite /gx_gmo /= !elem_of_cons elem_of_nil in He.
        destruct He as [->|[->|[->|[->|[->|[->|[]]]]]]];
          eexists; split; reflexivity.
      * apply lkg_gmo_mem.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|[|[|k]]]]; simplify_eq/=; done.
  - (* ppo⁻ ⊆ gmo: every arm is same-hart, po-earlier, memory-to-memory *)
    intros e1 e2 Hppo.
    destruct (gppo_gmem lkg e1 e2 Hppo) as [Hm1 Hm2].
    destruct (gppo_po_lt lkg e1 e2 Hppo) as [Hag Hlt].
    by apply lkg_gmo_po.
  - (* load value *)
    intros e a t v [(->&->&->&->)|[(->&->&->&->)|(->&->&->&->)]]%lkg_rd.
    + (* the h-acquire reads the image: it is gmo- and po-first *)
      split; [exact WeakLitmus.img0_x|].
      intros w' v' Hw' Hvis.
      destruct Hvis as [(_ & _ & Hp)|(Hag & Hoff & _)];
        [|by destruct w' as [i k]; simpl in Hoff; lia].
      exfalso. rewrite lkg_p00 in Hp. lia.
    + (* the CS-body load reads the data byte's image value *)
      split; [exact WeakLitmus.img0_y|].
      intros w' v' [-> ->]%lkg_wr_data Hvis.
      exfalso. destruct Hvis as [(_ & _ & Hp)|(Hag & _ & _)];
        [rewrite lkg_p11 lkg_p01 in Hp; lia|by simpl in Hag].
    + (* the j-acquire reads the h-release, which is co-maximal below it *)
      split.
      * exists RELh. split_and!.
        { by vm_compute. }
        { by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z,
                    [WeakLitmus.b0], 0%nat. }
        { left. apply lkg_mo; [by eexists|by eexists|].
          rewrite lkg_p03 lkg_p10. lia. }
      * intros w' v' [[-> _]|[[-> _]|[[-> _]|[-> _]]]]%lkg_wr_lock Hvis.
        { rewrite lkg_w00. lia. }
        { rewrite lkg_w03. lia. }
        { exfalso. destruct Hvis as [Hmo|(_ & Hoff & _)];
            [by eapply gmo_lt_irrefl|simpl in Hoff; lia]. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)];
            [rewrite lkg_p13 lkg_p10 in Hp; lia|simpl in Hoff; lia]. }
  - (* atomicity: the two RMWs read their own immediate co-predecessor *)
    intros e a t v [(->&->&->&->)|[(->&->&->&->)|(->&->&->&->)]]%lkg_rd
           Hw w' v' Hw' [Hlo Hhi].
    + rewrite lkg_w00 in Hhi. lia.
    + destruct Hw as (l & Hl & Hlw). rewrite /gx_lbl /= in Hl. by simplify_eq.
    + rewrite lkg_w10 in Hhi. lia.
Qed.

(* ====================================================================== *)
(** * 4. The lock protocol on byte 0 *)

Theorem lkg_pattern : lock_pattern lkg 0%Z.
Proof.
  split.
  - intros v0 Hv.
    assert (Hx : gx_img lkg 0%Z = Some lock_free) by exact WeakLitmus.img0_x.
    rewrite Hx in Hv. by simplify_eq.
  - intros w v [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]%lkg_wr_lock.
    + left. split_and!.
      * by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0]
                        [WeakLitmus.b1] WCexcl).
      * intros Heq. by apply WeakLitmus.b0_ne_b1.
      * exists 0%nat. by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0]
                                   [WeakLitmus.b1] WCexcl), 0%Z,
                                [0%nat], [WeakLitmus.b0], 0%nat.
    + by right.
    + left. split_and!.
      * by exists (LRmw true false 0 [2%nat] [WeakLitmus.b0]
                        [WeakLitmus.b1] WCexcl).
      * intros Heq. by apply WeakLitmus.b0_ne_b1.
      * exists 2%nat. by exists (LRmw true false 0 [2%nat] [WeakLitmus.b0]
                                   [WeakLitmus.b1] WCexcl), 0%Z,
                                [2%nat], [WeakLitmus.b0], 0%nat.
    + by right.
Qed.

Lemma lkg_acq_h : lock_acq lkg 0%Z ACQh.
Proof.
  exists WeakLitmus.b1. split.
  - by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl),
              0%Z, [WeakLitmus.b1], 0%nat.
  - intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

Lemma lkg_acq_j : lock_acq lkg 0%Z ACQj.
Proof.
  exists WeakLitmus.b1. split.
  - by exists (LRmw true false 0 [2%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl),
              0%Z, [WeakLitmus.b1], 0%nat.
  - intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

Lemma lkg_rel_h : lock_rel lkg 0%Z RELh.
Proof.
  by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z, [WeakLitmus.b0], 0%nat.
Qed.

Lemma lkg_rel_j : lock_rel lkg 0%Z RELj.
Proof.
  by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z, [WeakLitmus.b0], 0%nat.
Qed.

(** The two critical sections, built the way B2e-3 will build them: from the
    PO-LOCAL fact that between my acquire and my release my hart writes the
    lock byte nowhere else. *)
Theorem lkg_cs_h : lock_cs lkg 0%Z ACQh RELh.
Proof.
  apply lock_cs_intro; [exact lkg_consistent| | | |].
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkg_acq_h.
  - exact lkg_rel_h.
  - intros x v [[-> _]|[[-> _]|[[-> _]|[-> _]]]]%lkg_wr_lock Hag Hlo Hhi;
      simpl in *; lia.
Qed.

Theorem lkg_cs_j : lock_cs lkg 0%Z ACQj RELj.
Proof.
  apply lock_cs_intro; [exact lkg_consistent| | | |].
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkg_acq_j.
  - exact lkg_rel_j.
  - intros x v [[-> _]|[[-> _]|[[-> _]|[-> _]]]]%lkg_wr_lock Hag Hlo Hhi;
      simpl in *; lia.
Qed.

Theorem lkg_paired : lock_paired lkg 0%Z.
Proof.
  intros R HR.
  destruct (lkg_wr_lock R lock_free HR)
    as [[-> Hv]|[[-> _]|[[-> Hv]|[-> _]]]].
  - exfalso. by apply WeakLitmus.b0_ne_b1.
  - exists ACQh. exact lkg_cs_h.
  - exfalso. by apply WeakLitmus.b0_ne_b1.
  - exists ACQj. exact lkg_cs_j.
Qed.

(* ====================================================================== *)
(** * 5. THE WINDOWS REALLY ORDER

    [win_excl_of_pattern]'s conclusion instantiated at the two sections — and
    resolved: it is the LEFT disjunct, hart 0's release (write index 2) below
    hart 1's acquire (write index 3). *)

Theorem lkg_win_excl :
  (gwix lkg RELh < gwix lkg ACQj)%nat ∨ (gwix lkg RELj < gwix lkg ACQh)%nat.
Proof.
  apply (win_excl_of_pattern lkg 0%Z lkg_consistent lkg_pattern lkg_paired
           ACQh RELh ACQj RELj lkg_cs_h lkg_cs_j).
  by intros Heq.
Qed.

Corollary lkg_win_excl_h_first : (gwix lkg RELh < gwix lkg ACQj)%nat.
Proof.
  destruct lkg_win_excl as [H|H]; [exact H|].
  rewrite lkg_w13 lkg_w00 in H. lia.
Qed.

(* ====================================================================== *)
(** * 6. THE COVERAGE FACTS, AND THE SATISFIABILITY STATEMENT *)

Lemma lkg_aq_h : glbl_is lkg ACQh lb_aq.
Proof.
  by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl).
Qed.

Lemma lkg_aq_j : glbl_is lkg ACQj lb_aq.
Proof.
  by exists (LRmw true false 0 [2%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl).
Qed.

(** The release fence covers the CS body to the release: [(0,2)] / [(1,2)]
    sit at an INTERMEDIATE po position of the same hart, which is
    [gfence_between]'s shape. *)
Lemma lkg_fence_h : gfence_covers lkg EVh RELh.
Proof.
  exists true, true, true, true. split_and!.
  - split_and!; [done|simpl; lia|]. exists 2%nat. split_and!; [simpl; lia|simpl; lia|done].
  - left. split; [by exists (LLoad false 8 [0%nat] [WeakLitmus.b0])|done].
  - right. split; [by exists (LStore true 0 [WeakLitmus.b0] WCrel)|done].
Qed.

Lemma lkg_fence_j : gfence_covers lkg EVj RELj.
Proof.
  exists true, true, true, true. split_and!.
  - split_and!; [done|simpl; lia|]. exists 2%nat. split_and!; [simpl; lia|simpl; lia|done].
  - right. split; [by exists (LStore false 8 [WeakLitmus.b1] WCplain)|done].
  - right. split; [by exists (LStore true 0 [WeakLitmus.b0] WCrel)|done].
Qed.

(** THE STATEMENT: every hypothesis of [WeakRvwmoLock.cs_kill] except the
    three K1-configuration facts ([gviol G e w], [gmo_lt G w w0],
    [gmo_lt G w0 e]) holds simultaneously.  See the header for why the
    configuration must be excluded — a graph carrying it as well is exactly
    what [cs_kill] refutes. *)
Theorem cs_kill_hyps_sat :
  ∃ (G : gexec) (b : Z) (e w0 A_h R_h A_j R_j : geid),
    rvwmo_minus_consistent G ∧
    lock_pattern G b ∧ lock_paired G b ∧
    lock_cs G b A_h R_h ∧
    gpo G A_h e ∧ glbl_is G A_h lb_aq ∧ gfence_covers G e R_h ∧
    lock_cs G b A_j R_j ∧
    gpo G A_j w0 ∧ glbl_is G A_j lb_aq ∧ gfence_covers G w0 R_j ∧
    e.1 ≠ w0.1.
Proof.
  exists lkg, 0%Z, EVh, EVj, ACQh, RELh, ACQj, RELj. split_and!.
  - exact lkg_consistent.
  - exact lkg_pattern.
  - exact lkg_paired.
  - exact lkg_cs_h.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkg_aq_h.
  - exact lkg_fence_h.
  - exact lkg_cs_j.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkg_aq_j.
  - exact lkg_fence_j.
  - by simpl.
Qed.

(* ====================================================================== *)
(** * 7. THE OTHER HALF: the witness has no violation

    [cs_kill] is not vacuous, but neither does it FIRE here: [lkg] is
    rule-14 clean, so the configuration facts it would need are absent.  That
    is the correct behavior, and it is why §6's conjunction stops where it
    does. *)

Theorem lkg_no_viol (e w : geid) : ¬ gviol lkg e w.
Proof.
  intros (Hpo & Hme & Hw & Hmo).
  pose proof Hpo as (Hag & Hlt & _ & _).
  apply (gmo_lt_irrefl lkg e), (gmo_lt_trans lkg e w e); [|exact Hmo].
  apply lkg_gmo_po; [exact Hme|by apply glbl_is_w_gmem|exact Hag|exact Hlt].
Qed.

Theorem lkg_rule14 : grule14 lkg.
Proof.
  apply gviol_grule14; [by destruct lkg_consistent as (? & _)|exact lkg_no_viol].
Qed.
