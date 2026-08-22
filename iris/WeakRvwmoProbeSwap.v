(** * WeakRvwmoProbeSwap.v — THE FAILED-SWAP PROBE: [lock_pattern] IS FALSE
    FOR EVERY CONTENDED xv6 LOCK

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.1, finding F4(a).
    The kit under probe is [WeakRvwmoLock.v]; this file does not modify it.

    THE FINDING.  xv6's [acquire] spins with

        while (__sync_lock_test_and_set(&lk->locked, 1) != 0) ;

    i.e. an [amoswap.w.aq] that UNCONDITIONALLY WRITES 1 on every iteration.
    A FAILED iteration — the lock is held, the swap returns 1 — is therefore
    a [b]-write of a NONZERO byte whose own read entry at [b] names a NONZERO
    value.  [WeakRvwmoLock.lock_pattern G b] admits exactly two kinds of
    [b]-write:

      - a RELEASE: [v = lock_free]; or
      - an ACQUIRE: [glbl_is G w lb_is_r ∧ v ≠ lock_free ∧
                     ∃ t, greads_byte G w b t lock_free].

    A failed swap is neither: it writes 1 (not a release) and reads 1 (so the
    acquire arm's [greads_byte … lock_free] is unsatisfiable at it — a write
    event's byte value is functional, [gwrites_byte_det], and so is a read
    entry's).  Hence [lock_pattern G b] is FALSE on every execution in which
    any lock is CONTENDED, and the kit's hypotheses cannot be discharged for
    xv6's rows: [lock_pattern] is a hypothesis of [win_excl_of_pattern] and,
    through it, of [cs_kill].

    THE REPAIR (not made here — this file only exhibits the obstruction).
    [lock_pattern] needs a THIRD ARM: an RMW that READS A NONZERO VALUE and
    WRITES A NONZERO VALUE — a failed swap.  Such a write is harmless to the
    window theory: it sits strictly inside some holder's window (its read
    source is a nonzero [b]-write, i.e. an acquire or another failed swap,
    and atomicity makes it that write's co-successor), it transmits no
    message and it closes no section.  But the repair is NOT confined to the
    definition:

      - [acq_no_overlap]'s induction over [gwix] currently case-splits every
        [b]-write into acquire / release; with the third arm it must SKIP the
        failed swaps — they are neither the opening nor the closing write of
        a section, and the minimal-overlap descent must step over them rather
        than treat them as a section boundary;
      - [acq_src_rel] ("a nonzero read index names a RELEASE") becomes false
        as stated: a failed swap's source is an acquire or another failed
        swap.  It survives only for the acquires proper (read index naming
        [lock_free]), which is where its consumers use it.

    WHAT IS MACHINE-CHECKED HERE.  [swg] below is [WeakRvwmoLockWit.lkg] with
    ONE extra event: hart 1 spins once — a failed [amoswap.w.aq] reading the
    1 that hart 0's acquire wrote — before its successful acquire.

      hart 0                                hart 1
      (0,0) ACQ  amoswap.aq  b:0 -> 1       (1,0) SWP amoswap.aq b:1 -> 1
                 reads the image (t=0)                reads (0,0) (t=1)  <<<< NEW
      (0,1) LOAD d  (the CS body)           (1,1) ACQ amoswap.aq b:0 -> 1
      (0,2) FENCE rw,rw                                reads (0,3) (t=3)
      (0,3) REL  store b := 0               (1,2) STORE d := 1  (the CS body)
                                            (1,3) FENCE rw,rw
                                            (1,4) REL  store b := 0

    gmo places the failed swap immediately after hart 0's acquire (so that
    atomicity's "no [b]-write co-between the source and the RMW" holds with
    the source being that acquire), and hart 0's release then still separates
    the two sections.  Three theorems:

      [swg_consistent]  : [rvwmo_minus_consistent swg] — a contended lock is
                          a LEGITIMATE execution, so the obstruction is real
                          and not an artifact of an inconsistent graph;
      [swg_no_pattern]  : [¬ lock_pattern swg 0] — THE FINDING;
      [swg_paired]      : [lock_paired swg 0] still holds — the graph is
                          otherwise protocol-clean, so [lock_pattern] is the
                          only hypothesis that breaks.  (The failed swap is
                          hart 1's own, po-BEFORE its acquire, so it is not
                          co-between hart 1's acquire and release and hart
                          1's section is unaffected.)

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakRvwmoGraph
     WeakRvwmoXchg WeakRvwmoLock.

(* ====================================================================== *)
(** * 1. The graph

    Write indices ([gwix], 1-based) after the insertion:

      1  ACQh  (0,0)      4  ACQj  (1,1)
      2  SWP   (1,0)      5  EVj   (1,2)
      3  RELh  (0,3)      6  RELj  (1,4)

    so the failed swap's read index is 1 (hart 0's acquire) and hart 1's
    successful acquire reads index 3 (hart 0's release) — every read entry of
    [lkg] at or above the insertion point shifts by one. *)

Definition swg : gexec :=
  GExec WeakLitmus.img0
        [[LRmw true false 0 [0%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl;
          LLoad false 8 [0%nat] [WeakLitmus.b0];
          LFence true true true true;
          LStore true 0 [WeakLitmus.b0] WCrel];
         [LRmw true false 0 [1%nat] [WeakLitmus.b1] [WeakLitmus.b1] WCexcl;
          LRmw true false 0 [3%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl;
          LStore false 8 [WeakLitmus.b1] WCplain;
          LFence true true true true;
          LStore true 0 [WeakLitmus.b0] WCrel]]
        [(0%nat, 0%nat); (1%nat, 0%nat); (0%nat, 1%nat); (0%nat, 3%nat);
         (1%nat, 1%nat); (1%nat, 2%nat); (1%nat, 4%nat)].

Local Notation ACQh := (0%nat, 0%nat).
Local Notation EVh  := (0%nat, 1%nat).
Local Notation RELh := (0%nat, 3%nat).
Local Notation SWP  := (1%nat, 0%nat).
Local Notation ACQj := (1%nat, 1%nat).
Local Notation EVj  := (1%nat, 2%nat).
Local Notation RELj := (1%nat, 4%nat).

(* ====================================================================== *)
(** * 2. Inversions and the position/index arithmetic *)

Lemma swg_nodup : NoDup (gx_gmo swg).
Proof.
  repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
Qed.

Lemma swg_gpos_of (n : nat) (e : geid) : gx_gmo swg !! n = Some e → gpos swg e = n.
Proof. apply gpos_of_lookup, swg_nodup. Qed.

Lemma swg_gwix_of (n : nat) (w : geid) :
  gwrites swg !! n = Some w → gwix swg w = S n.
Proof. apply gwix_of_lookup, swg_nodup. Qed.

Lemma swg_p00 : gpos swg ACQh = 0%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p10 : gpos swg SWP  = 1%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p01 : gpos swg EVh  = 2%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p03 : gpos swg RELh = 3%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p11 : gpos swg ACQj = 4%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p12 : gpos swg EVj  = 5%nat. Proof. by apply swg_gpos_of. Qed.
Lemma swg_p14 : gpos swg RELj = 6%nat. Proof. by apply swg_gpos_of. Qed.

Lemma swg_w00 : gwix swg ACQh = 1%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.
Lemma swg_w10 : gwix swg SWP  = 2%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.
Lemma swg_w03 : gwix swg RELh = 3%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.
Lemma swg_w11 : gwix swg ACQj = 4%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.
Lemma swg_w12 : gwix swg EVj  = 5%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.
Lemma swg_w14 : gwix swg RELj = 6%nat. Proof. by apply swg_gwix_of; vm_compute. Qed.

(** The seven memory events, and nothing else. *)
Lemma swg_mem_inv (e : geid) :
  gmem swg e →
  e = ACQh ∨ e = EVh ∨ e = RELh ∨ e = SWP ∨ e = ACQj ∨ e = EVj ∨ e = RELj.
Proof.
  intros (l & Hl & Hm). destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=; naive_solver.
Qed.

Lemma swg_gmo_mem (e : geid) : gmem swg e → e ∈ gx_gmo swg.
Proof.
  intros [->|[->|[->|[->|[->|[->| ->]]]]]]%swg_mem_inv;
    rewrite /gx_gmo /= !elem_of_cons; naive_solver.
Qed.

(** gmo IS per-hart program order, so every same-hart po-earlier memory event
    is gmo-earlier — this one lemma discharges [gppo_gmo] wholesale. *)
Lemma swg_gmo_po (e1 e2 : geid) :
  gmem swg e1 → gmem swg e2 → e1.1 = e2.1 → (e1.2 < e2.2)%nat →
  gmo_lt swg e1 e2.
Proof.
  intros Hm1 Hm2 Hag Hlt.
  split_and!; [by apply swg_gmo_mem|by apply swg_gmo_mem|].
  apply swg_mem_inv in Hm1. apply swg_mem_inv in Hm2.
  destruct Hm1 as [->|[->|[->|[->|[->|[->| ->]]]]]];
    destruct Hm2 as [->|[->|[->|[->|[->|[->| ->]]]]]];
    simpl in Hag, Hlt; try lia;
    rewrite ?swg_p00 ?swg_p01 ?swg_p03 ?swg_p10 ?swg_p11 ?swg_p12 ?swg_p14;
    lia.
Qed.

(** The write footprints. *)
Lemma swg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte swg e a v →
  (e = ACQh ∧ a = 0%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELh ∧ a = 0%Z ∧ v = WeakLitmus.b0) ∨
  (e = SWP  ∧ a = 0%Z ∧ v = WeakLitmus.b1) ∨
  (e = ACQj ∧ a = 0%Z ∧ v = WeakLitmus.b1) ∨
  (e = EVj  ∧ a = 8%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELj ∧ a = 0%Z ∧ v = WeakLitmus.b0).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

(** The read footprints.  THE HEART OF THE FINDING is the third arm: the
    failed swap's read entry at byte 0 names the value [b1], not [b0]. *)
Lemma swg_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte swg e a t v →
  (e = ACQh ∧ a = 0%Z ∧ t = 0%nat ∧ v = WeakLitmus.b0) ∨
  (e = EVh  ∧ a = 8%Z ∧ t = 0%nat ∧ v = WeakLitmus.b0) ∨
  (e = SWP  ∧ a = 0%Z ∧ t = 1%nat ∧ v = WeakLitmus.b1) ∨
  (e = ACQj ∧ a = 0%Z ∧ t = 3%nat ∧ v = WeakLitmus.b0).
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

Lemma swg_wr_lock (w : geid) (v : bv 8) :
  gwrites_byte swg w 0%Z v →
  (w = ACQh ∧ v = WeakLitmus.b1) ∨ (w = RELh ∧ v = WeakLitmus.b0) ∨
  (w = SWP  ∧ v = WeakLitmus.b1) ∨ (w = ACQj ∧ v = WeakLitmus.b1) ∨
  (w = RELj ∧ v = WeakLitmus.b0).
Proof.
  intros [(->&_&->)|[(->&_&->)|[(->&_&->)|[(->&_&->)|[(_&Hab&_)|(->&_&->)]]]]]%swg_wr;
    auto 10. discriminate Hab.
Qed.

Lemma swg_wr_data (w : geid) (v : bv 8) :
  gwrites_byte swg w 8%Z v → w = EVj ∧ v = WeakLitmus.b1.
Proof.
  intros [(_&Hab&_)|[(_&Hab&_)|[(_&Hab&_)|[(_&Hab&_)|[(->&_&->)|(_&Hab&_)]]]]]%swg_wr;
    by [discriminate Hab|].
Qed.

(* ====================================================================== *)
(** * 3. [swg] IS RVWMO⁻-CONSISTENT — the contended lock is a real execution *)

Theorem swg_consistent : rvwmo_minus_consistent swg.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + exact swg_nodup.
    + intros e. split.
      * intros He. rewrite /gx_gmo /= !elem_of_cons elem_of_nil in He.
        destruct He as [->|[->|[->|[->|[->|[->|[->|[]]]]]]]];
          eexists; split; reflexivity.
      * apply swg_gmo_mem.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=; done.
  - (* ppo⁻ ⊆ gmo *)
    intros e1 e2 Hppo.
    destruct (gppo_gmem swg e1 e2 Hppo) as [Hm1 Hm2].
    destruct (gppo_po_lt swg e1 e2 Hppo) as [Hag Hlt].
    by apply swg_gmo_po.
  - (* load value *)
    intros e a t v
      [(->&->&->&->)|[(->&->&->&->)|[(->&->&->&->)|(->&->&->&->)]]]%swg_rd.
    + (* ACQh reads the image: it is gmo- and po-first *)
      split; [exact WeakLitmus.img0_x|].
      intros w' v' Hw' Hvis.
      destruct Hvis as [(_ & _ & Hp)|(Hag & Hoff & _)];
        [|by destruct w' as [i k]; simpl in Hoff; lia].
      exfalso. rewrite swg_p00 in Hp. lia.
    + (* EVh reads the data byte's image value *)
      split; [exact WeakLitmus.img0_y|].
      intros w' v' [-> ->]%swg_wr_data Hvis.
      exfalso. destruct Hvis as [(_ & _ & Hp)|(Hag & _ & _)];
        [rewrite swg_p12 swg_p01 in Hp; lia|by simpl in Hag].
    + (* THE FAILED SWAP reads hart 0's acquire (write index 1) *)
      split.
      * exists ACQh. split_and!.
        { by vm_compute. }
        { by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0]
                          [WeakLitmus.b1] WCexcl), 0%Z, [WeakLitmus.b1], 0%nat. }
        { left. split_and!;
            [by apply swg_gmo_mem; by eexists
            |by apply swg_gmo_mem; by eexists
            |rewrite swg_p00 swg_p10; lia]. }
      * intros w' v'
          [[-> _]|[[-> _]|[[-> _]|[[-> _]|[-> _]]]]]%swg_wr_lock Hvis.
        { rewrite swg_w00. lia. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(Hag & _ & _)];
            [rewrite swg_p03 swg_p10 in Hp; lia|by simpl in Hag]. }
        { exfalso. destruct Hvis as [Hmo|(_ & Hoff & _)];
            [by eapply gmo_lt_irrefl|simpl in Hoff; lia]. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)];
            [rewrite swg_p11 swg_p10 in Hp; lia|simpl in Hoff; lia]. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)];
            [rewrite swg_p14 swg_p10 in Hp; lia|simpl in Hoff; lia]. }
    + (* ACQj reads the h-release, now at write index 3 *)
      split.
      * exists RELh. split_and!.
        { by vm_compute. }
        { by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z,
                    [WeakLitmus.b0], 0%nat. }
        { left. split_and!;
            [by apply swg_gmo_mem; by eexists
            |by apply swg_gmo_mem; by eexists
            |rewrite swg_p03 swg_p11; lia]. }
      * intros w' v'
          [[-> _]|[[-> _]|[[-> _]|[[-> _]|[-> _]]]]]%swg_wr_lock Hvis.
        { rewrite swg_w00. lia. }
        { rewrite swg_w03. lia. }
        { rewrite swg_w10. lia. }
        { exfalso. destruct Hvis as [Hmo|(_ & Hoff & _)];
            [by eapply gmo_lt_irrefl|simpl in Hoff; lia]. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)];
            [rewrite swg_p14 swg_p11 in Hp; lia|simpl in Hoff; lia]. }
  - (* atomicity: each RMW's read source is its immediate co-predecessor *)
    intros e a t v
      [(->&->&->&->)|[(->&->&->&->)|[(->&->&->&->)|(->&->&->&->)]]]%swg_rd
      Hw w' v' Hw' [Hlo Hhi].
    + rewrite swg_w00 in Hhi. lia.
    + destruct Hw as (l & Hl & Hlw). rewrite /gx_lbl /= in Hl. by simplify_eq.
    + rewrite swg_w10 in Hhi. lia.
    + rewrite swg_w11 in Hhi. lia.
Qed.

(* ====================================================================== *)
(** * 4. THE FINDING: [lock_pattern] IS FALSE ON [swg]

    The failed swap is a byte-0 write of [b1].  The release arm needs
    [b1 = lock_free]; the acquire arm needs a read entry of [swg] at [SWP],
    byte 0, valued [lock_free] — and [swg_rd] says that entry is valued
    [b1].  Both arms fail, so the pattern's second conjunct is refuted at a
    single witness write. *)

Lemma swg_swp_writes_one : gwrites_byte swg SWP 0%Z WeakLitmus.b1.
Proof.
  by exists (LRmw true false 0 [1%nat] [WeakLitmus.b1] [WeakLitmus.b1] WCexcl),
            0%Z, [WeakLitmus.b1], 0%nat.
Qed.

(** The failed swap reads NONZERO: no read entry of it at byte 0 is free. *)
Lemma swg_swp_reads_one (t : nat) : ¬ greads_byte swg SWP 0%Z t lock_free.
Proof.
  intros [(He&_)|[(He&_)|[(_&_&_&Hv)|(He&_)]]]%swg_rd;
    [by simplify_eq|by simplify_eq
    |by apply WeakLitmus.b0_ne_b1; exact Hv|by simplify_eq].
Qed.

Theorem swg_no_pattern : ¬ lock_pattern swg 0%Z.
Proof.
  intros [_ Hpat].
  destruct (Hpat SWP WeakLitmus.b1 swg_swp_writes_one)
    as [(_ & _ & (t & Ht))|Hz].
  - by eapply swg_swp_reads_one.
  - by apply WeakLitmus.b0_ne_b1.
Qed.

(** For the record: it is not that [SWP] fails to be an acquire in the
    LOOSE sense — [lock_acq] (a nonzero [b]-write) holds of it.  What fails
    is the pattern's demand that every such write have read [lock_free]. *)
Lemma swg_swp_lock_acq : lock_acq swg 0%Z SWP.
Proof.
  exists WeakLitmus.b1. split; [exact swg_swp_writes_one|].
  intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

(* ====================================================================== *)
(** * 5. THE GRAPH IS OTHERWISE PROTOCOL-CLEAN: [lock_paired] SURVIVES

    Both releases still close a critical section of their own hart.  Hart 1's
    section is unaffected by the spin because the failed swap is po-BEFORE
    hart 1's acquire, hence not co-between the acquire and the release. *)

Lemma swg_acq_h : lock_acq swg 0%Z ACQh.
Proof.
  exists WeakLitmus.b1. split.
  - by exists (LRmw true false 0 [0%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl),
              0%Z, [WeakLitmus.b1], 0%nat.
  - intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

Lemma swg_acq_j : lock_acq swg 0%Z ACQj.
Proof.
  exists WeakLitmus.b1. split.
  - by exists (LRmw true false 0 [3%nat] [WeakLitmus.b0] [WeakLitmus.b1] WCexcl),
              0%Z, [WeakLitmus.b1], 0%nat.
  - intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

Lemma swg_rel_h : lock_rel swg 0%Z RELh.
Proof.
  by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z, [WeakLitmus.b0], 0%nat.
Qed.

Lemma swg_rel_j : lock_rel swg 0%Z RELj.
Proof.
  by exists (LStore true 0 [WeakLitmus.b0] WCrel), 0%Z, [WeakLitmus.b0], 0%nat.
Qed.

Theorem swg_cs_h : lock_cs swg 0%Z ACQh RELh.
Proof.
  apply lock_cs_intro; [exact swg_consistent| | | |].
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact swg_acq_h.
  - exact swg_rel_h.
  - intros x v [[-> _]|[[-> _]|[[-> _]|[[-> _]|[-> _]]]]]%swg_wr_lock
      Hag Hlo Hhi; simpl in *; lia.
Qed.

Theorem swg_cs_j : lock_cs swg 0%Z ACQj RELj.
Proof.
  apply lock_cs_intro; [exact swg_consistent| | | |].
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact swg_acq_j.
  - exact swg_rel_j.
  - intros x v [[-> _]|[[-> _]|[[-> _]|[[-> _]|[-> _]]]]]%swg_wr_lock
      Hag Hlo Hhi; simpl in *; lia.
Qed.

Theorem swg_paired : lock_paired swg 0%Z.
Proof.
  intros R HR.
  destruct (swg_wr_lock R lock_free HR)
    as [[-> Hv]|[[-> _]|[[-> Hv]|[[-> Hv]|[-> _]]]]].
  - exfalso. by apply WeakLitmus.b0_ne_b1.
  - exists ACQh. exact swg_cs_h.
  - exfalso. by apply WeakLitmus.b0_ne_b1.
  - exfalso. by apply WeakLitmus.b0_ne_b1.
  - exists ACQj. exact swg_cs_j.
Qed.
