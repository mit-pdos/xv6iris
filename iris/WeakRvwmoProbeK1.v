(** * WeakRvwmoProbeK1.v — FINDING F1: [kill_K1] is STRONGER than the
    theorem needs.

    kill_K1's hypotheses hold at a graph that normalizes (source-descent
    resolves it: w0 below w, then e below w); the obligation as stated
    cannot be discharged for xv6 — see route-b §4d.1 F1.

    THE WITNESS [mpg]: the message-passing READER WITHOUT A FENCE, with
    an INDEPENDENT EARLY STORE on the reader's hart.

      hart 0:  e = (0,0)  LLoad  byte 0, ts = [2]  (reads hart 1's store)
               w = (0,1)  LStore byte 8            (the violating write)
      hart 1:  w0 = (1,0) LStore byte 0            (e's rf-source)

      gmo:     w  <  w0  <  e

    [w] is a rule-14 violation ([e] po-before [w], [w] gmo-before [e]); it
    is the gmo-MINIMAL such write (gmo position 0) and [e] is its po-MINIMAL
    witness (po position 0); [e] is a read; and its rf-source [w0] is
    CROSS-HART and sits gmo-strictly inside the descent interval [(w, e)].
    Those are EXACTLY [kill_K1]'s hypotheses, so [kill_K1 mpgd] is false
    ([mpgd_kill_K1_false]) — the same shape as [lbgd_kill_K1_false].

    THE POINT, and the difference from the LB witness: [mpg] nevertheless
    NORMALIZES.  The rows-equivalent graph [mpg'] — gmo [w0 < e < w],
    i.e. descend the SOURCE below [w] first and then the witness —
    satisfies [grule14] ([mpg'_rule14]) and is consistent
    ([mpg'_consistent]), and [gd_equiv] relates the two ([mpg_equiv]),
    with the write-index renaming the transposition [tswap 1].  So at this
    graph the normalization SUCCEEDS while [kill_K1] DEMANDS a refutation:
    the obligation as landed asks us to rule out a graph that has a
    perfectly good rule-14 form, and no kernel-level fact about xv6 could
    ever supply that.  (Contrast [lbg], where no rows-equivalent rule-14
    graph exists at all — there the kill is a real obligation.)

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoNorm.

(* ====================================================================== *)
(** * 1. The two graphs *)

(** [mpg]: gmo = [w; w0; e].  The read's [ts] entry names write index 2,
    i.e. the second write in gmo order, which is hart 1's store [w0]
    (index 1 is hart 0's store [w]; index 0 is the era-initial image). *)
Definition mpg : gexec :=
  GExec WeakLitmus.img0
        [[LLoad false 0 [2%nat] [WeakLitmus.b1];
          LStore false 8 [WeakLitmus.b1] WCplain];
         [LStore false 0 [WeakLitmus.b1] WCplain]]
        [(0%nat, 1%nat); (1%nat, 0%nat); (0%nat, 0%nat)].

Definition mpgd : gdexec := GDExec mpg [].

(** [mpg']: gmo = [w0; e; w].  The SAME rows with the read's [ts] entry
    renamed by [tswap 1] (2 ↦ 1): hart 1's store is now the FIRST write. *)
Definition mpg' : gexec :=
  GExec WeakLitmus.img0
        [[LLoad false 0 [1%nat] [WeakLitmus.b1];
          LStore false 8 [WeakLitmus.b1] WCplain];
         [LStore false 0 [WeakLitmus.b1] WCplain]]
        [(1%nat, 0%nat); (0%nat, 0%nat); (0%nat, 1%nat)].

Definition mpgd' : gdexec := GDExec mpg' [].

(* ====================================================================== *)
(** * 2. The byte footprints (the poloc refutation's engine, as for [lbg]) *)

Lemma mpg_acc (e : geid) (a : Z) :
  gaccesses mpg e a →
  (e = (0%nat, 0%nat) ∧ a = 0%Z) ∨ (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨
  (e = (1%nat, 0%nat) ∧ a = 0%Z).
Proof.
  intros [Hw|Hr].
  - destruct Hw as (v & l & b & vs & j & Hl & Hwr & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
  - destruct Hr as (t & v & l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
Qed.

Lemma mpg_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte mpg e a v →
  (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨ (e = (1%nat, 0%nat) ∧ a = 0%Z).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

Lemma mpg'_acc (e : geid) (a : Z) :
  gaccesses mpg' e a →
  (e = (0%nat, 0%nat) ∧ a = 0%Z) ∨ (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨
  (e = (1%nat, 0%nat) ∧ a = 0%Z).
Proof.
  intros [Hw|Hr].
  - destruct Hw as (v & l & b & vs & j & Hl & Hwr & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
  - destruct Hr as (t & v & l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=;
      rewrite /acc_addr /=; naive_solver.
Qed.

Lemma mpg'_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte mpg' e a v →
  (e = (0%nat, 1%nat) ∧ a = 8%Z) ∨ (e = (1%nat, 0%nat) ∧ a = 0%Z).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

(* ====================================================================== *)
(** * 3. (a) [mpg] is RVWMO⁻(+deps)-consistent *)

Theorem mpg_consistent : rvwmo_minus_consistent mpg.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. split.
      * intros He. rewrite !elem_of_cons elem_of_nil in He.
        destruct He as [-> |[-> |[-> | []]]]; eexists; split; reflexivity.
      * intros (l & Hl & Hm).
        destruct e as [i k]. rewrite /gx_lbl /= in Hl.
        destruct i as [|[|i]]; simpl in Hl; [| |done];
          destruct k as [|[|k]]; simplify_eq/=;
          rewrite !elem_of_cons; auto.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|k]]; simplify_eq/=; done.
  - (* ppo⁻ ⊆ gmo: there are NO ppo⁻ edges *)
    intros e1 e2 Hppo. exfalso.
    destruct Hppo as [Hpl|[Hf|[Ha|Hr]]].
    + destruct Hpl as ((Hag & Hlt & _ & _) & a & H1 & H2).
      destruct (mpg_acc e1 a H1) as [[He1 Ha1]|[[He1 Ha1]|[He1 Ha1]]];
        destruct (mpg_acc e2 a H2) as [[He2 Ha2]|[[He2 Ha2]|[He2 Ha2]]];
        subst e1; subst e2; simpl in Hag, Hlt; lia.
    + destruct Hf as (pr & pw & sr & sw & (Hag & Hlt & kf & Hk1 & Hk2 & Hlf)
                      & _ & _).
      destruct e1 as [i1 k1], e2 as [i2 k2]; simpl in *; subst i2.
      rewrite /gx_lbl /= in Hlf.
      destruct i1 as [|[|i1]]; simpl in Hlf; [| |done];
        destruct kf as [|[|kf]]; simplify_eq/=; lia.
    + destruct Ha as (Hpo & (l & Hl & Hr') & (l' & Hl' & Haq) & _).
      destruct e1 as [i1 k1]. rewrite Hl in Hl'. simplify_eq.
      rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
    + destruct Hr as (Hpo & _ & (l & Hl & Hrl) & _).
      destruct e1 as [i1 k1]. rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
  - (* load value: the ONE read, byte 0 at write index 2 = hart 1's store *)
    intros e a t v Hr.
    destruct Hr as (l & base & ts & vs & j & Hl & Hrd & Hj & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=.
    split.
    + eexists. split_and!; [done| |].
      * by exists (LStore false 0 [WeakLitmus.b1] WCplain), 0%Z,
          [WeakLitmus.b1], 0%nat.
      * left. rewrite /gmo_lt /gpos /=. split_and!;
          [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
          |vm_compute; lia].
    + intros w' v' Hw' Hvis.
      destruct (mpg_wr w' _ _ Hw') as [[-> Hab]|[-> _]];
        [exfalso; rewrite /acc_addr /= in Hab; lia|].
      by vm_compute.
  - (* atomicity: no event both reads and writes *)
    intros e a t v Hr (l & Hl & Hw).
    destruct Hr as (l' & base & ts & vs & j & Hl' & Hrd & _).
    rewrite Hl in Hl'. simplify_eq.
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=; done.
Qed.

Theorem mpg_deps_consistent : rvwmo_minus_deps_consistent mpgd.
Proof.
  split_and!; [exact mpg_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(* ====================================================================== *)
(** * 4. (b) [kill_K1] is FALSE at [mpg] — its hypotheses all hold *)

Theorem mpgd_kill_K1_false : ¬ kill_K1 mpgd.
Proof.
  intros HK.
  apply (HK mpgd (gd_equiv_refl mpgd mpg_deps_consistent)
            (0%nat, 1%nat) (0%nat, 0%nat) 0%Z 2%nat WeakLitmus.b1
            (1%nat, 0%nat)).
  - (* the violation: e po-before w, w gmo-before e *)
    split_and!.
    + split_and!; [done|simpl; lia|by eexists|by eexists].
    + eexists. split; reflexivity.
    + eexists. split; reflexivity.
    + split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                  |vm_compute; lia].
  - (* [(0,1)] is gmo-minimal: it sits at gmo position 0 *)
    intros e' w' _ (_ & _ & Hlt). revert Hlt. vm_compute. lia.
  - (* [(0,0)] is po-minimal: it sits at po position 0 *)
    intros e' _ Hlt. simpl in Hlt. lia.
  - (* the witness is a read *)
    reflexivity.
  - (* it reads byte 0 at write index 2 *)
    exists (LLoad false 0 [2%nat] [WeakLitmus.b1]), 0%Z, [2%nat],
           [WeakLitmus.b1], 0%nat. split_and!; reflexivity.
  - (* write index 2 is hart 1's store *)
    by vm_compute.
  - (* which is CROSS-HART *)
    by simpl.
  - (* and sits gmo-above the violating write ... *)
    split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                |vm_compute; lia].
  - (* ... and gmo-below the witness *)
    split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                |vm_compute; lia].
Qed.

(* ====================================================================== *)
(** * 5. (c) THE POINT: [mpg] HAS a rows-equivalent rule-14 graph *)

Theorem mpg'_consistent : rvwmo_minus_consistent mpg'.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. split.
      * intros He. rewrite !elem_of_cons elem_of_nil in He.
        destruct He as [-> |[-> |[-> | []]]]; eexists; split; reflexivity.
      * intros (l & Hl & Hm).
        destruct e as [i k]. rewrite /gx_lbl /= in Hl.
        destruct i as [|[|i]]; simpl in Hl; [| |done];
          destruct k as [|[|k]]; simplify_eq/=;
          rewrite !elem_of_cons; auto.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|k]]; simplify_eq/=; done.
  - intros e1 e2 Hppo. exfalso.
    destruct Hppo as [Hpl|[Hf|[Ha|Hr]]].
    + destruct Hpl as ((Hag & Hlt & _ & _) & a & H1 & H2).
      destruct (mpg'_acc e1 a H1) as [[He1 Ha1]|[[He1 Ha1]|[He1 Ha1]]];
        destruct (mpg'_acc e2 a H2) as [[He2 Ha2]|[[He2 Ha2]|[He2 Ha2]]];
        subst e1; subst e2; simpl in Hag, Hlt; lia.
    + destruct Hf as (pr & pw & sr & sw & (Hag & Hlt & kf & Hk1 & Hk2 & Hlf)
                      & _ & _).
      destruct e1 as [i1 k1], e2 as [i2 k2]; simpl in *; subst i2.
      rewrite /gx_lbl /= in Hlf.
      destruct i1 as [|[|i1]]; simpl in Hlf; [| |done];
        destruct kf as [|[|kf]]; simplify_eq/=; lia.
    + destruct Ha as (Hpo & (l & Hl & Hr') & (l' & Hl' & Haq) & _).
      destruct e1 as [i1 k1]. rewrite Hl in Hl'. simplify_eq.
      rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
    + destruct Hr as (Hpo & _ & (l & Hl & Hrl) & _).
      destruct e1 as [i1 k1]. rewrite /gx_lbl /= in Hl.
      destruct i1 as [|[|i1]]; simpl in Hl; [| |done];
        destruct k1 as [|[|k1]]; simplify_eq/=; done.
  - (* load value: byte 0 at write index 1 = hart 1's store, now FIRST *)
    intros e a t v Hr.
    destruct Hr as (l & base & ts & vs & j & Hl & Hrd & Hj & Hv & Ha).
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=;
      destruct j as [|j]; simplify_eq/=.
    split.
    + eexists. split_and!; [done| |].
      * by exists (LStore false 0 [WeakLitmus.b1] WCplain), 0%Z,
          [WeakLitmus.b1], 0%nat.
      * left. rewrite /gmo_lt /gpos /=. split_and!;
          [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
          |vm_compute; lia].
    + intros w' v' Hw' Hvis.
      destruct (mpg'_wr w' _ _ Hw') as [[-> Hab]|[-> _]];
        [exfalso; rewrite /acc_addr /= in Hab; lia|].
      by vm_compute.
  - intros e a t v Hr (l & Hl & Hw).
    destruct Hr as (l' & base & ts & vs & j & Hl' & Hrd & _).
    rewrite Hl in Hl'. simplify_eq.
    destruct e as [i k]. rewrite /gx_lbl /= in Hl.
    destruct i as [|[|i]]; simpl in Hl; [| |done];
      destruct k as [|[|k]]; simplify_eq/=; done.
Qed.

Theorem mpg'_deps_consistent : rvwmo_minus_deps_consistent mpgd'.
Proof.
  split_and!; [exact mpg'_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(** RULE 14 holds in [mpg']: the only po pair is [e < w], and [e] is now
    gmo-below [w]. *)
Theorem mpg'_rule14 : grule14 mpg'.
Proof.
  intros e w Hpo Hme Hw.
  destruct Hpo as (Hag & Hlt & (le & Hle) & (lw & Hlw)).
  destruct e as [ie ke], w as [iw kw]; simpl in Hag, Hlt; subst iw.
  rewrite /gx_lbl /= in Hle Hlw.
  destruct ie as [|[|ie]]; simpl in Hle, Hlw; [| |done];
    destruct ke as [|[|ke]]; simpl in Hle; try done;
    destruct kw as [|[|kw]]; simpl in Hlw; try done; try lia.
  (* the ONE surviving pair: hart 0's load [e] po-before hart 0's store [w] *)
  split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
              |vm_compute; lia].
Qed.

(** ** 5.1 The rows correspondence: [tswap 1] renames write index 2 to 1 *)

Lemma mpg_rows_rel : rows_rel (tswap 1) mpg mpg'.
Proof.
  split_and!; [reflexivity| |].
  - reflexivity.
  - reflexivity.
Qed.

Lemma mpg_gwrites : gwrites mpg = [(0%nat, 1%nat); (1%nat, 0%nat)].
Proof. by vm_compute. Qed.

Lemma mpg'_gwrites : gwrites mpg' = [(1%nat, 0%nat); (0%nat, 1%nat)].
Proof. by vm_compute. Qed.

Lemma mpg_wperm : wperm (tswap 1) mpg mpg'.
Proof.
  split_and!.
  - apply tswap_inj.
  - intros t. destruct t as [|[|[|t]]].
    + reflexivity.
    + by vm_compute.
    + by vm_compute.
    + assert (Ht : tswap 1 (S (S (S t))) = S (S (S t)))
        by (rewrite /tswap /sidx; repeat case_bool_decide; lia).
      rewrite Ht /gwrite_at mpg_gwrites mpg'_gwrites. done.
  - by rewrite mpg_gwrites mpg'_gwrites.
Qed.

(** THE STATEMENT OF THE FINDING: the two graphs are [gd_equiv], and the
    second satisfies rule 14 — so [mpg] normalizes, yet [kill_K1] demands
    that its configuration be impossible. *)
Theorem mpg_equiv : gd_equiv mpgd mpgd'.
Proof.
  exists (tswap 1). split_and!.
  - exact mpg_rows_rel.
  - exact mpg_wperm.
  - reflexivity.
  - exact mpg'_deps_consistent.
Qed.

Theorem mpg_normalizes :
  ∃ GD', gd_equiv mpgd GD' ∧ grule14 (gd_g GD').
Proof. exists mpgd'. split; [exact mpg_equiv|exact mpg'_rule14]. Qed.
