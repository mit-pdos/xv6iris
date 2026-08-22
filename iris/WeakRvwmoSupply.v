(** * WeakRvwmoSupply.v — B1b-1: THE SUPPLY DERIVATION UNDER FABRIC QUIESCENCE

    Design: [claude-notes/design/weak-memory-route-b.md] §4b (B1b's shape)
    and §4d.4's **B1b — DESIGNED** entry (the staging: B1b-1 = fabric
    quiescence, B1b-2 = the fabric order as bundle data).

    THE GAP THIS CLOSES.  [WeakRvwmoConf.gdexec_conf] says every hart's ROW
    is emittable, one [adm_run]-then-realizing-step block per row event, at
    the hart's OWN row-position-indexed fabric.  [WeakAxRealize.exec_prog_ok']
    — the hypothesis T1 ([WeakSrvwmoCapstone.xv6_srvwmo_safe]) consumes —
    wants the same blocks indexed by GLOBAL TRACE POSITION, with ONE program
    state list per position and ONE global fabric.  B1b is the interleaving
    that turns the former into the latter.

    ** WHY QUIESCENCE IS A REAL MILESTONE AND NOT A CHEAT

    MMIO accesses are NOT memory events: [WeakEvInst]'s node emits the
    administrative label [LDev] for any [dev_addr] access, and
    [proj_lbl _ LDev = None], so no graph row carries a fabric access at
    all.  The fabric therefore moves ONLY inside the administrative stars,
    and a global [dv] for an interleaving of per-hart emissions exists iff
    the per-hart fabric sequences CHAIN across the trace.  Under QUIESCENCE
    — no [LDev] in any emission ([em_devfree]) — that chaining is vacuous:
    [WeakEvInst.pdev_ev_ok] makes every step fabric-PRESERVING and
    fabric-BLIND, so every hart's fabric sequence is constant and the global
    [dv := λ _, d0] threads through ANY interleaving.  What is NOT covered
    is an execution whose harts genuinely touch the fabric; that is B1b-2
    (the fabric order as bundle data), and nothing here is retracted by it.

    ** WHAT IS HERE

    (1) §2 — FABRIC BLINDNESS of a devfree emission: [adm_run_devfree] /
        [hemit_devfree_const] (the fabric is constant across the block
        range) and [hemit_devfree_refab] / [hemit_devfree_reindex] (the
        emission replays at any other fabric assignment constant on that
        range).  A STATEMENT CORRECTION is recorded at
        [hemit_devfree_reindex]: [dv' k = dv k] alone is NOT enough.

    (2) §3 — [em_devfree] and [gdexec_qconf], the quiescent conformance
        bundle, plus [gdexec_qconf_hull] (a hull of a quiescent-conformant
        graph is quiescent-conformant) and [gdexec_qconf_ren] (the
        [rows_rel] transport, mirroring [gdexec_conf_ren]).

    (3) §4 — [hblock] / [hemit_states]: the per-hart emission's INTERMEDIATE
        PROGRAM STATES, extracted from the (Prop-valued) [hemit] derivation
        as an honest function [nat → pexv6].  The existential is built BY
        THE INDUCTION, so no choice principle is used.

    (4) §5 — the per-agent wstate bridge [cand_ws_relp]: the release-pending
        bit of the candidate's axiomatic per-agent wstate at trace position
        [k] equals that of [row_ws (rows i) n], [n] = the number of [i]'s
        events strictly before [k].  This is the ONLY thing the projection
        equation reads of the state ([WeakRvwmoConf]'s §1/§3.1), which is
        what makes the per-hart fold usable at a global trace position.

    (5) §6 — THE INTERLEAVING THEOREM [supply_of_qconf], and §7 the
        composition [hull_supply] (+ [topo_supply], the acyclicity route). *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
(* AFTER the axiomatic band, exactly as [WeakRvwmoConf] does it: the WLABEL
   constructors are the unqualified ones here. *)
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. LIST PRELIMINARIES

    All four are about the interaction of [filter]/[take] on the trace with
    the per-agent row it induces.  [Stdlib.Lists.List] shadows several stdpp
    list names in this import context (durable notes), so the stdpp ones are
    written qualified where they collide. *)

Lemma eadm_fst (ls : list wlabel) : (eadm ls).*1 = ls.
Proof.
  rewrite /eadm -list_fmap_compose. rewrite -{2}(list_fmap_id ls).
  apply list_fmap_ext. by intros i l _.
Qed.

(** The label sequence of ONE emission block. *)
Lemma eblock_fst ls l k es :
  (eadm ls ++ (l, Some k) :: es).*1 = ls ++ l :: es.*1.
Proof. by rewrite fmap_app fmap_cons eadm_fst. Qed.

Lemma not_elem_of_block {A} (x : A) (ls : list A) (l : A) (es : list A) :
  x ∉ ls ++ l :: es → x ∉ ls ∧ l ≠ x ∧ x ∉ es.
Proof.
  intros H. split_and!.
  - intros Hin. apply H, elem_of_app. by left.
  - intros ->. apply H, elem_of_app. right. apply elem_of_list_here.
  - intros Hin. apply H, elem_of_app. right. by apply elem_of_list_further.
Qed.

(** A FINITE choice principle, proved by induction — the range is bounded, so
    no axiom is involved.  Needed because the conformance bundle hands back
    an emission per agent under an existential. *)
Lemma nat_bounded_choice {A} (a0 : A) (P : nat → A → Prop) (N : nat) :
  (∀ i, (i < N)%nat → ∃ a, P i a) →
  ∃ F : nat → A, ∀ i, (i < N)%nat → P i (F i).
Proof.
  induction N as [|N IH]; intros H.
  - exists (λ _, a0). intros i Hi. lia.
  - destruct IH as (F & HF); [intros i Hi; apply H; lia|].
    destruct (H N ltac:(lia)) as (a & Ha).
    exists (λ i, if bool_decide (i = N) then a else F i).
    intros i Hi. case_bool_decide as Hc; [by subst i|apply HF; lia].
Qed.

(** The pointwise-lookup rebuild of a list. *)
Lemma fmap_seq_default {A} (x : A) (l : list A) :
  (λ i, default x (l !! i)) <$> seq 0 (length l) = l.
Proof.
  apply list_eq. intros j. rewrite list_lookup_fmap.
  destruct (decide (j < length l)%nat) as [Hj|Hj].
  - rewrite lookup_seq_lt //=.
    by destruct (lookup_lt_is_Some_2 l j Hj) as [a ->].
  - rewrite lookup_seq_ge; [|lia].
    symmetry. apply lookup_ge_None_2. lia.
Qed.

(* ====================================================================== *)
(** * 2. FABRIC BLINDNESS OF A [LDev]-FREE EMISSION

    [WeakEvInst.pdev_ev] is a function of the LABEL alone ([LDev] ↦ [true],
    everything else ↦ [false]), and [WeakEvInst.pdev_ev_ok] then says a
    non-[LDev] step is fabric-PRESERVING ([d' = d]) and fabric-BLIND
    ([∀ d0, pstep_ev p d0 l p' d0]).  Both halves are used below. *)

Lemma pdev_ev_false p l p' : l ≠ LDev → pdev_ev p l p' = false.
Proof. by destruct l. Qed.

Lemma pstep_ev_devfree p d l p' d' :
  pstep_ev p d l p' d' → l ≠ LDev →
  d' = d ∧ ∀ d0, pstep_ev p d0 l p' d0.
Proof.
  intros Hs Hne. by apply (pdev_ev_ok p d l p' d' Hs (pdev_ev_false p l p' Hne)).
Qed.

(** ** 2.1 The administrative run *)

Lemma adm_run_devfree instr p d ls p' d' :
  adm_run instr p d ls p' d' → LDev ∉ ls → d' = d.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH]; intros Hnd; [done|].
  have Hne : l ≠ LDev by (intros ->; apply Hnd, elem_of_list_here).
  destruct (pstep_ev_devfree _ _ _ _ _ Hs Hne) as [-> _].
  apply IH. intros Hin. apply Hnd. by apply elem_of_list_further.
Qed.

Lemma adm_run_refab instr p d ls p' d' :
  adm_run instr p d ls p' d' → LDev ∉ ls →
  ∀ d0, adm_run instr p d0 ls p' d0.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ IH]; intros Hnd d0;
    [apply ARnil|].
  have Hne : l ≠ LDev by (intros ->; apply Hnd, elem_of_list_here).
  have Hrest : LDev ∉ ls by (intros Hin; apply Hnd, elem_of_list_further).
  destruct (pstep_ev_devfree _ _ _ _ _ Hs Hne) as [-> Hall].
  eapply ARcons; [exact Ha|apply Hall|by apply IH].
Qed.

(** ** 2.2 The emission

    [hemit]'s fabric parameter [dv] is indexed by ROW POSITION (scope note
    (S-d) of [WeakRvwmoConf]): [dv k] is where the [k]-th row event's
    administrative run starts, [dv (S k)] where its realizing step ends. *)

Lemma hemit_devfree_const dv k ws row p es pfin :
  hemit dv k ws row p es pfin → LDev ∉ es.*1 →
  ∀ j, (k ≤ j)%nat → (j ≤ k + length row)%nat → dv j = dv k.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros Hnd j Hlo Hhi.
  - simpl in Hhi. assert (j = k) by lia. by subst j.
  - rewrite !eblock_fst in Hnd.
    destruct (not_elem_of_block _ _ _ _ Hnd) as (Hne1 & Hnel & Hrest).
    have Hda : da = dv k by (eapply adm_run_devfree; [exact Har|exact Hne1]).
    destruct (pstep_ev_devfree _ _ _ _ _ Hst Hnel) as [Hd _].
    have Hsk : dv (S k) = dv k by rewrite Hd Hda.
    destruct (decide (j = k)) as [->|Hjk]; [done|].
    rewrite (IH Hrest j ltac:(lia) ltac:(simpl in Hhi; lia)) //.
  - rewrite !eblock_fst in Hnd.
    destruct (not_elem_of_block _ _ _ _ Hnd) as (Hne1 & Hnel1 & Hnd2).
    destruct (not_elem_of_block _ _ _ _ Hnd2) as (Hne2 & Hnel2 & Hrest).
    have Hda : da = dv k by (eapply adm_run_devfree; [exact Har1|exact Hne1]).
    destruct (pstep_ev_devfree _ _ _ _ _ Hst1 Hnel1) as [Hd1 _].
    have Hdm2 : dm2 = dm by (eapply adm_run_devfree; [exact Har2|exact Hne2]).
    destruct (pstep_ev_devfree _ _ _ _ _ Hst2 Hnel2) as [Hd2 _].
    have Hsk : dv (S k) = dv k by rewrite Hd2 Hdm2 Hd1 Hda.
    destruct (decide (j = k)) as [->|Hjk]; [done|].
    rewrite (IH Hrest j ltac:(lia) ltac:(simpl in Hhi; lia)) //.
Qed.

(** THE REFABRICATION.  *** STATEMENT CORRECTION (recorded): the form asked
    for in the B1b-1 brief — [∀ dv', dv' k = dv k → hemit dv' k …] — is
    FALSE.  A devfree block is fabric-PRESERVING, so its realizing step ends
    at the fabric its administrative run started from; [hemit dv' …] then
    forces [dv' (S k) = dv' k], which [dv' k = dv k] does not supply.  What
    is true (and what B1b-1 needs) is: the emission replays at ANY fabric
    assignment that is CONSTANT on the block's index range.  The [λ _, d0]
    specialization below is the form [gdexec_qconf] consumes; note it needs
    no relation to [dv] at all — that is FULL fabric blindness. *)
Lemma hemit_devfree_refab dv k ws row p es pfin :
  hemit dv k ws row p es pfin → LDev ∉ es.*1 →
  ∀ (dv' : nat → dev_state) (d0 : dev_state),
    (∀ j, (k ≤ j)%nat → (j ≤ k + length row)%nat → dv' j = d0) →
    hemit dv' k ws row p es pfin.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros Hnd dv' d0 Hc.
  - apply HEnil.
  - rewrite !eblock_fst in Hnd.
    destruct (not_elem_of_block _ _ _ _ Hnd) as (Hne1 & Hnel & Hrest).
    destruct (pstep_ev_devfree _ _ _ _ _ Hst Hnel) as [_ Hall].
    eapply HEone.
    + rewrite (Hc k ltac:(lia) ltac:(simpl; lia)).
      eapply adm_run_refab; [exact Har|exact Hne1].
    + exact Hre.
    + rewrite (Hc (S k) ltac:(lia) ltac:(simpl; lia)). apply Hall.
    + apply (IH Hrest dv' d0). intros j Hlo Hhi.
      apply Hc; [lia|simpl; lia].
  - rewrite !eblock_fst in Hnd.
    destruct (not_elem_of_block _ _ _ _ Hnd) as (Hne1 & Hnel1 & Hnd2).
    destruct (not_elem_of_block _ _ _ _ Hnd2) as (Hne2 & Hnel2 & Hrest).
    destruct (pstep_ev_devfree _ _ _ _ _ Hst1 Hnel1) as [_ Hall1].
    destruct (pstep_ev_devfree _ _ _ _ _ Hst2 Hnel2) as [_ Hall2].
    eapply HEpair.
    + rewrite (Hc k ltac:(lia) ltac:(simpl; lia)).
      eapply adm_run_refab; [exact Har1|exact Hne1].
    + exact Hre.
    + apply Hall1.
    + eapply adm_run_refab; [exact Har2|exact Hne2].
    + rewrite (Hc (S k) ltac:(lia) ltac:(simpl; lia)). apply Hall2.
    + apply (IH Hrest dv' d0). intros j Hlo Hhi.
      apply Hc; [lia|simpl; lia].
Qed.

Lemma hemit_devfree_reindex dv k ws row p es pfin :
  hemit dv k ws row p es pfin → LDev ∉ es.*1 →
  ∀ d0 : dev_state, hemit (λ _, d0) k ws row p es pfin.
Proof.
  intros Hem Hnd d0. by eapply (hemit_devfree_refab _ _ _ _ _ _ _ Hem Hnd _ d0).
Qed.

(* ====================================================================== *)
(** * 3. THE QUIESCENT CONFORMANCE BUNDLE

    [WeakRvwmoConf.gdexec_conf] with the per-hart fabric pinned to a
    CONSTANT [λ _, d0] and the emission required [LDev]-free.  §2 is what
    makes the pinning free: a devfree emission at ANY fabric assignment is
    an emission at every constant one ([hemit_devfree_reindex]). *)

Definition em_devfree (em : hemission) : Prop := LDev ∉ em_labels em.

Definition gdexec_qconf (boot : agent → pexv6) (d0 : dev_state)
    (GD : gdexec) : Prop :=
  ∀ i row, gx_prog (gd_g GD) !! i = Some row →
    ∃ em, hart_conf i row (boot i) (λ _, d0) em ∧
          em_devfree em ∧
          (∀ jk, jk ∈ row_deps (em_items em) →
                 ((i, jk.1), (i, jk.2)) ∈ gd_deps GD).

(** The bundle IS a [gdexec_conf] bundle — the milestone is a
    SPECIALIZATION, not a different interface. *)
Lemma gdexec_qconf_conf boot d0 GD :
  gdexec_qconf boot d0 GD → gdexec_conf boot (λ _ _, d0) GD.
Proof.
  intros H i row Hrow. destruct (H i row Hrow) as (em & Hem & _ & Hdep).
  by exists em.
Qed.

(** ** 3.1 [em_devfree] is stable under the two emission operations *)

(** [wlbl_ren] never MANUFACTURES an [LDev]: it is the identity on every
    constructor but the three read-carrying ones, and those it maps to
    themselves. *)
Lemma wlbl_ren_dev π l : wlbl_ren π l = LDev → l = LDev.
Proof. by destruct l. Qed.

Lemma em_devfree_ren π em : em_devfree em → em_devfree (em_ren π em).
Proof.
  rewrite /em_devfree em_labels_ren. intros H Hin.
  apply elem_of_list_fmap in Hin as (l & Heq & Hl).
  apply H. by rewrite (wlbl_ren_dev π l (eq_sym Heq)) in Hl.
Qed.

Lemma em_devfree_prefix em em' :
  em_items em' `prefix_of` em_items em → em_devfree em → em_devfree em'.
Proof.
  rewrite /em_devfree /em_labels. intros [t ->] H Hin.
  apply H. rewrite fmap_app elem_of_app. by left.
Qed.

(** ** 3.2 [row_deps] of a prefix of the ITEM list

    NOTE the index subtlety (the brief's warning): the prefix here is over
    ITEMS, not over ROW POSITIONS — that is exactly the shape
    [WeakRvwmoConf.hemit_prefix] hands back, and it is the right one, since
    [row_deps]' fold is over items and the row positions are carried IN the
    items. *)
Lemma row_deps_aux_app s es1 es2 jk :
  jk ∈ row_deps_aux s es1 → jk ∈ row_deps_aux s (es1 ++ es2).
Proof.
  revert s. induction es1 as [|it es1 IH]; intros s Hjk; simpl in Hjk.
  { by apply elem_of_nil in Hjk. }
  simpl. apply elem_of_app in Hjk as [Hjk|Hjk]; apply elem_of_app.
  - by left.
  - right. by apply IH.
Qed.

Lemma row_deps_prefix es1 es2 jk :
  es1 `prefix_of` es2 → jk ∈ row_deps es1 → jk ∈ row_deps es2.
Proof. intros [t ->] Hjk. by apply row_deps_aux_app. Qed.

(** ** 3.3 THE HULL TRANSPORT

    [WeakRvwmoHull]'s rows are CUT-then-RENAMED, so the seam is
    [hart_conf_prefix] followed by [hart_conf_ren] — exactly as
    [hull_rows_rel] advertises.  The dep clause lands in the hull's FILTERED
    dep set because a [row_deps] edge of an emission of [take c p] names row
    positions BELOW [c] on both ends ([hart_conf_row_deps_wf]), which is
    [gcut]'s clause. *)
Theorem gdexec_qconf_hull boot d0 GD cs :
  gdexec_qconf boot d0 GD → gdexec_qconf boot d0 (gd_hull GD cs).
Proof.
  intros Hq i row' Hrow'.
  rewrite /gd_hull /= gxh_prog_lookup in Hrow'.
  destruct (cs !! i) as [c|] eqn:Hc; [|done]. simpl in Hrow'.
  destruct (gx_prog (gd_g GD) !! i) as [p|] eqn:Hp; [|done]. simpl in Hrow'.
  injection Hrow' as <-.
  destruct (Hq i p Hp) as (em & Hem & Hdf & Hdep).
  destruct (hart_conf_prefix i p (boot i) (λ _, d0) em c Hem)
    as (em' & Hem' & Hpre).
  exists (em_ren (hren (gd_g GD) cs) em'). split_and!.
  - by apply hart_conf_ren.
  - by apply em_devfree_ren, (em_devfree_prefix em em').
  - intros jk Hjk.
    rewrite /em_ren /= row_deps_ren in Hjk.
    destruct (hart_conf_row_deps_wf i (take c p) (boot i) (λ _, d0) em' jk
                Hem' Hjk) as (_ & (lb1 & Hl1 & _) & (lb2 & Hl2 & _)).
    have Hlt1 : (jk.1 < c)%nat.
    { pose proof (lookup_lt_Some _ _ _ Hl1) as H.
      rewrite length_take in H. lia. }
    have Hlt2 : (jk.2 < c)%nat.
    { pose proof (lookup_lt_Some _ _ _ Hl2) as H.
      rewrite length_take in H. lia. }
    apply gd_hull_deps. split_and!.
    + apply Hdep. by eapply row_deps_prefix.
    + by eapply gcut_intro.
    + by eapply gcut_intro.
Qed.

(** ** 3.4 THE ORBIT TRANSPORT, mirroring [gdexec_conf_ren] *)
Lemma gdexec_qconf_ren π boot d0 GD GD' :
  rows_rel π (gd_g GD) (gd_g GD') →
  gd_deps GD' = gd_deps GD →
  gdexec_qconf boot d0 GD → gdexec_qconf boot d0 GD'.
Proof.
  intros Hrr Hdeps Hq i row' Hrow'.
  destruct Hrr as (_ & Hprog & _).
  rewrite Hprog list_lookup_fmap in Hrow'.
  apply fmap_Some in Hrow' as (row & Hrow & ->).
  destruct (Hq i row Hrow) as (em & Hem & Hdf & Hdep).
  exists (em_ren π em). split_and!.
  - by apply hart_conf_ren.
  - by apply em_devfree_ren.
  - intros jk Hjk. rewrite Hdeps. apply Hdep.
    by rewrite /em_ren /= row_deps_ren in Hjk.
Qed.

(* ====================================================================== *)
(** * 4. THE EMISSION'S INTERMEDIATE PROGRAM STATES

    [hemit] is a Prop-valued inductive, so its intermediate [pexv6] states
    cannot be read off by a recursor.  [hemit_states] extracts them as an
    honest function anyway: the existential witness is BUILT BY THE
    INDUCTION (the tail's function, extended at 0), so no choice principle
    is involved. *)

Definition hblock (dv : nat → dev_state) (k : nat) (ws : wstate)
    (lb : lbl) (p p' : pexv6) : Prop :=
  ∃ pa da,
    adm_star pstep_ev true p (dv k) pa da ∧
    ((∃ l, hlbl_realizes pa ws lb l ∧ pstep_ev pa da l p' (dv (S k)))
     ∨ (∃ pm dm pm2 dm2 l1 l2,
          hlbl_realizes_pair pa pm2 ws lb l1 l2 ∧
          pstep_ev pa da l1 pm dm ∧
          adm_star pstep_ev false pm dm pm2 dm2 ∧
          pstep_ev pm2 dm2 l2 p' (dv (S k)))).

Lemma hemit_states dv k ws row p es pfin :
  hemit dv k ws row p es pfin →
  ∃ f : nat → pexv6, f 0%nat = p ∧
    ∀ n lb, row !! n = Some lb →
      hblock dv (n + k) (row_ws_aux k ws (take n row)) lb (f n) (f (S n)).
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH].
  - exists (λ _, p). split; [done|]. intros n lb Hn. by rewrite lookup_nil in Hn.
  - destruct IH as (f' & Hf0 & Hf).
    exists (λ n, match n with 0%nat => p | S n' => f' n' end).
    split; [done|]. intros n lb0 Hn. destruct n as [|n]; simpl in Hn |- *.
    + injection Hn as <-. rewrite Hf0. exists pa, da.
      split; [exact (adm_run_star _ _ _ _ _ _ Har)|]. left. by exists l.
    + rewrite -Nat.add_succ_r. by apply Hf.
  - destruct IH as (f' & Hf0 & Hf).
    exists (λ n, match n with 0%nat => p | S n' => f' n' end).
    split; [done|]. intros n lb0 Hn. destruct n as [|n]; simpl in Hn |- *.
    + injection Hn as <-. rewrite Hf0. exists pa, da.
      split; [exact (adm_run_star _ _ _ _ _ _ Har1)|]. right.
      exists pm, dm, pm2, dm2, l1, l2.
      split_and!;
        [done|done|exact (adm_run_star _ _ _ _ _ _ Har2)|done].
    + rewrite -Nat.add_succ_r. by apply Hf.
Qed.

Lemma hart_conf_states i row p0 dv em :
  hart_conf i row p0 dv em →
  ∃ f : nat → pexv6, f 0%nat = p0 ∧
    ∀ n lb, row !! n = Some lb → hblock dv n (row_ws row n) lb (f n) (f (S n)).
Proof.
  intros Hem. destruct (hemit_states _ _ _ _ _ _ _ Hem) as (f & Hf0 & Hf).
  exists f. split; [done|]. intros n lb Hn.
  specialize (Hf n lb Hn). rewrite Nat.add_0_r in Hf.
  rewrite /row_ws. exact Hf.
Qed.

(* ====================================================================== *)
(** * 5. THE PER-AGENT WSTATE, AT A GLOBAL TRACE POSITION

    The projection equation reads the axiomatic state ONLY through
    [w_relp (ms_ws σ i)] ([WeakRvwmoConf]'s §1: [pcls_ev_relp]), and
    [w_relp] of the per-hart fold is a fold of the ROW'S OWN LABELS and
    nothing else ([row_ws_relp]).  This section closes the loop: the
    candidate's per-agent [w_relp] at trace position [k] IS the row fold at
    the number of [i]'s events strictly below [k]. *)

Definition trow (i : agent) (tr : list estep) : list lbl :=
  (λ s, es_lb s) <$> filter (λ s, es_ag s = i) tr.

Definition tcnt (i : agent) (tr : list estep) : nat :=
  length (filter (λ s, es_ag s = i) tr).

Lemma filter_take_prefix (P : estep → Prop) `{∀ s, Decision (P s)} tr n :
  filter P (take n tr) `prefix_of` filter P tr.
Proof.
  exists (filter P (drop n tr)).
  by rewrite -list_basics.filter_app take_drop.
Qed.

(** The [k]-th trace step of agent [i] is the [tcnt]-th element of [i]'s
    row. *)
Lemma trow_at i tr k s :
  tr !! k = Some s → es_ag s = i →
  trow i tr !! tcnt i (take k tr) = Some (es_lb s).
Proof.
  intros Hk Hag.
  have Hstep : filter (λ s0, es_ag s0 = i) (take (S k) tr)
             = filter (λ s0, es_ag s0 = i) (take k tr) ++ [s].
  { rewrite (take_S_r tr k s Hk) list_basics.filter_app
      (filter_cons_True _ s [] Hag) filter_nil //. }
  destruct (filter_take_prefix (λ s0, es_ag s0 = i) tr (S k)) as [t Ht].
  rewrite /trow list_lookup_fmap /tcnt.
  have Hlk : filter (λ s0, es_ag s0 = i) tr !! length
               (filter (λ s0, es_ag s0 = i) (take k tr)) = Some s.
  { rewrite Ht Hstep -app_assoc. by apply list_lookup_middle. }
  by rewrite Hlk.
Qed.

Lemma tcnt_step_eq i tr k s :
  tr !! k = Some s → es_ag s = i →
  tcnt i (take (S k) tr) = S (tcnt i (take k tr)).
Proof.
  intros Hk Hag. rewrite /tcnt (take_S_r tr k s Hk) list_basics.filter_app
    (filter_cons_True _ s [] Hag) filter_nil length_app /=. lia.
Qed.

Lemma tcnt_step_ne i tr k s :
  tr !! k = Some s → es_ag s ≠ i →
  tcnt i (take (S k) tr) = tcnt i (take k tr).
Proof.
  intros Hk Hag. rewrite /tcnt (take_S_r tr k s Hk) list_basics.filter_app
    (filter_cons_False _ s [] Hag) filter_nil length_app /=. lia.
Qed.

(** The machine's per-agent post-state, at [w_relp]. *)
Lemma mnext_ws_relp σ i l :
  w_relp (ms_ws (mnext σ i l) i) = lpost_relp (w_relp (ms_ws σ i)) l.
Proof.
  destruct l as [aq base ts vs|rl base vs kc|pr pw sr sw|
                 aq rl base ts rvs wvs kc]; simpl; rewrite upd_ws_eq.
  - apply load_post_run_relp.
  - rewrite store_post_run_relp. by destruct vs.
  - by destruct pw, sw.
  - rewrite store_post_run_relp load_post_run_relp. by destruct wvs.
Qed.

(** THE BRIDGE. *)
Lemma cand_ws_relp c i k :
  (k ≤ length (cd_tr c))%nat →
  w_relp (ms_ws (stt (cand_exec c) k) i)
  = w_relp (row_ws (trow i (cd_tr c)) (tcnt i (take k (cd_tr c)))).
Proof.
  induction k as [|k IH]; intros Hk.
  - have Hσ : stt (cand_exec c) 0%nat = cand_init c
      by (apply stt_lookup; exact (replay_0 (cand_init c) (cd_tr c))).
    by rewrite Hσ.
  - destruct (lookup_lt_is_Some_2 (cd_tr c) k ltac:(lia)) as [s Hs].
    rewrite (cand_next c k s Hs).
    destruct (decide (es_ag s = i)) as [Hag|Hag].
    + subst i. rewrite mnext_ws_relp.
      rewrite (tcnt_step_eq _ (cd_tr c) k s Hs eq_refl).
      rewrite (row_ws_step _ _ _ (trow_at _ (cd_tr c) k s Hs eq_refl)).
      rewrite lbl_post_relp (IH ltac:(lia)) //.
    + have Hne : i ≠ es_ag s by (intros Heq; apply Hag; by rewrite Heq).
      rewrite (mnext_ws_ne _ _ _ _ Hne).
      rewrite (tcnt_step_ne i (cd_tr c) k s Hs Hag). apply IH. lia.
Qed.

(* ====================================================================== *)
(** * 6. THE INTERLEAVING THEOREM

    The candidate's trace is an INTERLEAVING of the per-hart rows (that is
    exactly the third clause of [WeakRvwmoLin.rule14_linearization] /
    [WeakRvwmoHull.hull_linearizes]).  [supply_of_qconf] turns the per-hart
    emissions into [exec_prog_ok']'s trace-indexed supply: at trace position
    [k], agent [i]'s program state is the one its emission reaches after the
    number of [i]'s events strictly below [k].

    NOTE what the theorem does NOT need: [em_devfree].  The quiescence is
    already SPENT in the hypothesis's shape — the per-hart fabric is the
    constant [λ _, d0], which is what §2 justifies — and from there the
    interleaving is fabric-free. *)

(** The projection equation reads the wstate ONLY through [w_relp]. *)
Lemma hlbl_realizes_relp p ws ws' lb l :
  w_relp ws' = w_relp ws → hlbl_realizes p ws lb l → hlbl_realizes p ws' lb l.
Proof.
  intros Hr (Hnb & Hlat & Hrf & Hpr). split_and!; [done|done|done|].
  by rewrite (pcls_ev_relp p l ws' ws Hr).
Qed.

Lemma hlbl_realizes_pair_relp p pm ws ws' lb l1 l2 :
  w_relp ws' = w_relp ws →
  hlbl_realizes_pair p pm ws lb l1 l2 → hlbl_realizes_pair p pm ws' lb l1 l2.
Proof.
  intros Hr (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
             -> & -> & Hne & Hlen & ->).
  have Hc : pcls_ev pm (LExStore rl base data asrc2 vsrc2)
              (load_post_run ws' aq base tvs.*1)
          = pcls_ev pm (LExStore rl base data asrc2 vsrc2)
              (load_post_run ws aq base tvs.*1).
  { apply pcls_ev_relp. by rewrite !load_post_run_relp Hr. }
  exists aq, rl, base, tvs, data, asrc1, asrc2, vsrc2.
  split_and!; [done|done|done|done|by rewrite Hc].
Qed.

Theorem supply_of_qconf (c : cand) (boot : agent → pexv6) (d0 : dev_state)
    (rows : agent → list lbl) (N : nat) :
  (* the trace is an interleaving of the rows ... *)
  (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c) = rows i) →
  (* ... over the agents below [N] (everyone else is absent from it) ... *)
  (∀ i, (N ≤ i)%nat → rows i = []) →
  (* ... and every such agent's row is emittable at the CONSTANT fabric *)
  (∀ i, (i < N)%nat → ∃ em, hart_conf i (rows i) (boot i) (λ _, d0) em) →
  ∃ pst : nat → list pexv6,
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c).
Proof.
  intros Hrows Hbnd Hconf.
  have Hch : ∀ i, (i < N)%nat → ∃ f : nat → pexv6,
      f 0%nat = boot i ∧
      ∀ n lb, rows i !! n = Some lb →
        hblock (λ _, d0) n (row_ws (rows i) n) lb (f n) (f (S n)).
  { intros i Hi. destruct (Hconf i Hi) as (em & Hem).
    exact (hart_conf_states i (rows i) (boot i) (λ _, d0) em Hem). }
  destruct (nat_bounded_choice (λ _ : nat, PDisk None) _ N Hch) as (F & HF).
  exists (λ k, (λ i, F i (tcnt i (take k (cd_tr c)))) <$> seq 0 N).
  split.
  - apply list_eq. intros j. rewrite !list_lookup_fmap.
    destruct (decide (j < N)%nat) as [Hj|Hj].
    + rewrite lookup_seq_lt //=. by rewrite (proj1 (HF j Hj)).
    + rewrite lookup_seq_ge //. lia.
  - intros k s Hs. simpl in Hs.
    have Hklen : (k ≤ length (cd_tr c))%nat.
    { pose proof (lookup_lt_Some _ _ _ Hs). lia. }
    have Hrow : rows (es_ag s) !! tcnt (es_ag s) (take k (cd_tr c))
                = Some (es_lb s).
    { rewrite -Hrows. exact (trow_at (es_ag s) (cd_tr c) k s Hs eq_refl). }
    have HiN : (es_ag s < N)%nat.
    { destruct (decide (es_ag s < N)%nat) as [?|Hge]; [done|].
      rewrite (Hbnd (es_ag s) ltac:(lia)) in Hrow.
      by rewrite lookup_nil in Hrow. }
    destruct (HF (es_ag s) HiN) as (Hf0 & Hfb).
    destruct (Hfb _ _ Hrow) as (pa & da & Hstar & Hdisj).
    have Hrelp : w_relp (ms_ws (stt (cand_exec c) k) (es_ag s))
               = w_relp (row_ws (rows (es_ag s))
                                (tcnt (es_ag s) (take k (cd_tr c)))).
    { rewrite (cand_ws_relp c (es_ag s) k Hklen) /trow. by rewrite Hrows. }
    exists (F (es_ag s) (tcnt (es_ag s) (take k (cd_tr c)))), pa, da,
           (F (es_ag s) (S (tcnt (es_ag s) (take k (cd_tr c))))).
    split_and!.
    + rewrite list_lookup_fmap lookup_seq_lt //=.
    + apply list_eq. intros j. rewrite list_lookup_fmap.
      destruct (decide (j < N)%nat) as [Hj|Hj].
      * rewrite lookup_seq_lt //=.
        destruct (decide (j = es_ag s)) as [->|Hji].
        { rewrite list_lookup_insert;
            [|rewrite length_fmap length_seq; lia].
          by rewrite (tcnt_step_eq _ (cd_tr c) k s Hs eq_refl). }
        { rewrite list_lookup_insert_ne // list_lookup_fmap
                  lookup_seq_lt //=.
          rewrite (tcnt_step_ne j (cd_tr c) k s Hs
                     (λ H, Hji (eq_sym H))) //. }
      * rewrite lookup_seq_ge; [|lia]. simpl.
        rewrite list_lookup_insert_ne; [|lia].
        rewrite list_lookup_fmap lookup_seq_ge //. lia.
    + exact Hstar.
    + destruct Hdisj as [(l & Hre & Hst)|
                         (pm & dm & pm2 & dm2 & l1 & l2 & Hre & Hs1 & Hs2 & Hs3)].
      * left. exists l. split; [|exact Hst].
        apply hlbl_realizes_ax.
        by eapply hlbl_realizes_relp; [exact Hrelp|exact Hre].
      * right. exists pm, dm, pm2, dm2, l1, l2.
        split_and!; [|exact Hs1|exact Hs2|exact Hs3].
        apply hlbl_realizes_pair_ax.
        by eapply hlbl_realizes_pair_relp; [exact Hrelp|exact Hre].
Qed.

(* ====================================================================== *)
(** * 7. THE COMPOSITIONS

    [supply_of_qconf]'s three hypotheses, supplied by the two landed
    linearizations: [WeakRvwmoHull.hull_linearizes] (the |V|-induction's
    route: a violation-free hull) and [WeakRvwmoTopo.normalize_of_acyclic] +
    [WeakRvwmoLin.rule14_linearization] (the acyclicity route). *)

Lemma qconf_rows boot d0 GD i :
  gdexec_qconf boot d0 GD →
  ∃ em, hart_conf i (default [] (gx_prog (gd_g GD) !! i)) (boot i)
                  (λ _, d0) em.
Proof.
  intros Hq. destruct (gx_prog (gd_g GD) !! i) as [row|] eqn:E; simpl.
  - destruct (Hq i row E) as (em & Hem & _ & _). by exists em.
  - exists (HEm [] (boot i)). apply HEnil.
Qed.

Lemma prog_row_nil G i :
  (length (gx_prog G) ≤ i)%nat → default [] (gx_prog G !! i) = [].
Proof. intros H. by rewrite (lookup_ge_None_2 _ _ H). Qed.

Lemma gxh_nharts G cs :
  (length (gx_prog (gx_hull G cs)) ≤ length (gx_prog G))%nat.
Proof.
  change (gx_prog (gx_hull G cs))
    with ((λ row : list lbl, lbl_ren (hren G cs) <$> row)
            <$> zip_with take cs (gx_prog G)).
  rewrite length_fmap length_zip_with. lia.
Qed.

(** ** 7.1 THE HULL ROUTE *)
Theorem hull_supply (boot : agent → pexv6) (d0 : dev_state)
    (GD : gdexec) (cs : list nat) (N : nat) :
  rvwmo_minus_deps_consistent GD →
  hull_ok (gd_g GD) cs →
  (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol (gd_g GD) e w) →
  gdexec_qconf boot d0 GD →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c) ∧
    cd_log c (length (cd_tr c))
      = omap (gmsg (gd_g GD)) (filter (gcut cs) (gwrites (gd_g GD))).
Proof.
  intros Hcons Hok Hvf Hq HN.
  destruct (hull_linearizes GD cs Hcons Hok Hvf)
    as (c & Hsr & Himg & Hrow & Hlog).
  destruct (supply_of_qconf c boot d0
              (λ i, default [] (gx_prog (gx_hull (gd_g GD) cs) !! i)) N)
    as (pst & Hpst0 & Hprog).
  - intros i. by rewrite (Hrow i) gxh_row.
  - intros i Hi. apply prog_row_nil.
    pose proof (gxh_nharts (gd_g GD) cs). lia.
  - intros i _.
    exact (qconf_rows boot d0 (gd_hull GD cs) i (gdexec_qconf_hull _ _ _ cs Hq)).
  - by exists c, pst.
Qed.

(** ** 7.2 THE ACYCLICITY ROUTE

    [normalize_of_acyclic]'s [Decision] premise is the instance
    [WeakRvwmoTopo] leaves open (its §4 note); it is passed through here
    rather than assumed. *)
Theorem topo_supply (boot : agent → pexv6) (d0 : dev_state)
    (GD : gdexec) (N : nat) :
  rvwmo_minus_deps_consistent GD →
  (∀ x y, Decision (RacyD GD x y)) →
  (∀ x, ¬ tc (RacyD GD) x x) →
  gdexec_qconf boot d0 GD →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c).
Proof.
  intros Hcons Hdec Hacy Hq HN.
  destruct (normalize_of_acyclic GD Hcons Hdec Hacy)
    as (GD' & pi & Hcons' & H14 & Hrr & Hdeps & _).
  have Hq' : gdexec_qconf boot d0 GD'
    by (eapply gdexec_qconf_ren; [exact Hrr|exact Hdeps|exact Hq]).
  destruct Hcons' as (Hc' & _ & _).
  destruct (rule14_linearization (gd_g GD') Hc' H14)
    as (c & Hsr & Himg & Hrow & _).
  destruct (supply_of_qconf c boot d0
              (λ i, default [] (gx_prog (gd_g GD') !! i)) N)
    as (pst & Hpst0 & Hprog).
  - exact Hrow.
  - intros i Hi. apply prog_row_nil.
    rewrite (rows_rel_nharts pi (gd_g GD) (gd_g GD') Hrr). lia.
  - intros i _. exact (qconf_rows boot d0 GD' i Hq').
  - exists c, pst. split_and!; [done| |done|done].
    rewrite Himg. by apply (rows_rel_img pi).
Qed.

(* ====================================================================== *)
(** * 8. SMOKE TESTS

    The interleaving bookkeeping ([trow]/[tcnt]) and the wstate bridge
    ([cand_ws_relp]) checked on a concrete three-step, three-agent trace.
    The point of the last one is END-TO-END: the release-pending bit the
    MACHINE's per-agent state carries at trace position 2 for agent 1 is the
    one the PER-HART ROW FOLD predicts — which is the only thing the
    projection equation reads of the state, and hence the whole content of
    §5. *)

Definition smoke_tr : list estep :=
  [EStep 0 (WeakAxiomatic.LStore false 0 [bv_0 8] WCplain);
   EStep 1 (WeakAxiomatic.LFence false true false true);
   EStep 0 (WeakAxiomatic.LStore false 8 [bv_0 8] WCplain)].

Definition smoke_c : cand := Cand (λ _, None) smoke_tr.

Example smoke_trow0 :
  trow 0 smoke_tr = [WeakAxiomatic.LStore false 0 [bv_0 8] WCplain;
                     WeakAxiomatic.LStore false 8 [bv_0 8] WCplain].
Proof. vm_compute. reflexivity. Qed.

Example smoke_trow1 :
  trow 1 smoke_tr = [WeakAxiomatic.LFence false true false true].
Proof. vm_compute. reflexivity. Qed.

Example smoke_tcnt0 : tcnt 0 (take 2 smoke_tr) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example smoke_tcnt1 : tcnt 1 (take 2 smoke_tr) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example smoke_row_relp :
  w_relp (row_ws (trow 1 smoke_tr) (tcnt 1 (take 2 smoke_tr))) = true.
Proof. vm_compute. reflexivity. Qed.

Example smoke_cand_relp : w_relp (ms_ws (stt (cand_exec smoke_c) 2) 1) = true.
Proof.
  exact (eq_trans (cand_ws_relp smoke_c 1 2 ltac:(simpl; lia)) smoke_row_relp).
Qed.

(** ... and the agent that has NOT fenced still has it clear. *)
Example smoke_cand_relp0 : w_relp (ms_ws (stt (cand_exec smoke_c) 2) 0) = false.
Proof.
  rewrite (cand_ws_relp smoke_c 0 2 ltac:(simpl; lia)). vm_compute. reflexivity.
Qed.

(* ====================================================================== *)
(** * 9. THE AUDIT *)

Print Assumptions hemit_devfree_const.
Print Assumptions hemit_devfree_reindex.
Print Assumptions gdexec_qconf_hull.
Print Assumptions gdexec_qconf_ren.
Print Assumptions hemit_states.
Print Assumptions cand_ws_relp.
Print Assumptions supply_of_qconf.
Print Assumptions hull_supply.
Print Assumptions topo_supply.
