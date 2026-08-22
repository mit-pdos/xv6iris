(** * WeakEvProv.v — DEPENDENCY-PROVENANCE SOUNDNESS (B2e-3b, slice 2a)

    Design: [claude-notes/design/weak-memory-route-b.md] §4e, the "TWO
    SHAPES" block and its **DECIDED (ii) DYNAMIC PROVENANCE**.

    ------------------------------------------------------------------------
    WHAT THIS FILE IS FOR.

    The certification step of §4d.2(2) claims that a SOLO RUN of the verified
    program emits a given write with the graph's label whenever every read
    feeding it reads its true source.  That is a VALUE-DETERMINISM property of
    the EMISSION — "the label is a function of the values of the registers the
    instruction reads and of its own memory answers" — and tier 1 never needed
    it: it used the dependency annotations for ORDERING only, and nothing in
    the tree said that the Sail semantics reads exactly the registers the
    decoded roles name.  IT DOES NOT: a translated access reads [satp] and
    [mstatus], [sret] reads [sepc], and RVWMO's syntactic roles name none of
    them (deviation D-4).

    SLICE 2a's ANSWER (DEC-7, [WeakEvLang]): the emission's SOURCE lists stop
    being decoded and become the per-instruction READ SET the machine
    accumulates in [WeakLang.ibch] — appended to at every [RegRead] of a
    carrier register, reset at the two instruction boundaries.  Coverage then
    holds BY CONSTRUCTION, and what is left to prove is the GENERIC
    determinism fact: two runs of the SAME Sail continuation from regstates
    that agree on the registers the run actually reads are IDENTICAL.  That
    generic fact is this file.

    ------------------------------------------------------------------------
    THE THREE STATEMENTS, in the order the design asks for them.

    (1) PER STEP.  [pnode_step_dagree]: one monad node, two regstates that
        agree on the registers THAT NODE reads (which is [{r}] at a
        [RegRead r] and [∅] everywhere else) — same label, same continuation,
        same channel, same device state, and the successor regstates still
        agree.  [pnode_step_regread_agree] is the [RegRead] case on its own,
        which is the one the design names.

    (2) PER SILENT STRETCH.  [erun_silent_dagree]: the same, iterated along
        [WeakEvLift.erun_silent] — the reflective silent stepper the WP tier
        already batches with — with the read set of the whole stretch
        ([erun_rds]) as the agreement footprint.  This is
        [WeakEvLift.esil_node_agree]'s spine at the WEAKER hypothesis: that
        lemma assumes agreement on the entire owned footprint [D], this one
        assumes agreement only on what the stretch READ.

    (3) THE COVERAGE BRIDGE.  [pnode_step_channel] / [erun_ib_rds]: the
        channel's read set is EXACTLY the list of carrier registers the
        stretch read (given that the stretch crosses no instruction
        boundary, which is what [erun_ann] rules out).  Together with (2)
        this is the sentence the certification wants: agreement on the
        sources the emission NAMES implies agreement on everything the run
        consulted, hence the same emitted label.

    ------------------------------------------------------------------------
    WHAT IS **NOT** PROVED HERE, AND EXACTLY WHAT IT WOULD TAKE.

    The PER-INSTRUCTION statement — "two runs of one instruction from
    regstates agreeing on the instruction's named sources, given EQUAL
    memory-read answers, emit the same memory-event sequence" — is not
    stated as a single theorem, because an instruction's run is not a silent
    stretch: it is a silent stretch, then a labelled node, then another, and
    the labelled nodes' successors are chosen by the MACHINE (a read's [tvs],
    a [Choose]) rather than computed from [rs].  Its obligations, each of
    which is discharged by a lemma already in this file or in [WeakEvInst],
    are:

      (P-a) the silent stretches: [erun_silent_dagree] (proved here);
      (P-b) the labelled nodes' LABELS: for a [RegWrite] the label is
            [erw_label (erw_of (deps_of_ib (ib_bits ib)) (ib_rds ib) r)],
            a function of the CHANNEL and the NODE alone — no [rs] — so it
            is equal on both sides as soon as the channel is
            ([pnode_step_dagree] gives that, and [pnode_step_channel] says
            the channel moves as a function of the node alone).  For a
            memory node the label's [base]/[data] come from the node's own
            request record, likewise [rs]-free;
      (P-c) the labelled nodes' CONTINUATIONS: a [MemRead] continues at
            [k (inl (w, None))], so EQUAL ANSWERS ⇒ equal continuations —
            this is the "for memory reads: equal answers ([tvs]) ⇒ equal
            continuations" clause, and it is a hypothesis of the
            certification (the solo run is run AT the graph's values), not a
            fact about the semantics;
      (P-d) the ITERATION over (a)–(c) until the instruction boundary, which
            needs a measure: the number of nodes an instruction takes is not
            bounded uniformly (the walker's loop), so the induction has to be
            on the run's own length, i.e. on the [rtc] of
            [WeakEvLift.esilD] plus one labelled step — the shape
            [WeakEvLift.erun_silent_sound] already produces.

    None of (P-b)–(P-d) needs a new mechanism; they need the certification's
    own statement to exist, which is slice 3.  Nothing here is [Admitted]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import RiscvLang RiscvPtsto.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakEvLift.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The footprint: which registers a node reads, and what agreement
       on a read set means *)

(** THE REGISTERS ONE NODE READS, as the channel records them: a [RegRead]
    of a dependency CARRIER contributes its [wreg], everything else
    contributes nothing.  This is [WeakEvLang.ib_rd]'s payload, read off the
    node instead of the channel. *)
Definition pnode_rds (m : M unit) : list wreg :=
  match m with
  | Interface.Ret _ => []
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead r _ =>
          match ereg_num r with Some n => [n] | None => [] end
      | _ => []
      end
  end.

(** AGREEMENT AT A READ SET.  Two regstates agree at [S] when they agree on
    every register that is either NOT a dependency carrier (PC,
    [cur_privilege], [misa], the counters — the "non-memory state" of the
    design's soundness sentence, which the certification's solo run shares
    with the real one by construction) or is a carrier NAMED in [S].

    The premise is the exact dual of [WeakEvLang.ereg_num]: a register with
    no [wreg] satisfies it vacuously. *)
Definition dreg_agree (S : list wreg) (rs1 rs2 : regstate) : Prop :=
  forall r : register,
    (forall n : wreg, ereg_num r = Some n -> n ∈ S) ->
    register_lookup r rs1 = register_lookup r rs2.

Lemma dreg_agree_refl S rs : dreg_agree S rs rs.
Proof. by intros r _. Qed.

Lemma dreg_agree_sym S rs1 rs2 :
  dreg_agree S rs1 rs2 -> dreg_agree S rs2 rs1.
Proof. intros Hag r Hr. symmetry. by apply Hag. Qed.

(** A SMALLER read set is a WEAKER requirement, so agreement transfers
    downwards — which is what lets one stretch's hypothesis serve each of
    its steps. *)
Lemma dreg_agree_mono S S' rs1 rs2 :
  S ⊆ S' -> dreg_agree S' rs1 rs2 -> dreg_agree S rs1 rs2.
Proof.
  intros Hsub Hag r Hr. apply Hag. intros n Hn.
  unfold subseteq, list_subseteq in Hsub. exact (Hsub n (Hr n Hn)).
Qed.

(** ... and it survives a register write that BOTH sides perform with the
    SAME value — which is every [RegWrite] node, because the written value
    is part of the node TERM, not of the register file. *)
Lemma dreg_agree_set S rs1 rs2 (r : register) (v : type_of_register r) :
  dreg_agree S rs1 rs2 ->
  dreg_agree S (register_set r v rs1) (register_set r v rs2).
Proof.
  intros Hag r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite !register_lookup_set.
  - rewrite !(irrelevant_register_set r' r _ v (register_beq_false r' r Hne)).
    by apply Hag.
Qed.

(** The one use of the hypothesis: a node's own register is covered. *)
Lemma dreg_agree_read S rs1 rs2 (r : register) :
  (forall n : wreg, ereg_num r = Some n -> n ∈ S) ->
  dreg_agree S rs1 rs2 -> register_lookup r rs1 = register_lookup r rs2.
Proof. intros Hr Hag. by apply Hag. Qed.

Lemma pnode_rds_read (r : register) (dir : _)
    (k : type_of_register r -> M unit) (S : list wreg) (n : wreg) :
  pnode_rds (Interface.Next (Interface.RegRead r dir) k) ⊆ S ->
  ereg_num r = Some n -> n ∈ S.
Proof.
  intros Hsub Hn. unfold subseteq, list_subseteq in Hsub. apply Hsub.
  rewrite /pnode_rds /= Hn. by apply elem_of_list_singleton.
Qed.

(* ====================================================================== *)
(** ** 2. PER STEP: [rs] is consulted at a [RegRead] and nowhere else *)

(** THE DESIGN'S OWN SENTENCE: a [RegRead r] step from two regstates that
    agree on [r] produces the SAME continuation (and the same everything
    else). *)
Lemma pnode_step_regread_agree (r : register) (dir : _)
    (k : type_of_register r -> M unit) (rs1 rs2 : regstate) (ib : oib32)
    (d : dev_state) (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) :
  register_lookup r rs1 = register_lookup r rs2 ->
  pnode_step (Interface.Next (Interface.RegRead r dir) k) rs1 ib d l m' ors
    fn' d' oib ->
  pnode_step (Interface.Next (Interface.RegRead r dir) k) rs2 ib d l m' ors
    fn' d' oib.
Proof.
  intros Hlk (-> & -> & -> & -> & -> & ->). rewrite Hlk.
  by split_and!.
Qed.

(** ... AND THE WHOLE NODE DISPATCH, uniformly.  The successor register file
    may differ (a [RegWrite] writes into both), but it still agrees at the
    same read set, so the statement composes. *)
Lemma pnode_step_dagree (S : list wreg) (m : M unit) (rs1 rs2 : regstate)
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (ors1 : option regstate) (fn' : option (bool * bool * bool * bool))
    (d' : dev_state) (oib : option oib32) :
  pnode_rds m ⊆ S ->
  dreg_agree S rs1 rs2 ->
  pnode_step m rs1 ib d l m' ors1 fn' d' oib ->
  exists ors2 : option regstate,
    pnode_step m rs2 ib d l m' ors2 fn' d' oib /\
    dreg_agree S (default rs1 ors1) (default rs2 ors2).
Proof.
  intros Hsub Hag Hstep. destruct m as [y|T oc k].
  { exists ors1. split; [exact Hstep|].
    destruct Hstep as (tick & _ & _ & -> & _). exact Hag. }
  destruct oc; simpl in Hstep |- *;
    try (by destruct Hstep);
    try (exists ors1; split; [exact Hstep|];
         destruct ors1 as [x|]; [apply dreg_agree_refl|exact Hag]).
  - (* [RegRead]: the ONE place the register file is consulted *)
    have Hlk : register_lookup reg rs1 = register_lookup reg rs2.
    { apply Hag. intros n Hn.
      exact (pnode_rds_read reg _ k S n Hsub Hn). }
    exists ors1. split.
    + destruct Hstep as (-> & -> & -> & -> & -> & ->).
      rewrite Hlk. by split_and!.
    + destruct Hstep as (_ & _ & -> & _). exact Hag.
  - (* [RegWrite]: both sides write the SAME value, taken from the node *)
    destruct Hstep as (-> & -> & -> & -> & -> & ->).
    exists (Some (register_set reg regval rs2)). split; [by split_and!|].
    simpl. by apply dreg_agree_set.
Qed.

(* ====================================================================== *)
(** ** 3. THE COVERAGE BRIDGE: the channel records exactly those reads *)

(** The channel's move at one node, as a FUNCTION of the node — which is
    what makes it independent of the register file and of the label. *)
Definition ibn_step (m : M unit) (ib : oib32) : oib32 :=
  match m with
  | Interface.Ret _ => ib_none
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead r _ => ib_rd ib r
      | Interface.InstrAnnounce ob => ib_ann (ib_of_bvn ob)
      | _ => ib
      end
  end.

(** ... and whether the node is an INSTRUCTION BOUNDARY, i.e. one of the two
    nodes that RESET the read set. *)
Definition ibn_ann (m : M unit) : bool :=
  match m with
  | Interface.Ret _ => true
  | Interface.Next oc _ =>
      match oc with Interface.InstrAnnounce _ => true | _ => false end
  end.

Lemma pnode_step_channel (m : M unit) (rs : regstate) (ib : oib32)
    (d : dev_state) (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) :
  pnode_step m rs ib d l m' ors fn' d' oib -> default ib oib = ibn_step m ib.
Proof.
  destruct m as [y|T oc k].
  { by intros (tick & _ & _ & _ & _ & _ & ->). }
  destruct oc; simpl; intros Hstep;
    repeat (match goal with
            | H : context[if dev_addr ?a then _ else _] |- _ =>
                destruct (dev_addr a)
            | H : False |- _ => destruct H
            | H : exists _, _ |- _ => destruct H as [? H]
            | H : _ /\ _ |- _ => destruct H as [? H]
            | H : _ \/ _ |- _ => destruct H as [H|H]
            end); subst; reflexivity.
Qed.

(** THE ACCUMULATION LAW: away from an instruction boundary the channel's
    read set grows by exactly the node's own reads. *)
Lemma ibn_step_rds (m : M unit) (ib : oib32) :
  ibn_ann m = false -> ib_rds (ibn_step m ib) = ib_rds ib ++ pnode_rds m.
Proof.
  destruct m as [y|T oc k]; [done|].
  destruct oc; simpl; intros Hann; try discriminate Hann;
    try by rewrite app_nil_r.
  rewrite /ib_rd /ib_read. by destruct (ereg_num reg); [|rewrite app_nil_r].
Qed.

(* ====================================================================== *)
(** ** 4. PER SILENT STRETCH: the induction, on [WeakEvLift]'s spine *)

(** The reads of a whole silent stretch, along the SAME reflective stepper
    the WP tier batches with ([WeakEvLift.erun_silent]). *)
Fixpoint erun_rds (n : nat) (D : gset register) (rs : regstate) (m : M unit)
    : list wreg :=
  match n with
  | 0%nat => []
  | S n' =>
      match esil_node D rs m with
      | Some (rs', m') => pnode_rds m ++ erun_rds n' D rs' m'
      | None => []
      end
  end.

(** ... its channel, and whether it crosses an instruction boundary. *)
Fixpoint erun_ib (n : nat) (D : gset register) (rs : regstate) (m : M unit)
    (ib : oib32) : oib32 :=
  match n with
  | 0%nat => ib
  | S n' =>
      match esil_node D rs m with
      | Some (rs', m') => erun_ib n' D rs' m' (ibn_step m ib)
      | None => ib
      end
  end.

Fixpoint erun_ann (n : nat) (D : gset register) (rs : regstate) (m : M unit)
    : bool :=
  match n with
  | 0%nat => false
  | S n' =>
      match esil_node D rs m with
      | Some (rs', m') => ibn_ann m || erun_ann n' D rs' m'
      | None => false
      end
  end.

(** WHETHER a silent node fires does not depend on the register file — only
    on the node and on the owned footprint.  (It is what lets the two sides
    of the agreement lemma stop at the same place.) *)
Lemma esil_node_none (D : gset register) (rs1 rs2 : regstate) (m : M unit) :
  esil_node D rs1 m = None -> esil_node D rs2 m = None.
Proof.
  destruct m as [y|T oc k]; [done|].
  destruct oc; simpl; try done; case_decide; done.
Qed.

Lemma esil_node_dagree (D : gset register) (S : list wreg)
    (rs1 rs2 : regstate) (m : M unit) (rs1' : regstate) (m1 : M unit) :
  pnode_rds m ⊆ S ->
  dreg_agree S rs1 rs2 ->
  esil_node D rs1 m = Some (rs1', m1) ->
  exists rs2' : regstate,
    esil_node D rs2 m = Some (rs2', m1) /\ dreg_agree S rs1' rs2'.
Proof.
  intros Hsub Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (injection Hnode as <- <-; exists rs2; by split).
  - (* RegRead: answered from the file, which agrees on the register *)
    case_decide as HrD; [|discriminate Hnode].
    have Hlk : register_lookup reg rs1 = register_lookup reg rs2.
    { apply Hag. intros n Hn.
      exact (pnode_rds_read reg _ k S n Hsub Hn). }
    injection Hnode as <- <-. rewrite Hlk. exists rs2. by split.
  - (* RegWrite: the same value moves on both sides *)
    case_decide as HrD; [|discriminate Hnode].
    injection Hnode as <- <-. eexists. split; [reflexivity|].
    by apply dreg_agree_set.
Qed.

(** THE SILENT-RUN LEMMA.  [WeakEvLift.esil_node_agree] iterated, but at the
    DYNAMIC footprint: the hypothesis is agreement on what the stretch READ,
    not on the whole owned register frame. *)
Theorem erun_silent_dagree (n : nat) (D : gset register) (S : list wreg)
    (rs1 rs2 : regstate) (m : M unit) (rs1' : regstate) (m1 : M unit) :
  erun_rds n D rs1 m ⊆ S ->
  dreg_agree S rs1 rs2 ->
  erun_silent n D rs1 m = (rs1', m1) ->
  exists rs2' : regstate,
    erun_silent n D rs2 m = (rs2', m1) /\ dreg_agree S rs1' rs2'.
Proof.
  revert rs1 rs2 m. induction n as [|n IH]; intros rs1 rs2 m Hsub Hag Hrun.
  { simpl in Hrun. injection Hrun as <- <-. exists rs2. by split. }
  simpl in Hrun. simpl in Hsub. simpl.
  destruct (esil_node D rs1 m) as [[rs1a m1a]|] eqn:Hnode.
  - simpl in Hrun. simpl in Hsub.
    have Hsub1 : pnode_rds m ⊆ S.
    { intros x Hx. unfold subseteq, list_subseteq in Hsub.
      apply Hsub, elem_of_app. by left. }
    destruct (esil_node_dagree D S rs1 rs2 m rs1a m1a Hsub1 Hag Hnode)
      as (rs2a & Hnode2 & Hag2).
    rewrite Hnode2. apply (IH rs1a rs2a m1a); [|exact Hag2|exact Hrun].
    intros x Hx. unfold subseteq, list_subseteq in Hsub.
    apply Hsub, elem_of_app. by right.
  - simpl in Hrun. rewrite (esil_node_none D rs1 rs2 m Hnode).
    injection Hrun as <- <-. exists rs2. by split.
Qed.

(** THE COVERAGE STATEMENT, at the stretch: away from an instruction
    boundary the channel accumulates EXACTLY the stretch's carrier reads.
    Composed with [erun_silent_dagree] this says what the certification
    needs — agreement on the sources the emission NAMES is agreement on
    everything the stretch consulted. *)
Theorem erun_ib_rds (n : nat) (D : gset register) (rs : regstate)
    (m : M unit) (ib : oib32) :
  erun_ann n D rs m = false ->
  ib_rds (erun_ib n D rs m ib) = ib_rds ib ++ erun_rds n D rs m.
Proof.
  revert rs m ib. induction n as [|n IH]; intros rs m ib Hann.
  { simpl. by rewrite app_nil_r. }
  simpl in Hann |- *.
  destruct (esil_node D rs m) as [[rs1 m1]|] eqn:Hnode;
    [|by rewrite app_nil_r].
  simpl in Hann. apply orb_false_elim in Hann as [Ha Hb].
  rewrite (IH rs1 m1 (ibn_step m ib) Hb) (ibn_step_rds m ib Ha).
  by rewrite -app_assoc.
Qed.

(** ... and the corollary the certification quotes: if the two regstates
    agree at the read set the CHANNEL ends up holding, they agree at the
    read set the stretch needs, so the stretch is the same on both sides. *)
Corollary erun_silent_dagree_channel (n : nat) (D : gset register)
    (rs1 rs2 : regstate) (m : M unit) (ib : oib32) (rs1' : regstate)
    (m1 : M unit) :
  erun_ann n D rs1 m = false ->
  dreg_agree (ib_rds (erun_ib n D rs1 m ib)) rs1 rs2 ->
  erun_silent n D rs1 m = (rs1', m1) ->
  exists rs2' : regstate,
    erun_silent n D rs2 m = (rs2', m1) /\
    dreg_agree (ib_rds (erun_ib n D rs1 m ib)) rs1' rs2'.
Proof.
  intros Hann Hag Hrun.
  apply (erun_silent_dagree n D _ rs1 rs2 m rs1' m1); [|exact Hag|exact Hrun].
  rewrite (erun_ib_rds n D rs1 m ib Hann).
  intros x Hx. apply elem_of_app. by right.
Qed.

(* ====================================================================== *)
(** ** 5. THE INSTANCE-LEVEL STATEMENT

    [pstep_ev] at two hart states that differ only in the register file. *)

Lemma pstep_hart_dagree (S : list wreg) (cpu : CPU) (m : M unit)
    (rs1 rs2 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (ors1 : option regstate) (fn' : option (bool * bool * bool * bool))
    (d' : dev_state) (oib : option oib32) :
  pnode_rds m ⊆ S ->
  dreg_agree S rs1 rs2 ->
  pstep_hart cpu m rs1 fn ib d l m' ors1 fn' d' oib ->
  exists ors2 : option regstate,
    pstep_hart cpu m rs2 fn ib d l m' ors2 fn' d' oib /\
    dreg_agree S (default rs1 ors1) (default rs2 ors2).
Proof.
  intros Hsub Hag [Hn|Hp].
  - rewrite /pstep_node in Hn. destruct fn as [[[[pr pw] sr] sw]|].
    + destruct Hn as (-> & -> & -> & -> & -> & ->).
      exists None. split; [left; by split_and!|exact Hag].
    + destruct (pnode_step_dagree S m rs1 rs2 ib d l m' ors1 fn' d' oib
                  Hsub Hag Hn) as (ors2 & Hn2 & Hag2).
      exists ors2. split; [by left|exact Hag2].
  - (* THE PLIC WIRE: the delivered value comes from the FABRIC, so both
       sides write the same bit into the same register. *)
    destruct Hp as (-> & -> & -> & -> & -> & ->).
    eexists. split; [right; by split_and!|]. simpl.
    by apply dreg_agree_set.
Qed.

Theorem pstep_ev_dagree (S : list wreg) (cpu : CPU) (m : M unit)
    (rs1 rs2 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (rs1' : regstate) (fn' : option (bool * bool * bool * bool))
    (ib' : oib32) (d' : dev_state) :
  pnode_rds m ⊆ S ->
  dreg_agree S rs1 rs2 ->
  pstep_ev (PHart cpu m rs1 fn ib) d l (PHart cpu m' rs1' fn' ib') d' ->
  exists rs2' : regstate,
    pstep_ev (PHart cpu m rs2 fn ib) d l (PHart cpu m' rs2' fn' ib') d' /\
    dreg_agree S rs1' rs2'.
Proof.
  intros Hsub Hag (_ & ors1 & oib & -> & -> & Hst).
  destruct (pstep_hart_dagree S cpu m rs1 rs2 fn ib d l m' ors1 fn' d' oib
              Hsub Hag Hst) as (ors2 & Hst2 & Hag2).
  exists (default rs2 ors2). split; [|exact Hag2].
  split; [reflexivity|]. exists ors2, oib. by split_and!.
Qed.
