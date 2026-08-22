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
    SLICE 2b (§4e, "SLICES 2b/3, STATED"): THE PER-INSTRUCTION LEMMA, in
    §§6-10.  The run of one instruction is a [pstep_ev] chain of the hart
    ([pevrun]), annotated ([phrun]) with the three things the chain does
    not carry: the carriers the steps READ, the registers they WROTE, and
    whether a step was an instruction BOUNDARY.  On top of it:

      (A) [instr_dagree] / [instr_dagree_ev] — the LOCKSTEP half.  From
          agreement off a taint set [T] and "the instruction read no
          tainted carrier" (as a statement about the CHANNEL's read set,
          via [phrun_ib_rds]), the second run is the first STEP FOR STEP:
          the same label list — hence the same emitted memory labels,
          address, data, class and sources — the same successor node,
          fence, channel and fabric, and register files still agreeing off
          [T].  This is what slice 3 consumes for the write labels.
      (B) [phrun_frame] / [taint_closure] / [taint_closure_load] — the
          DIVERGENT half.  Once a read's answers differ the two runs are at
          different NODES and share nothing; what survives is the frame
          law, so the taint set grows by exactly the registers the
          remainders wrote.

    THREE NARROWINGS, all deliberate and all stated at their lemma:

      - the agreement is now indexed by a PREDICATE, not a list, because a
        taint COMPLEMENT is not a list;
      - (A) is EXISTENTIAL in the second run ("the certified run can be
        built to follow the emission"), because the converse pairing is
        FALSE: [Choose] and the boundary's [tick] are invisible in the
        label, so equal labels do not pin equal runs.  Equal memory
        ANSWERS therefore need no hypothesis — the second run is built at
        the first one's answers, which is exactly the certification's use;
      - (B) does not COMPUTE the written set from the decoder ("the
        destination is the load's [rd]"): that is the instruction
        inventory, i.e. slice 3.  Here the written set is the run's own
        annotation, and the hypothesis demands [ereg_num r = Some n] of
        it — so a write to a NON-carrier (the PC!) cannot be absorbed into
        the taint set.  That is the honest statement that a tainted value
        reaching the PC is a control divergence this discipline does not
        cover.

    §10 is the non-vacuity witness: a two-node fragment that reads [x15]
    and writes [x14], run at a taint set holding the destination and not
    the source, so that none of the above is true merely for want of an
    inhabited step.

    ------------------------------------------------------------------------
    WHAT SLICE 2a LEFT OPEN (kept for the record; (P-a)-(P-d) are now
    discharged by §§6-8, (P-c) as the existential construction above).

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

    Nothing here is [Admitted] or [Axiom]-ed. *)
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
    no [wreg] satisfies it vacuously.

    SLICE 2b generalises [S] from a LIST to a PREDICATE [P : wreg -> Prop]:
    the certification's invariant is agreement OFF a taint set
    ([P := fun n => n ∉ T]), which is the membership predicate of no list.
    Nothing else changes — every slice-2a statement below is the instance
    [P := fun n => n ∈ S]. *)
Definition dreg_agree (P : wreg -> Prop) (rs1 rs2 : regstate) : Prop :=
  forall r : register,
    (forall n : wreg, ereg_num r = Some n -> P n) ->
    register_lookup r rs1 = register_lookup r rs2.

(** "every register this stretch read is allowed by [P]" — the shape the
    hypotheses below take, replacing slice 2a's [_ ⊆ S]. *)
Definition rds_ok (P : wreg -> Prop) (l : list wreg) : Prop :=
  forall n : wreg, n ∈ l -> P n.

Lemma rds_ok_app P l1 l2 : rds_ok P (l1 ++ l2) -> rds_ok P l1 /\ rds_ok P l2.
Proof.
  intros H. split; intros n Hn; apply H, elem_of_app; by [left|right].
Qed.

Lemma dreg_agree_refl P rs : dreg_agree P rs rs.
Proof. by intros r _. Qed.

Lemma dreg_agree_sym P rs1 rs2 :
  dreg_agree P rs1 rs2 -> dreg_agree P rs2 rs1.
Proof. intros Hag r Hr. symmetry. by apply Hag. Qed.

Lemma dreg_agree_trans P rs1 rs2 rs3 :
  dreg_agree P rs1 rs2 -> dreg_agree P rs2 rs3 -> dreg_agree P rs1 rs3.
Proof. intros H1 H2 r Hr. by rewrite (H1 r Hr) (H2 r Hr). Qed.

(** A SMALLER read set — equivalently a LARGER taint set — is a WEAKER
    requirement, so agreement transfers downwards: that is what lets one
    stretch's hypothesis serve each of its steps, and what lets a GROWING
    taint set weaken the certification's invariant. *)
Lemma dreg_agree_mono (P P' : wreg -> Prop) rs1 rs2 :
  (forall n, P n -> P' n) -> dreg_agree P' rs1 rs2 -> dreg_agree P rs1 rs2.
Proof. intros Hsub Hag r Hr. apply Hag. intros n Hn. by apply Hsub, Hr. Qed.

(** ... and it survives a register write that BOTH sides perform with the
    SAME value — which is every [RegWrite] node, because the written value
    is part of the node TERM, not of the register file. *)
Lemma dreg_agree_set P rs1 rs2 (r : register) (v : type_of_register r) :
  dreg_agree P rs1 rs2 ->
  dreg_agree P (register_set r v rs1) (register_set r v rs2).
Proof.
  intros Hag r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite !register_lookup_set.
  - rewrite !(irrelevant_register_set r' r _ v (register_beq_false r' r Hne)).
    by apply Hag.
Qed.

(** ... and, dually (slice 2b), a write into a register the agreement
    EXCLUDES — a carrier whose [wreg] the taint set holds — changes
    nothing the agreement speaks about.  This is the one-step frame law
    the taint closure of §9 is built from. *)
Lemma dreg_agree_excl P rs (r : register) (v : type_of_register r) :
  (exists n, ereg_num r = Some n /\ ~ P n) ->
  dreg_agree P rs (register_set r v rs).
Proof.
  intros (n & Hn & HP) r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - exfalso. by apply HP, Hr'.
  - by rewrite (irrelevant_register_set r' r _ v (register_beq_false r' r Hne)).
Qed.

(** The one use of the hypothesis: a node's own register is covered. *)
Lemma dreg_agree_read P rs1 rs2 (r : register) :
  (forall n : wreg, ereg_num r = Some n -> P n) ->
  dreg_agree P rs1 rs2 -> register_lookup r rs1 = register_lookup r rs2.
Proof. intros Hr Hag. by apply Hag. Qed.

Lemma pnode_rds_read (r : register) (dir : _)
    (k : type_of_register r -> M unit) (P : wreg -> Prop) (n : wreg) :
  rds_ok P (pnode_rds (Interface.Next (Interface.RegRead r dir) k)) ->
  ereg_num r = Some n -> P n.
Proof.
  intros Hsub Hn. apply Hsub.
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
Lemma pnode_step_dagree (P : wreg -> Prop) (m : M unit) (rs1 rs2 : regstate)
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (ors1 : option regstate) (fn' : option (bool * bool * bool * bool))
    (d' : dev_state) (oib : option oib32) :
  rds_ok P (pnode_rds m) ->
  dreg_agree P rs1 rs2 ->
  pnode_step m rs1 ib d l m' ors1 fn' d' oib ->
  exists ors2 : option regstate,
    pnode_step m rs2 ib d l m' ors2 fn' d' oib /\
    dreg_agree P (default rs1 ors1) (default rs2 ors2).
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
      exact (pnode_rds_read reg _ k P n Hsub Hn). }
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

Lemma esil_node_dagree (D : gset register) (P : wreg -> Prop)
    (rs1 rs2 : regstate) (m : M unit) (rs1' : regstate) (m1 : M unit) :
  rds_ok P (pnode_rds m) ->
  dreg_agree P rs1 rs2 ->
  esil_node D rs1 m = Some (rs1', m1) ->
  exists rs2' : regstate,
    esil_node D rs2 m = Some (rs2', m1) /\ dreg_agree P rs1' rs2'.
Proof.
  intros Hsub Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (injection Hnode as <- <-; exists rs2; by split).
  - (* RegRead: answered from the file, which agrees on the register *)
    case_decide as HrD; [|discriminate Hnode].
    have Hlk : register_lookup reg rs1 = register_lookup reg rs2.
    { apply Hag. intros n Hn.
      exact (pnode_rds_read reg _ k P n Hsub Hn). }
    injection Hnode as <- <-. rewrite Hlk. exists rs2. by split.
  - (* RegWrite: the same value moves on both sides *)
    case_decide as HrD; [|discriminate Hnode].
    injection Hnode as <- <-. eexists. split; [reflexivity|].
    by apply dreg_agree_set.
Qed.

(** THE SILENT-RUN LEMMA.  [WeakEvLift.esil_node_agree] iterated, but at the
    DYNAMIC footprint: the hypothesis is agreement on what the stretch READ,
    not on the whole owned register frame. *)
Theorem erun_silent_dagree (n : nat) (D : gset register) (P : wreg -> Prop)
    (rs1 rs2 : regstate) (m : M unit) (rs1' : regstate) (m1 : M unit) :
  rds_ok P (erun_rds n D rs1 m) ->
  dreg_agree P rs1 rs2 ->
  erun_silent n D rs1 m = (rs1', m1) ->
  exists rs2' : regstate,
    erun_silent n D rs2 m = (rs2', m1) /\ dreg_agree P rs1' rs2'.
Proof.
  revert rs1 rs2 m. induction n as [|n IH]; intros rs1 rs2 m Hsub Hag Hrun.
  { simpl in Hrun. injection Hrun as <- <-. exists rs2. by split. }
  simpl in Hrun. simpl in Hsub. simpl.
  destruct (esil_node D rs1 m) as [[rs1a m1a]|] eqn:Hnode.
  - simpl in Hrun. simpl in Hsub.
    have Hsub1 : rds_ok P (pnode_rds m).
    { intros x Hx. apply Hsub, elem_of_app. by left. }
    destruct (esil_node_dagree D P rs1 rs2 m rs1a m1a Hsub1 Hag Hnode)
      as (rs2a & Hnode2 & Hag2).
    rewrite Hnode2. apply (IH rs1a rs2a m1a); [|exact Hag2|exact Hrun].
    intros x Hx. apply Hsub, elem_of_app. by right.
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
  dreg_agree (fun w => w ∈ ib_rds (erun_ib n D rs1 m ib)) rs1 rs2 ->
  erun_silent n D rs1 m = (rs1', m1) ->
  exists rs2' : regstate,
    erun_silent n D rs2 m = (rs2', m1) /\
    dreg_agree (fun w => w ∈ ib_rds (erun_ib n D rs1 m ib)) rs1' rs2'.
Proof.
  intros Hann Hag Hrun.
  apply (erun_silent_dagree n D _ rs1 rs2 m rs1' m1); [|exact Hag|exact Hrun].
  intros x Hx. rewrite (erun_ib_rds n D rs1 m ib Hann).
  apply elem_of_app. by right.
Qed.

(* ====================================================================== *)
(** ** 5. THE INSTANCE-LEVEL STATEMENT

    [pstep_ev] at two hart states that differ only in the register file. *)

Lemma pstep_hart_dagree (P : wreg -> Prop) (cpu : CPU) (m : M unit)
    (rs1 rs2 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (ors1 : option regstate) (fn' : option (bool * bool * bool * bool))
    (d' : dev_state) (oib : option oib32) :
  rds_ok P (pnode_rds m) ->
  dreg_agree P rs1 rs2 ->
  pstep_hart cpu m rs1 fn ib d l m' ors1 fn' d' oib ->
  exists ors2 : option regstate,
    pstep_hart cpu m rs2 fn ib d l m' ors2 fn' d' oib /\
    dreg_agree P (default rs1 ors1) (default rs2 ors2).
Proof.
  intros Hsub Hag [Hn|Hp].
  - rewrite /pstep_node in Hn. destruct fn as [[[[pr pw] sr] sw]|].
    + destruct Hn as (-> & -> & -> & -> & -> & ->).
      exists None. split; [left; by split_and!|exact Hag].
    + destruct (pnode_step_dagree P m rs1 rs2 ib d l m' ors1 fn' d' oib
                  Hsub Hag Hn) as (ors2 & Hn2 & Hag2).
      exists ors2. split; [by left|exact Hag2].
  - (* THE PLIC WIRE: the delivered value comes from the FABRIC, so both
       sides write the same bit into the same register. *)
    destruct Hp as (-> & -> & -> & -> & -> & ->).
    eexists. split; [right; by split_and!|]. simpl.
    by apply dreg_agree_set.
Qed.

Theorem pstep_ev_dagree (P : wreg -> Prop) (cpu : CPU) (m : M unit)
    (rs1 rs2 : regstate) (fn : option (bool * bool * bool * bool))
    (ib : oib32) (d : dev_state) (l : wlabel) (m' : M unit)
    (rs1' : regstate) (fn' : option (bool * bool * bool * bool))
    (ib' : oib32) (d' : dev_state) :
  rds_ok P (pnode_rds m) ->
  dreg_agree P rs1 rs2 ->
  pstep_ev (PHart cpu m rs1 fn ib) d l (PHart cpu m' rs1' fn' ib') d' ->
  exists rs2' : regstate,
    pstep_ev (PHart cpu m rs2 fn ib) d l (PHart cpu m' rs2' fn' ib') d' /\
    dreg_agree P rs1' rs2'.
Proof.
  intros Hsub Hag (_ & ors1 & oib & -> & -> & Hst).
  destruct (pstep_hart_dagree P cpu m rs1 rs2 fn ib d l m' ors1 fn' d' oib
              Hsub Hag Hst) as (ors2 & Hst2 & Hag2).
  exists (default rs2 ors2). split; [|exact Hag2].
  split; [reflexivity|]. exists ors2, oib. by split_and!.
Qed.

(* ====================================================================== *)
(** ** 6. SLICE 2b: THE ANNOTATED HART STEP

    The per-instruction lemma is an induction over a hart's [pstep_ev]
    chain, and the induction needs three things the chain itself does not
    carry: WHICH carriers the step read (the taint hypothesis), WHICH
    registers it wrote (the taint conclusion) and WHETHER it was an
    instruction boundary (the channel's reset).  [pstep_hw] is [pstep_hart]
    with exactly those three annotations, computed from the node — one
    disjunct per arm of [pstep_hart], so that each annotation is EXACT
    rather than an over-approximation:

      - the plain node arm ([fn = None]) reads [pnode_rds m], writes
        [pnode_wrs m], and is a boundary iff [ibn_ann m];
      - the PARKED-FENCE arm consults neither the node nor the register
        file: no reads, no writes, no boundary;
      - the PLIC wire writes [sig_seip] and nothing else. *)

(** THE REGISTERS ONE NODE WRITES — the dual of [pnode_rds].  A [RegWrite]
    contributes its register; every other node contributes nothing
    ([pnode_step]'s [ors] is [None] at every other arm, which is
    [pnode_step_ors] below). *)
Definition pnode_wrs (m : M unit) : list register :=
  match m with
  | Interface.Ret _ => []
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegWrite r _ _ => [r]
      | _ => []
      end
  end.

Lemma pnode_step_ors (m : M unit) (rs : regstate) (ib : oib32) (d : dev_state)
    (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) :
  pnode_step m rs ib d l m' ors fn' d' oib ->
  ors = None \/
  exists (r : register) (v : type_of_register r),
    r ∈ pnode_wrs m /\ ors = Some (register_set r v rs).
Proof.
  destruct m as [y|T oc k].
  { intros (tick & _ & _ & -> & _). by left. }
  destruct oc; simpl; intros Hstep;
    repeat (match goal with
            | H : context[if dev_addr ?a then _ else _] |- _ =>
                destruct (dev_addr a)
            | H : False |- _ => destruct H
            | H : exists _, _ |- _ => destruct H as [? H]
            | H : _ /\ _ |- _ => destruct H as [? H]
            | H : _ \/ _ |- _ => destruct H as [H|H]
            end); subst; try (by left).
  right. exists reg, regval. split; [|reflexivity].
  by apply elem_of_list_singleton.
Qed.

(** THE BOUNDARY IS VISIBLE IN THE LABEL.  Both nodes that reset the
    channel — the terminal [Ret] and the [InstrAnnounce] — emit [LInstr],
    and no other node does; so "this run stays inside one instruction" is
    the checkable side condition [LInstr ∉ ls]. *)
Lemma pnode_step_ann (m : M unit) (rs : regstate) (ib : oib32)
    (d : dev_state) (l : wlabel) (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) :
  pnode_step m rs ib d l m' ors fn' d' oib -> ibn_ann m = true -> l = LInstr.
Proof.
  destruct m as [y|T oc k].
  { by intros (tick & -> & _) _. }
  destruct oc; simpl; intros Hstep Hann; try discriminate Hann.
  by destruct Hstep as (-> & _).
Qed.

Definition pstep_hw (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : option (bool * bool * bool * bool)) (ib : oib32) (d : dev_state)
    (l : wlabel) (rds : list wreg) (ws : list register) (ann : bool)
    (m' : M unit) (ors : option regstate)
    (fn' : option (bool * bool * bool * bool)) (d' : dev_state)
    (oib : option oib32) : Prop :=
  (fn = None /\ pnode_step m rs ib d l m' ors fn' d' oib /\
   rds = pnode_rds m /\ ws = pnode_wrs m /\ ann = ibn_ann m)
  \/ (exists pr pw sr sw, fn = Some (pr, pw, sr, sw) /\
        pstep_node cpu m rs fn ib d l m' ors fn' d' oib /\
        rds = [] /\ ws = [] /\ ann = false)
  \/ (pstep_plic cpu m rs fn ib d l m' ors fn' d' oib /\
      rds = [] /\ ws = [(sig_seip : register)] /\ ann = false).

Lemma pstep_hw_hart cpu m rs fn ib d l rds ws ann m' ors fn' d' oib :
  pstep_hw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib ->
  pstep_hart cpu m rs fn ib d l m' ors fn' d' oib.
Proof.
  intros [(-> & H & _)|[(pr & pw & sr & sw & -> & H & _)|(H & _)]].
  - left. exact H.
  - by left.
  - by right.
Qed.

Lemma pstep_hart_hw cpu m rs fn ib d l m' ors fn' d' oib :
  pstep_hart cpu m rs fn ib d l m' ors fn' d' oib ->
  exists rds ws ann, pstep_hw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib.
Proof.
  intros [Hn|Hp].
  - destruct fn as [[[[pr pw] sr] sw]|].
    + exists [], [], false. right; left. exists pr, pw, sr, sw. by split_and!.
    + exists (pnode_rds m), (pnode_wrs m), (ibn_ann m).
      left. by split_and!.
  - exists [], [(sig_seip : register)], false. right; right. by split_and!.
Qed.

(** The three annotations, one lemma each. *)
Lemma pstep_hw_ann cpu m rs fn ib d l rds ws ann m' ors fn' d' oib :
  pstep_hw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib ->
  ann = true -> l = LInstr.
Proof.
  intros [(-> & H & _ & _ & ->)|[(pr & pw & sr & sw & -> & H & _ & _ & ->)
                                |(H & _ & _ & ->)]] Hann;
    [by eapply pnode_step_ann|discriminate Hann|discriminate Hann].
Qed.

Lemma pstep_hw_channel cpu m rs fn ib d l rds ws ann m' ors fn' d' oib :
  pstep_hw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib ->
  ann = false -> ib_rds (default ib oib) = ib_rds ib ++ rds.
Proof.
  intros [(-> & H & -> & _ & ->)|[(pr & pw & sr & sw & -> & H & -> & _ & _)
                                 |(H & -> & _)]] Hann.
  - rewrite (pnode_step_channel m rs ib d l m' ors fn' d' oib H).
    by apply ibn_step_rds.
  - destruct H as (_ & _ & _ & _ & _ & ->). by rewrite app_nil_r.
  - destruct H as (_ & _ & _ & _ & -> & _). by rewrite app_nil_r.
Qed.

Lemma pstep_hw_frame (P : wreg -> Prop) cpu m rs fn ib d l rds ws ann m'
    ors fn' d' oib :
  pstep_hw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib ->
  (forall r, r ∈ ws -> exists n, ereg_num r = Some n /\ ~ P n) ->
  dreg_agree P rs (default rs ors).
Proof.
  intros [(-> & H & _ & -> & _)|[(pr & pw & sr & sw & -> & H & _ & -> & _)
                                |(H & _ & -> & _)]] Hws.
  - destruct (pnode_step_ors m rs ib d l m' ors fn' d' oib H)
      as [->|(r & v & Hr & ->)]; simpl; [apply dreg_agree_refl|].
    apply dreg_agree_excl. by apply Hws.
  - destruct H as (_ & _ & -> & _). apply dreg_agree_refl.
  - destruct H as (_ & _ & _ & _ & _ & ->). simpl.
    apply dreg_agree_excl. apply Hws. by apply elem_of_list_singleton.
Qed.

(** THE STEP'S OWN AGREEMENT LEMMA: [pstep_hart_dagree] at the annotated
    shape.  Note the annotations are carried UNCHANGED to the second run —
    the two runs read the same registers, write the same registers and
    cross the same boundaries, because they are at the SAME node. *)
Lemma pstep_hw_dagree (P : wreg -> Prop) cpu m rs1 rs2 fn ib d l rds ws ann
    m' ors1 fn' d' oib :
  pstep_hw cpu m rs1 fn ib d l rds ws ann m' ors1 fn' d' oib ->
  rds_ok P rds ->
  dreg_agree P rs1 rs2 ->
  exists ors2, pstep_hw cpu m rs2 fn ib d l rds ws ann m' ors2 fn' d' oib /\
    dreg_agree P (default rs1 ors1) (default rs2 ors2).
Proof.
  intros [(-> & H & -> & -> & ->)|[(pr & pw & sr & sw & -> & H & -> & -> & ->)
                                  |(H & -> & -> & ->)]] Hrds Hag.
  - destruct (pnode_step_dagree P m rs1 rs2 ib d l m' ors1 fn' d' oib
                Hrds Hag H) as (ors2 & H2 & Hag2).
    exists ors2. split; [left; by split_and!|exact Hag2].
  - destruct H as (-> & -> & -> & -> & -> & ->). exists None. split.
    + right; left. exists pr, pw, sr, sw. by split_and!.
    + exact Hag.
  - destruct H as (-> & -> & -> & -> & -> & ->).
    eexists. split; [right; right; by split_and!|]. simpl.
    by apply dreg_agree_set.
Qed.

(* ====================================================================== *)
(** ** 7. THE RUN: a hart's [pstep_ev] chain, and its annotated twin *)

(** THE PLAIN CHAIN, at Layer 1's own type. *)
Inductive pevrun : list wlabel -> pexv6 -> dev_state -> pexv6 -> dev_state
    -> Prop :=
| pevrun_nil p d : pevrun [] p d p d
| pevrun_more l ls p d p1 d1 p2 d2 :
    pstep_ev p d l p1 d1 -> pevrun ls p1 d1 p2 d2 ->
    pevrun (l :: ls) p d p2 d2.

(** THE ANNOTATED CHAIN of ONE hart: the same steps, carrying the read
    list, the written list and the boundary flag of §6, concatenated. *)
Inductive phrun (cpu : CPU) : list wlabel -> list wreg -> list register ->
    bool -> M unit -> regstate -> option (bool * bool * bool * bool) ->
    oib32 -> dev_state -> M unit -> regstate ->
    option (bool * bool * bool * bool) -> oib32 -> dev_state -> Prop :=
| phrun_nil m rs fn ib d : phrun cpu [] [] [] false m rs fn ib d m rs fn ib d
| phrun_more l ls rds rds' ws ws' ann ann' m rs fn ib d
      m1 ors fn1 oib d1 m2 rs2 fn2 ib2 d2 :
    pstep_hw cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib ->
    phrun cpu ls rds' ws' ann' m1 (default rs ors) fn1 (default ib oib) d1
      m2 rs2 fn2 ib2 d2 ->
    phrun cpu (l :: ls) (rds ++ rds') (ws ++ ws') (ann || ann')
      m rs fn ib d m2 rs2 fn2 ib2 d2.

Lemma phrun_pevrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' :
  phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' ->
  pevrun ls (PHart cpu m rs fn ib) d (PHart cpu m' rs' fn' ib') d'.
Proof.
  induction 1 as [|l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib
                    d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH].
  - apply pevrun_nil.
  - eapply pevrun_more; [|exact IH].
    split; [reflexivity|]. exists ors, oib.
    split_and!; [reflexivity|reflexivity|].
    eapply pstep_hw_hart. exact Hstep.
Qed.

Lemma pevrun_phrun ls p d p' d' :
  pevrun ls p d p' d' ->
  forall cpu m rs fn ib m' rs' fn' ib',
    p = PHart cpu m rs fn ib -> p' = PHart cpu m' rs' fn' ib' ->
    exists rds ws ann, phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d'.
Proof.
  induction 1 as [p d|l ls p d p1 d1 p2 d2 Hstep Hrun IH];
    intros cpu m rs fn ib m' rs' fn' ib' -> Heq.
  { injection Heq as -> -> -> ->.
    exists [], [], false. apply phrun_nil. }
  destruct p1 as [cpu1 m1 rs1 fn1 ib1|dp1]; [|by destruct p2].
  destruct Hstep as (-> & ors & oib & -> & -> & Hst).
  destruct (pstep_hart_hw cpu m rs fn ib d l m1 ors fn1 d1 oib Hst)
    as (rds & ws & ann & Hhw).
  destruct (IH cpu m1 (default rs ors) fn1 (default ib oib) m' rs' fn' ib'
              eq_refl Heq) as (rds' & ws' & ann' & Hrun').
  exists (rds ++ rds'), (ws ++ ws'), (ann || ann').
  by eapply phrun_more.
Qed.

(** The run-level readings of §6's three annotations. *)
Theorem phrun_ib_rds cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' :
  phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' ->
  ann = false -> ib_rds ib' = ib_rds ib ++ rds.
Proof.
  induction 1 as [|l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib
                    d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH]; intros Hann.
  { by rewrite app_nil_r. }
  apply orb_false_elim in Hann as [Ha Hb].
  have Hc : ib_rds (default ib oib) = ib_rds ib ++ rds.
  { by eapply pstep_hw_channel; [exact Hstep|exact Ha]. }
  rewrite (IH Hb) Hc. by rewrite -app_assoc.
Qed.

Lemma phrun_ann cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' :
  phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' ->
  ann = true -> LInstr ∈ ls.
Proof.
  induction 1 as [|l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib
                    d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH]; intros Hann;
    [discriminate Hann|].
  apply orb_true_elim in Hann as [Ha|Hb].
  - have Hl : l = LInstr.
    { by eapply pstep_hw_ann; [exact Hstep|exact Ha]. }
    rewrite Hl. apply elem_of_list_here.
  - apply elem_of_list_further, IH, Hb.
Qed.

Corollary phrun_no_instr cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' :
  phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' ->
  LInstr ∉ ls -> ann = false.
Proof.
  intros Hrun Hni. destruct ann; [|reflexivity].
  exfalso. apply Hni. by eapply phrun_ann; [exact Hrun|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 8. (A) THE PER-INSTRUCTION SOUNDNESS LEMMA

    Two runs of ONE hart from register files that agree off the taint set
    [T], at the same node, the same parked fence, the same channel and the
    same fabric.  If the run READS no tainted carrier then the second run
    is the FIRST one step for step: the same labels — hence the same
    emitted memory labels, address, data, class and sources included — the
    same successor node, fence, channel and fabric, and register files
    that still agree off [T].

    THE MEMORY ANSWERS need no hypothesis in this formulation, and that is
    the point of stating it existentially: the second run is CONSTRUCTED
    from the first, so it is constructed AT THE SAME ANSWERS ([tvs], the
    [Choose]n value, the [Ret]'s tick).  That is exactly the certification's
    use — the solo run is built to follow the graph's values, and this
    lemma says the build succeeds and emits what the emission emits.  The
    converse pairing ("two GIVEN runs with equal labels are equal") is
    FALSE and must not be assumed: [Choose] and the boundary's [tick] are
    invisible in the label. *)
Theorem phrun_dagree (P : wreg -> Prop) cpu ls rds ws ann m rs1 fn ib d
    m' rs1' fn' ib' d' :
  phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' ->
  rds_ok P rds ->
  forall rs2, dreg_agree P rs1 rs2 ->
  exists rs2', phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' /\
    dreg_agree P rs1' rs2'.
Proof.
  induction 1 as [m rs fn ib d|l ls rds rds' ws ws' ann ann' m rs fn ib d
                    m1 ors fn1 oib d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH];
    intros Hrds rsb Hag.
  { exists rsb. split; [apply phrun_nil|exact Hag]. }
  apply rds_ok_app in Hrds as [Hrds1 Hrds2].
  destruct (pstep_hw_dagree P cpu m rs rsb fn ib d l rds ws ann m1 ors fn1
              d1 oib Hstep Hrds1 Hag) as (orsb & Hstepb & Hagb).
  destruct (IH Hrds2 (default rsb orsb) Hagb) as (rsb' & Hrunb & Hagb').
  exists rsb'. split; [|exact Hagb'].
  by eapply phrun_more.
Qed.

(** THE HEADLINE, at the channel: the hypothesis is about the read set the
    CHANNEL ends up holding — which is what [WeakEvLang.erw_srcs] hands to
    the emission and what §4e's "no [row_deps] path from a substituted read
    to [z]" is a statement about — and the side condition that the run
    stays inside one instruction is the checkable [LInstr ∉ ls]. *)
Theorem instr_dagree (T : list wreg) cpu ls rds ws ann m rs1 fn ib d
    m' rs1' fn' ib' d' :
  phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' ->
  LInstr ∉ ls ->
  (forall n, n ∈ ib_rds ib' -> n ∉ T) ->
  forall rs2, dreg_agree (fun n => n ∉ T) rs1 rs2 ->
  exists rs2', phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' /\
    dreg_agree (fun n => n ∉ T) rs1' rs2'.
Proof.
  intros Hrun Hni Hib rs2 Hag.
  have Hann : ann = false.
  { by eapply phrun_no_instr; [exact Hrun|exact Hni]. }
  have Hcov : ib_rds ib' = ib_rds ib ++ rds.
  { by eapply phrun_ib_rds; [exact Hrun|exact Hann]. }
  eapply phrun_dagree; [exact Hrun| |exact Hag].
  intros n Hn. apply Hib. rewrite Hcov. apply elem_of_app. by right.
Qed.

(** ... and the same statement over [pstep_ev] chains, which is the form
    §4e asks for: the annotations are recovered from the chain. *)
Theorem instr_dagree_ev (T : list wreg) cpu ls m rs1 fn ib d m' rs1' fn' ib' d' :
  pevrun ls (PHart cpu m rs1 fn ib) d (PHart cpu m' rs1' fn' ib') d' ->
  LInstr ∉ ls ->
  (forall n, n ∈ ib_rds ib' -> n ∉ T) ->
  forall rs2, dreg_agree (fun n => n ∉ T) rs1 rs2 ->
  exists rs2',
    pevrun ls (PHart cpu m rs2 fn ib) d (PHart cpu m' rs2' fn' ib') d' /\
    dreg_agree (fun n => n ∉ T) rs1' rs2'.
Proof.
  intros Hrun Hni Hib rs2 Hag.
  destruct (pevrun_phrun ls _ d _ d' Hrun cpu m rs1 fn ib m' rs1' fn' ib'
              eq_refl eq_refl) as (rds & ws & ann & Hh).
  destruct (instr_dagree T cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d'
              Hh Hni Hib rs2 Hag) as (rs2' & Hh2 & Hag2).
  exists rs2'. split; [|exact Hag2]. by eapply phrun_pevrun; exact Hh2.
Qed.

(** THE WRITE LABEL IS A FUNCTION OF THE NODE AND THE CHANNEL, not of the
    register file — the fact §4e's clause (iii) names, and the reason the
    lockstep above delivers equal stores.  [LLoad]/[LExLoad] are NOT
    determined this way: their [tvs] is the MACHINE's answer, which is why
    equal answers is a hypothesis of the certification and not a
    theorem. *)
Definition wl_is_store (l : wlabel) : bool :=
  match l with
  | LStore _ _ _ _ _ | LExStore _ _ _ _ _ => true
  | _ => false
  end.

Lemma pnode_step_store_det (m : M unit) (rs1 rs2 : regstate) (ib : oib32)
    (d : dev_state) (l1 l2 : wlabel) (m1 m2 : M unit)
    (ors1 ors2 : option regstate)
    (fn1 fn2 : option (bool * bool * bool * bool)) (d1 d2 : dev_state)
    (oib1 oib2 : option oib32) :
  pnode_step m rs1 ib d l1 m1 ors1 fn1 d1 oib1 ->
  pnode_step m rs2 ib d l2 m2 ors2 fn2 d2 oib2 ->
  wl_is_store l1 = true -> wl_is_store l2 = true -> l1 = l2.
Proof.
  destruct m as [y|T oc k].
  { by intros (t1 & -> & _) (t2 & -> & _). }
  destruct oc; simpl; intros H1 H2;
    repeat (match goal with
            | H : context[if dev_addr ?a then _ else _] |- _ =>
                destruct (dev_addr a)
            | H : False |- _ => destruct H
            | H : exists _, _ |- _ => destruct H as [? H]
            | H : _ /\ _ |- _ => destruct H as [? H]
            | H : _ \/ _ |- _ => destruct H as [H|H]
            end); subst; intros Hs1 Hs2;
    try discriminate Hs1; try discriminate Hs2; try reflexivity;
    congruence.
Qed.

(* ====================================================================== *)
(** ** 9. (B) THE TAINT CLOSURE: what a DIVERGENT remainder costs

    When a memory read's answers DIFFER the two runs part company — the
    continuation is [k (inl (w, None))], so a different [w] is a different
    NODE, and from there the runs share nothing.  What survives is a FRAME
    property, and it is the honest general content of §4e's clause (ii):
    a run changes the register file only where it WRITES, so agreement
    survives off the written set.  The taint set therefore grows by exactly
    the registers the divergent remainder writes — [pnode_wrs] on the node
    arm, [sig_seip] on the PLIC wire — and NOT by anything else.

    WHAT THIS DOES NOT DO, deliberately: it does not COMPUTE the written
    set from the decoded instruction ("the destination is the decoder's
    [rd]").  That is the instruction inventory, i.e. slice 3's own work;
    here the written set is the run's annotation, and the caller discharges
    "the remainder writes only [rd]" per instruction form.  The hypothesis
    is stated so that a non-carrier write (the PC!) CANNOT be absorbed into
    the taint set: [ereg_num r = Some n] is required, which is exactly the
    honest statement that a tainted value reaching the PC is a control
    divergence the taint discipline does not cover. *)
Theorem phrun_frame (P : wreg -> Prop) cpu ls rds ws ann m rs fn ib d
    m' rs' fn' ib' d' :
  phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' ->
  (forall r, r ∈ ws -> exists n, ereg_num r = Some n /\ ~ P n) ->
  dreg_agree P rs rs'.
Proof.
  induction 1 as [|l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib
                    d1 m2 rs2 fn2 ib2 d2 Hstep Hrun IH]; intros Hws.
  { apply dreg_agree_refl. }
  eapply dreg_agree_trans.
  - eapply pstep_hw_frame; [exact Hstep|].
    intros r Hr. apply Hws, elem_of_app. by left.
  - apply IH. intros r Hr. apply Hws, elem_of_app. by right.
Qed.

(** THE CLOSURE, for two runs that have parted company: agreement off the
    OLD taint set plus what either remainder wrote. *)
Theorem taint_closure (P : wreg -> Prop) cpu1 ls1 rds1 ws1 ann1
    m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1'
    cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' :
  dreg_agree P rs1 rs2 ->
  phrun cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' ->
  phrun cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' ->
  (forall r, r ∈ ws1 ++ ws2 -> exists n, ereg_num r = Some n /\ ~ P n) ->
  dreg_agree P rs1' rs2'.
Proof.
  intros Hag Hr1 Hr2 Hws.
  have H1 : dreg_agree P rs1 rs1'.
  { eapply phrun_frame; [exact Hr1|].
    intros r Hr. apply Hws, elem_of_app. by left. }
  have H2 : dreg_agree P rs2 rs2'.
  { eapply phrun_frame; [exact Hr2|].
    intros r Hr. apply Hws, elem_of_app. by right. }
  eapply dreg_agree_trans; [by apply dreg_agree_sym|].
  eapply dreg_agree_trans; [exact Hag|exact H2].
Qed.

(** ... in the form §4e quotes: a load whose answers differ taints its
    DESTINATION [rd], and the next instruction's agreement holds off
    [rd :: T].  [T'] here is [rd :: T]; the hypothesis says both
    remainders write only carriers already tainted or [rd] itself. *)
Corollary taint_closure_load (T : list wreg) (rd : wreg) cpu1 ls1 rds1 ws1
    ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1'
    cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' :
  dreg_agree (fun n => n ∉ T) rs1 rs2 ->
  phrun cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' ->
  phrun cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' ->
  (forall r, r ∈ ws1 ++ ws2 ->
     exists n, ereg_num r = Some n /\ n ∈ rd :: T) ->
  dreg_agree (fun n => n ∉ rd :: T) rs1' rs2'.
Proof.
  intros Hag Hr1 Hr2 Hws.
  eapply taint_closure; [|exact Hr1|exact Hr2|].
  - eapply dreg_agree_mono; [|exact Hag].
    intros n Hn Hin. apply Hn, elem_of_list_further, Hin.
  - intros r Hr. destruct (Hws r Hr) as (n & Hn & Hin).
    exists n. split; [exact Hn|]. intros Hno. by apply Hno.
Qed.

(* ====================================================================== *)
(** ** 10. NON-VACUITY

    Every hypothesis above is satisfiable with a NON-EMPTY run whose
    annotations are non-empty: a two-node instruction fragment that READS
    one carrier ([x15]) and WRITES another ([x14]), run at a taint set that
    holds the destination and not the source.  Without this the whole
    section could be true because [pstep_hw] is uninhabited at a non-empty
    read or write list. *)
Definition wit_m : M unit :=
  Interface.Next (Interface.RegRead (R_bitvector_64 x15) None)
    (fun v => Interface.Next (Interface.RegWrite (R_bitvector_64 x14) None v)
                (fun _ => Interface.Ret tt)).

Lemma wit_run (cpu : CPU) (rs : regstate) (d : dev_state) :
  exists ls rds ws ann m' ib' rs',
    phrun cpu ls rds ws ann wit_m rs None ib_none d m' rs' None ib' d /\
    rds = [15%nat] /\ ws = [(R_bitvector_64 x14 : register)] /\
    ann = false /\ LInstr ∉ ls /\ ib_rds ib' = [15%nat].
Proof.
  eexists _, _, _, _, _, _, _. split_and!.
  - eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /wit_m /pnode_step. by split_and!. }
    eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /pnode_step. by split_and!. }
    apply phrun_nil.
  - by vm_compute.
  - by vm_compute.
  - reflexivity.
  - intros Hin. apply elem_of_cons in Hin as [Hin|Hin]; [discriminate Hin|].
    apply elem_of_cons in Hin as [Hin|Hin]; [|by apply elem_of_nil in Hin].
    vm_compute in Hin. discriminate Hin.
  - by vm_compute.
Qed.

Example instr_dagree_nonvacuous (cpu : CPU) (rs1 rs2 : regstate)
    (d : dev_state) :
  dreg_agree (fun n => n ∉ [14%nat]) rs1 rs2 ->
  exists ls m' ib' rs1' rs2',
    phrun cpu ls [15%nat] [(R_bitvector_64 x14 : register)] false
      wit_m rs1 None ib_none d m' rs1' None ib' d /\
    phrun cpu ls [15%nat] [(R_bitvector_64 x14 : register)] false
      wit_m rs2 None ib_none d m' rs2' None ib' d /\
    dreg_agree (fun n => n ∉ [14%nat]) rs1' rs2'.
Proof.
  intros Hag.
  destruct (wit_run cpu rs1 d)
    as (ls & rds & ws & ann & m' & ib' & rs1' & Hrun & -> & -> & -> & Hni & Hib).
  destruct (instr_dagree [14%nat] cpu ls [15%nat]
              [(R_bitvector_64 x14 : register)] false wit_m rs1 None ib_none d
              m' rs1' None ib' d Hrun Hni
              ltac:(rewrite Hib; intros n Hn;
                    apply elem_of_list_singleton in Hn as ->;
                    intros Hin; apply elem_of_list_singleton in Hin;
                    discriminate Hin)
              rs2 Hag) as (rs2' & Hrun2 & Hag2).
  by exists ls, m', ib', rs1', rs2'.
Qed.
