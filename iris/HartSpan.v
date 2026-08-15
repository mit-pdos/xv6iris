(* HartSpan.v -- THE SPAN RULE, the B′ keystone (design doc §5 item 1c).

   A batched stretch (HartLift) requires every touched register in an
   exclusively-owned footprint.  A real cycle's prelude reads ~54 registers
   that are NOT ownable and whose values are irrelevant (the pmpaddr file
   with every PMP entry OFF, mie/mideleg/mip/sig_meip/sig_seip under
   MIE=0).  The span rule covers such stretches:

     - WRITES are gated on the caller's exclusive footprint [Drw]
       (frame + ghost updates, exactly as the batch rule);
     - READS ARE UNGATED -- the machine answers them from its own file;
     - a read-only, dfrac-generic frame [Dro] pins the value-SENSITIVE
       reads (the config bundle) and is exported as an agreement fact;
     - the continuation is quantified over the RELATIONAL landing set:
       an rtc of span steps in which, BETWEEN nodes, every register
       outside [Drw ∪ Dro] may be perturbed arbitrarily.  That is the
       honest in-WP knowledge: the ghost cells pin exactly the framed
       registers; the semantic licence (RiscvLang.prim_step_hart_regs_frame
       -- only the plic's sig_seip write is cross-thread) pins more, but
       is not derivable from inside a WP proof.

   The landing quantifier is killed by a ONCE-PER-CLASS pure
   characterization lemma: with the [Dro] values pinned, every span chain
   from the class's monad is forced to the same landing, because each
   unowned read feeds a value-insensitive continuation (checked by cbn --
   the mechanism the symbolic-stretch probe validated).  Spans are CHOPPED
   at invariant-cell writes (minstret_increment / minstret / the tick's
   clock cells), each a single-node HartRegNode rule.

   The rule is proven by STRUCTURAL INDUCTION ON THE MONAD -- each step's
   continuation is an immediate subterm -- via the [Acc] fixpoint
   [mchild_wf]; no Löb, no fuel. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The span step, pure layer.                                           *)
(* ====================================================================== *)

(* One MACHINE node of a span: reads ungated, writes gated on [Drw],
   silent-class nodes free; memory, device, Ret, Choose and out-of-[Drw]
   writes are NOT span steps -- they are where a span STOPS. *)
Definition hspan_node (Drw : gset register) (c c' : M unit * regstate)
    : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       | Interface.RegRead r _        => fun k =>
           c' = (k (register_lookup r c.2), c.2)
       | Interface.RegWrite r _ v     => fun k =>
           r ∈ Drw /\ c' = (k tt, register_set r v c.2)
       | Interface.InstrAnnounce _    => fun k => c' = (k tt, c.2)
       | Interface.BranchAnnounce _ _ => fun k => c' = (k tt, c.2)
       | Interface.Barrier _          => fun k => c' = (k tt, c.2)
       | Interface.CacheOp _          => fun k => c' = (k tt, c.2)
       | Interface.TlbOp _            => fun k => c' = (k tt, c.2)
       | Interface.TakeException _    => fun k => c' = (k tt, c.2)
       | Interface.ReturnException _  => fun k => c' = (k tt, c.2)
       | Interface.TranslationStart _ => fun k => c' = (k tt, c.2)
       | Interface.TranslationEnd _   => fun k => c' = (k tt, c.2)
       | Interface.CycleCount         => fun k => c' = (k tt, c.2)
       | Interface.Message _          => fun k => c' = (k tt, c.2)
       | Interface.GetCycleCount      => fun k => c' = (k 0%Z, c.2)
       | _ => fun _ => False
       end) k
  end.

(* the INTERFERED span step: before the node, every register outside
   [D = Drw ∪ Dro] may have been re-written by the environment.  [rs1] is
   the file the node actually runs on. *)
Definition hspani (D Drw : gset register) (c c' : M unit * regstate)
    : Prop :=
  exists rs1 : regstate,
    reg_agree_on D rs1 c.2 /\ hspan_node Drw (c.1, rs1) c'.

Definition hspan (D Drw : gset register) : relation (M unit * regstate) :=
  rtc (hspani D Drw).

(* Where a span stops: the node classes [hspan_node] refuses regardless of
   the file -- the boundary ([Ret]), a memory/device event, [Choose], a
   failure -- or a register WRITE outside [Drw].  This is a function of the
   monad's head alone, so the caller's characterization lemma can compute
   it. *)
Definition hspan_stops (Drw : gset register) (m : M unit) : bool :=
  match m with
  | Interface.Ret _ => true
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead _ _ => false
      | Interface.RegWrite r _ _ => bool_decide (r ∉ Drw)
      | Interface.MemRead _ _ => true
      | Interface.MemWrite _ _ => true
      | Interface.Choose _ => true
      | Interface.GenericFail _ => true
      | Interface.Discard => true
      | Interface.ExtraOutcome _ => true
      | _ => false
      end
  end.

(* ====================================================================== *)
(* 2. Structural well-foundedness of the monad: each span step's           *)
(*    continuation is an immediate subterm.  The [Acc] fixpoint is what    *)
(*    lets the WP rule recurse without fuel (the weak branch's             *)
(*    [WeakSailComplete.mchild_wf] is the pattern source).                 *)
(* ====================================================================== *)

(* immediate-subterm: [y] is an immediate continuation of [m].  The
   match-Prop form (∃ v, y = k v) rather than an Inductive: [Acc] is in
   Prop so the ∃ eliminates into it, the structural [Fixpoint] recurses
   through the function field, and no dependent inversion (hence no UIP)
   is ever needed.  This is the weak branch's validated
   [WeakSailComplete.mchild] kit, transcribed. *)
Definition mchild (y m : M unit) : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next _ k => exists v, y = k v
  end.

Fixpoint macc (m : M unit) {struct m} : Acc mchild m.
Proof.
  constructor. intros y Hy. destruct m as [x|T oc k]; cbn in Hy.
  - destruct Hy.
  - destruct Hy as [v ->]. apply macc.
Defined.

Lemma mchild_wf : well_founded mchild.
Proof. exact macc. Qed.

(* a span step descends the subterm order *)
Lemma hspan_node_mchild (Drw : gset register) (c c' : M unit * regstate) :
  hspan_node Drw c c' -> mchild c'.1 c.1.
Proof.
  (* TODO(agent): destruct the node; each arm's successor is [k v] for the
     node's own continuation -- exhibit the [∃ v]. *)
  destruct c as [m rs]. destruct m as [y|T oc k]; simpl; [intros []|].
  destruct oc; simpl; intros H;
    first
      [ exact (match H with end)
      | rewrite H; simpl; by eexists
      | destruct H as [_ ->]; simpl; by eexists ].
Qed.

(* ====================================================================== *)
(* 3. The read-only frame: dfrac-generic, never updated, exported as       *)
(*    agreement.                                                           *)
(* ====================================================================== *)

Section span.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* per-register dfracs: the config bundle mixes [DfracOwn q] cells
     (cur_privilege, mstatus, pmpcfg, hart_state) with discarded [□] ones
     (misa, mseccfg, pma_regions, htif, ...) *)
  Definition hreg_frame_ro (Df : register -> dfrac) (rs : regstate)
      (Dro : gset register) : iProp Σ :=
    ([∗ set] r ∈ Dro, reg_pointsto r (Df r) (register_lookup r rs))%I.

  Lemma hreg_frame_ro_agree Df rs Dro (rs0 : regstate) :
    reg_interp rs0 -∗ hreg_frame_ro Df rs Dro -∗
    ⌜reg_agree_on Dro rs rs0⌝.
  Proof.
    (* TODO(agent): as HartLift.hreg_frame_agree, with [reg_valid_dq]. *)
    rewrite /hreg_frame_ro. iIntros "Hi Hf".
    rewrite bi.pure_forall. iIntros (r). rewrite bi.pure_impl. iIntros (Hr).
    iDestruct (big_sepS_elem_of _ _ r Hr with "Hf") as "Hr".
    iDestruct (reg_valid_dq rs0 r (Df r) (register_lookup r rs) with "Hi Hr")
      as %Hv.
    iPureIntro. by symmetry.
  Qed.

  (* helper: the ro-frame, like [hreg_frame], only reads the footprint's
     lookups, so it re-anchors across any file agreeing on [Dro]. *)
  Local Lemma hreg_frame_ro_ext_local Df rs rs' Dro :
    reg_agree_on Dro rs rs' ->
    hreg_frame_ro Df rs Dro ⊣⊢ hreg_frame_ro Df rs' Dro.
  Proof.
    intros Hag. rewrite /hreg_frame_ro. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  (* helper: ONE machine node of a span, with the [wp_hart_step] mask dance,
     witness/inversion and ghost re-establishment done once.  The
     continuation receives the machine's pre file [rsM] (which the frames
     pin on [Drw ∪ Dro]) and the [hspan_node] step it took, with both
     frames re-anchored at the landing file [rs2]. *)
  Local Lemma wp_hspan_node_local (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (m : M unit) :
    Drw ## Dro ->
    hspan_stops Drw m = false ->
    ⊢ gen_cert -∗
      hreg_frame rs Drw -∗
      hreg_frame_ro Df rs Dro -∗
      ▷ (∀ (m2 : M unit) (rsM rs2 : regstate),
           ⌜reg_agree_on (Drw ∪ Dro) rs rsM⌝ -∗
           ⌜hspan_node Drw (m, rsM) (m2, rs2)⌝ -∗
           hreg_frame rs2 Drw -∗
           hreg_frame_ro Df rs2 Dro -∗
           WP (HartE gen_id cpu_id m2 : expr riscv_lang)) -∗
      WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros (Hdisj Hns) "#Hcert Hrf Hro H".
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ". destruct σ as [rsM mem0 dev0].
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (hreg_frame_agree rs Drw rsM with "Hri Hrf") as %HagW.
    iDestruct (hreg_frame_ro_agree Df rs Dro rsM with "Hri Hro") as %HagO.
    assert (Hag : reg_agree_on (Drw ∪ Dro) rs rsM).
    { intros r' Hr'. apply elem_of_union in Hr' as [Hr'|Hr'];
        [by apply HagW|by apply HagO]. }
    destruct m as [y|T oc k]; [discriminate Hns|].
    destruct oc; try discriminate Hns.
    (* 14 goals: RegRead, RegWrite, then the 12 silent classes *)
    2: { (* RegWrite: [hspan_stops = false] forces [reg ∈ Drw] *)
      apply bool_decide_eq_false_1, dec_stable in Hns.
      assert (HrO : reg ∉ Dro) by set_solver.
      assert (HagW' : reg_agree_on Drw (register_set reg regval rs)
                        (register_set reg regval rsM)).
      { intros r' Hr'. destruct (decide (r' = reg)) as [->|Hne].
        - by rewrite !register_lookup_set.
        - rewrite !(irrelevant_register_set r' reg _ regval
                      (register_beq_false r' reg Hne)).
          by apply HagW. }
      assert (HagO' : reg_agree_on Dro rs (register_set reg regval rsM)).
      { intros r' Hr'.
        assert (Hne : r' <> reg) by (intros ->; by apply HrO).
        rewrite (irrelevant_register_set r' reg rsM regval
                   (register_beq_false r' reg Hne)).
        by apply HagO. }
      iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
      iExists (k tt), (MState (register_set reg regval rsM) mem0 dev0).
      iSplitR; [iPureIntro; split; reflexivity|].
      iNext. iIntros (m' σ') "%Hstep".
      destruct Hstep as [-> Hσ'].
      assert (σ' = MState (register_set reg regval rsM) mem0 dev0) as ->
        by exact Hσ'.
      iMod (hreg_frame_update rs Drw reg regval rsM Hns with "Hri Hrf")
        as "[Hri Hrf]".
      iMod "Hmask" as "_". iModIntro.
      iSplitR "H Hrf Hro"; [iFrame "Hri Hmem Hdev"|].
      iApply ("H" $! (k tt) rsM (register_set reg regval rsM)
                with "[%] [%] [Hrf] [Hro]").
      - exact Hag.
      - simpl. split; [exact Hns|reflexivity].
      - by iApply (hreg_frame_ext (register_set reg regval rs)
                     (register_set reg regval rsM) Drw HagW').
      - by iApply (hreg_frame_ro_ext_local Df rs (register_set reg regval rsM)
                     Dro HagO'). }
    (* RegRead and the silent classes: the file does not move *)
    all: iApply fupd_mask_intro; [apply empty_subseteq|]; iIntros "Hmask";
         iExists _, (MState rsM mem0 dev0);
         (iSplitR; [iPureIntro; split; reflexivity|]);
         iNext; iIntros (m' σ') "%Hstep";
         destruct Hstep as [-> ->];
         iMod "Hmask" as "_"; iModIntro;
         (iSplitR "H Hrf Hro"; [iFrame "Hri Hmem Hdev"|]);
         iApply ("H" $! _ rsM rsM with "[%] [%] [Hrf] [Hro]");
         [ exact Hag
         | simpl; reflexivity
         | by iApply (hreg_frame_ext rs rsM Drw HagW)
         | by iApply (hreg_frame_ro_ext_local Df rs rsM Dro HagO) ].
  Qed.

  (* helper: an [hspani] step's ∃rs1 only constrains the start file on
     [D], so the SAME step launches from any [D]-agreeing start file. *)
  Local Lemma hspani_shift_local (D Drw : gset register)
      (rsA rsB : regstate) (m : M unit) (c' : M unit * regstate) :
    reg_agree_on D rsA rsB ->
    hspani D Drw (m, rsA) c' -> hspani D Drw (m, rsB) c'.
  Proof.
    intros Hag (rs1 & Hag1 & Hnode). exists rs1. split; [|exact Hnode].
    intros r Hr. etrans; [exact (Hag1 r Hr)|exact (Hag r Hr)].
  Qed.

  (* helper: the span rule with the [Acc] argument explicit -- the
     well-founded induction lives here; [wp_hart_span] instantiates it
     with [macc m]. *)
  Local Lemma wp_hart_span_acc_local (Drw Dro : gset register)
      (Df : register -> dfrac) :
    Drw ## Dro ->
    forall m : M unit, Acc mchild m ->
    forall rs : regstate,
    hspan_stops Drw m = false ->
    ⊢ gen_cert -∗
      hreg_frame rs Drw -∗
      hreg_frame_ro Df rs Dro -∗
      ▷ (∀ (m' : M unit) (rs' : regstate),
           ⌜exists rs0 : regstate,
              reg_agree_on (Drw ∪ Dro) rs rs0 /\
              hspan (Drw ∪ Dro) Drw (m, rs0) (m', rs') /\
              hspan_stops Drw m' = true⌝ -∗
           hreg_frame rs' Drw -∗
           hreg_frame_ro Df rs' Dro -∗
           WP (HartE gen_id cpu_id m' : expr riscv_lang)) -∗
      WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    intros Hdisj m HAcc. induction HAcc as [m _ IH]. intros rs Hns.
    iIntros "#Hcert Hrf Hro Hcont".
    iApply (wp_hspan_node_local Drw Dro Df rs m Hdisj Hns
              with "Hcert Hrf Hro [Hcont]").
    iNext. iIntros (m2 rsM rs2) "%Hag %Hnode Hrf Hro".
    destruct (hspan_stops Drw m2) eqn:Hs2.
    - (* the successor stops: fire the continuation with a one-step chain *)
      iApply ("Hcont" $! m2 rs2 with "[%] Hrf Hro").
      exists rsM. split; [exact Hag|]. split; [|exact Hs2].
      apply rtc_once. exists rsM.
      split; [intros r' Hr'; reflexivity|exact Hnode].
    - (* still a span class: recurse on the subterm, prepending the step *)
      iApply (IH m2 (hspan_node_mchild Drw (m, rsM) (m2, rs2) Hnode) rs2 Hs2
                with "Hcert Hrf Hro [Hcont]").
      iNext. iIntros (m' rs') "%Hland Hrf Hro".
      iApply ("Hcont" $! m' rs' with "[%] Hrf Hro").
      destruct Hland as (rs0' & Hag' & Hchain & Hstop').
      apply rtc_inv in Hchain as [Heq|(cmid & Hfirst & Hrest)].
      { exfalso. injection Heq as <- <-. congruence. }
      exists rsM. split; [exact Hag|]. split; [|exact Hstop'].
      eapply rtc_l.
      { exists rsM. split; [intros r' Hr'; reflexivity|exact Hnode]. }
      eapply rtc_l; [|exact Hrest].
      apply (hspani_shift_local (Drw ∪ Dro) Drw rs0' rs2 m2 cmid);
        [intros r' Hr'; symmetry; exact (Hag' r' Hr')|exact Hfirst].
  Qed.

  (* ==================================================================== *)
  (* 4. THE SPAN RULE.                                                     *)
  (*                                                                       *)
  (* The caller supplies both frames anchored at ONE file [rs] (its own    *)
  (* certification file: the machine's file agrees with it on Drw ∪ Dro,   *)
  (* which is all the characterization lemma reads).  The continuation     *)
  (* receives EVERY stopped landing reachable through interfered span      *)
  (* steps from an agreeing start file, with both frames re-anchored at    *)
  (* the landing file.  [Drw ## Dro] keeps the ro-frame's values stable    *)
  (* (span writes are Drw-gated).                                          *)
  (*                                                                       *)
  (* The ▷ sits on the continuation ONCE: a span takes at least zero       *)
  (* steps, so the zero-step landing must be available immediately --       *)
  (* hence the ▷?-free hand-off below fires the continuation with the      *)
  (* later ONLY after at least one machine step; the stopped-immediately   *)
  (* case is the caller's to handle before applying the rule (its monad's  *)
  (* head is a stop class it would route to an event rule instead).  To    *)
  (* keep ONE rule, the premise [hspan_stops Drw m = false] excludes the   *)
  (* zero-step case: the span takes at least one step, so the whole        *)
  (* continuation sits under one ▷.                                        *)
  (* ==================================================================== *)
  Lemma wp_hart_span (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (m : M unit) :
    Drw ## Dro ->
    hspan_stops Drw m = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    ▷ (∀ (m' : M unit) (rs' : regstate),
         ⌜exists rs0 : regstate,
            reg_agree_on (Drw ∪ Dro) rs rs0 /\
            hspan (Drw ∪ Dro) Drw (m, rs0) (m', rs') /\
            hspan_stops Drw m' = true⌝ -∗
         hreg_frame rs' Drw -∗
         hreg_frame_ro Df rs' Dro -∗
         WP (HartE gen_id cpu_id m' : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    (* TODO(agent): by well-founded induction on [mchild_wf m] (e.g. [induction (macc m)]).
       Per step: [wp_hart_step]; the callback's σ gives the machine file;
       [hreg_frame_agree]/[hreg_frame_ro_agree] pin agreement on Drw/Dro;
       the node's head is [m]'s (concrete constructor —
       [hspan_stops Drw m = false] says it is a span class):
       - RegRead r: the machine's successor is [K (register_lookup r
         σ.(sregs))]; the witness and inversion are the deterministic
         RegRead arm of [mnode_step].  The span witness for the recursion:
         one [hspani] step whose [rs1] is σ's file (which agrees with the
         TRACKED [rs] on Drw ∪ Dro by the frames -- that is exactly
         [hspani]'s ∃rs1).
       - RegWrite r (r ∈ Drw by...): CAREFUL -- [hspan_stops m = false]
         gives [r ∈ Drw] via bool_decide; the frame updates as in
         [HartLift.wp_hsil_node]'s RegWrite case ([hreg_frame_update]);
         the ro-frame is untouched ([Drw ## Dro] keeps its lookups stable
         under [register_set r] via [irrelevant_register_set]).
       - silent-class nodes: state unchanged, frames re-anchored by
         [hreg_frame_ext] (lookups unchanged).
       After the step, the successor monad is a subterm ([hspan_node_mchild])
       -- if [hspan_stops Drw m' = true], fire the continuation with the
       one-step-chain witness; otherwise recurse by the induction
       hypothesis, PREPENDING the step to the recursive landing's chain
       (rtc_l), and re-anchoring both frames at the post file.
       The ▷-bookkeeping: the first machine step strips the continuation's
       ▷; recursive invocations pass it un-▷'d (the IH's continuation
       premise is under ▷ -- introduce it with [iNext] absorbed by the
       step's own later, exactly as [wp_hsil_rtc] does).
       CHAIN COMPOSITION CARE: the landing fact's start file [rs0] is the
       FIRST step's machine file; the recursive call's fact starts at the
       post-step file -- compose with [rtc_l] and transport the agreement
       ([reg_agree_on] is preserved by the step on Drw ∪ Dro: reads change
       nothing, Drw writes move both [rs] and the machine file in
       lock-step, so re-anchor [rs := post-write rs]). *)
    intros Hdisj Hns.
    exact (wp_hart_span_acc_local Drw Dro Df Hdisj m (macc m) rs Hns).
  Qed.

End span.
