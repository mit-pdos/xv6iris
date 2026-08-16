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
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The span step, pure layer.                                           *)
(* ====================================================================== *)

(* One MACHINE node of a span: reads ungated, writes gated on [Drw],
   silent-class nodes free; memory, device, Ret, Choose and out-of-[Drw]
   writes are NOT span steps -- they are where a span STOPS. *)
Definition hspan_node {X : Type} (Drw : gset register)
    (c c' : M X * regstate)
    : Prop :=
  match c.1 with
  | Interface.Ret _ => False
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
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
Definition hspani {X : Type} (D Drw : gset register)
    (c c' : M X * regstate)
    : Prop :=
  exists rs1 : regstate,
    reg_agree_on D rs1 c.2 /\ hspan_node Drw (c.1, rs1) c'.

Definition hspan {X : Type} (D Drw : gset register)
    : relation (M X * regstate) :=
  rtc (hspani D Drw).

(* Where a span stops: the node classes [hspan_node] refuses regardless of
   the file -- the boundary ([Ret]), a memory/device event, [Choose], a
   failure -- or a register WRITE outside [Drw].  This is a function of the
   monad's head alone, so the caller's characterization lemma can compute
   it. *)
Definition hspan_stops {X : Type} (Drw : gset register) (m : M X) : bool :=
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

(* ---------------------------------------------------------------------- *)
(* THE PURE CHARACTERIZATION A STRETCH EXPORTS, and the ONE shape every     *)
(* per-model-function lemma in this port is stated in.                      *)
(*                                                                          *)
(*   from any file agreeing with [rs] on [D], every maximal interfered      *)
(*   span chain of [m] lands at [Ret x], with a file agreeing with [rs']    *)
(*   on [D].                                                                *)
(*                                                                          *)
(* NO continuation, NO landing, NO context -- which is what makes it        *)
(* reusable at every call site and privilege mode, and what makes the       *)
(* tick-generic [KT] axis of the earlier characterizations unnecessary:     *)
(* what follows a sub-monad is not this lemma's business.  [swp_span]       *)
(* turns one of these into a [swp] fact; that is the only way stretches     *)
(* enter the proof interface.                                               *)
(* ---------------------------------------------------------------------- *)
Definition hval {X : Type} (D Drw : gset register) (rs : regstate)
    (m : M X) (x : X) (rs' : regstate) : Prop :=
  forall (rs0 : regstate) (l : M X * regstate),
    reg_agree_on D rs0 rs ->
    hspan D Drw (m, rs0) l ->
    hspan_stops Drw l.1 = true ->
    l.1 = Interface.Ret x /\ reg_agree_on D l.2 rs'.

Lemma reg_agree_refl (D : gset register) (rs : regstate) :
  reg_agree_on D rs rs.
Proof. intros r _. reflexivity. Qed.

Lemma reg_agree_trans (D : gset register) (rs1 rs2 rs3 : regstate) :
  reg_agree_on D rs1 rs2 -> reg_agree_on D rs2 rs3 -> reg_agree_on D rs1 rs3.
Proof. intros H1 H2 r Hr. etrans; [exact (H1 r Hr)|exact (H2 r Hr)]. Qed.

Lemma reg_agree_mono (D D' : gset register) (rs rs' : regstate) :
  D' ⊆ D -> reg_agree_on D rs rs' -> reg_agree_on D' rs rs'.
Proof. intros Hsub Hag r Hr. by apply Hag, Hsub. Qed.

Lemma reg_agree_set (D : gset register) (r : register)
    (v : type_of_register r) (rs rs' : regstate) :
  reg_agree_on D rs rs' ->
  reg_agree_on D (register_set r v rs) (register_set r v rs').
Proof.
  intros Hag r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite !register_lookup_set.
  - rewrite !(irrelevant_register_set r' r _ v (register_beq_false r' r Hne)).
    by apply Hag.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE COMPUTATIONAL ROUTE INTO [hval]: a fuel-bounded functional walker    *)
(* that REFUSES anything it is not entitled to.                            *)
(*                                                                          *)
(* It answers a register read from the tracked file only when the register  *)
(* is in [D] (so interference cannot change the answer), takes a register   *)
(* write only when the register is in [Drw] (so the caller owns it), passes *)
(* the silent classes, and stops at [Ret].  EVERYTHING ELSE IS [None]:      *)
(* memory, devices, [Choose], failures, a read it cannot pin, a write it    *)
(* cannot make.                                                             *)
(*                                                                          *)
(* Because the refusals are built in, [hfrun_hval] needs NO side condition  *)
(* -- no memory-freeness, no write-freeness, no state-preservation premise. *)
(* This one lemma covers both jobs the design doc gave to two mechanisms:   *)
(* the footprinted BATCH (a fully-owned stretch: the walker just runs it)   *)
(* and the DECODE bridge (a concrete word's decoder reads only config       *)
(* registers, all in the read-only frame, and returns the instruction) --   *)
(* so neither an [exec]-at-a-reference-state transport nor a [mem_free]     *)
(* obligation is needed.  What it does NOT cover is a stretch that reads    *)
(* registers OUTSIDE [D] (the M-mode prelude's ~54 unownable reads): there  *)
(* the landing is forced by VALUE-INSENSITIVITY, which is not computable    *)
(* and is what the ∀-peeled class characterizations prove by hand.          *)
(* ---------------------------------------------------------------------- *)
Fixpoint hfrun {X : Type} (n : nat) (D Drw : gset register) (rs : regstate)
    (m : M X) {struct n} : option (X * regstate) :=
  match n with
  | 0%nat => None
  | S n' =>
      match m with
      | Interface.Ret x => Some (x, rs)
      | Interface.Next oc k =>
          (match oc in Interface.outcome _ T
                 return (T -> M X) -> option (X * regstate) with
           | Interface.RegRead r _ => fun k =>
               if bool_decide (r ∈ D)
               then hfrun n' D Drw rs (k (register_lookup r rs))
               else None
           | Interface.RegWrite r _ v => fun k =>
               if bool_decide (r ∈ Drw)
               then hfrun n' D Drw (register_set r v rs) (k tt)
               else None
           | Interface.InstrAnnounce _    => fun k => hfrun n' D Drw rs (k tt)
           | Interface.BranchAnnounce _ _ => fun k => hfrun n' D Drw rs (k tt)
           | Interface.Barrier _          => fun k => hfrun n' D Drw rs (k tt)
           | Interface.CacheOp _          => fun k => hfrun n' D Drw rs (k tt)
           | Interface.TlbOp _            => fun k => hfrun n' D Drw rs (k tt)
           | Interface.TakeException _    => fun k => hfrun n' D Drw rs (k tt)
           | Interface.ReturnException _  => fun k => hfrun n' D Drw rs (k tt)
           | Interface.TranslationStart _ => fun k => hfrun n' D Drw rs (k tt)
           | Interface.TranslationEnd _   => fun k => hfrun n' D Drw rs (k tt)
           | Interface.CycleCount         => fun k => hfrun n' D Drw rs (k tt)
           | Interface.Message _          => fun k => hfrun n' D Drw rs (k tt)
           | Interface.GetCycleCount      => fun k => hfrun n' D Drw rs (k 0%Z)
           | _ => fun _ => None
           end) k
      end
  end.

(* THE REDUCTION EQUATIONS, and the trap they exist to avoid (measured):
   NEVER [cbn [... hfrun ...]] against a FOLDED model term.  To expose the
   [match m] scrutinee, cbn has to reduce [m] itself, and it does so with
   no regard for the whitelist -- [cbn [hfrun]] on
   [hfrun 6 D Drw rs (should_inc_minstret Machine)] does not finish in
   60 s, while the same goal with the spine pre-reduced and [hfrun] stepped
   by these equations is milliseconds.  This is the [hregread_resume_red]
   discipline again: reduce the SPINE with a whitelisted cbn, then step the
   walker one node at a time by [rewrite]. *)
Lemma hfrun_ret {X : Type} (n : nat) (D Drw : gset register)
    (rs : regstate) (x : X) :
  hfrun (S n) D Drw rs (Interface.Ret x) = Some (x, rs).
Proof. reflexivity. Qed.

Lemma hfrun_read {X : Type} (n : nat) (D Drw : gset register)
    (rs : regstate) (r : register) (ak : option unit)
    (k : type_of_register r -> M X) :
  hfrun (S n) D Drw rs (Interface.Next (Interface.RegRead r ak) k)
  = if bool_decide (r ∈ D)
    then hfrun n D Drw rs (k (register_lookup r rs))
    else None.
Proof. reflexivity. Qed.

Lemma hfrun_write {X : Type} (n : nat) (D Drw : gset register)
    (rs : regstate) (r : register) (ak : option unit)
    (v : type_of_register r) (k : unit -> M X) :
  hfrun (S n) D Drw rs (Interface.Next (Interface.RegWrite r ak v) k)
  = if bool_decide (r ∈ Drw)
    then hfrun n D Drw (register_set r v rs) (k tt)
    else None.
Proof. reflexivity. Qed.

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
Definition mchild {X : Type} (y m : M X) : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next _ k => exists v, y = k v
  end.

Fixpoint macc {X : Type} (m : M X) {struct m} : Acc mchild m.
Proof.
  constructor. intros y Hy. destruct m as [x|T oc k]; cbn in Hy.
  - destruct Hy.
  - destruct Hy as [v ->]. apply macc.
Defined.

Lemma mchild_wf {X : Type} : well_founded (@mchild X).
Proof. exact macc. Qed.

(* a span step descends the subterm order *)
Lemma hspan_node_mchild {X : Type} (Drw : gset register)
    (c c' : M X * regstate) :
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
     frames re-anchored at the landing file [rs2].

     STATED IN A CONTEXT [C] (HartSwp.mctx), at a sub-monad [m : M X]:
     that is what lets the SAME node proof serve [swp] facts about
     sub-monads at every type, including sub-monads sitting inside
     [run_hart_active]'s early-return region.  The pure side
     ([hspan_node]) stays about [m]'s OWN node -- the context is invisible
     to it, which is the whole point. *)
  Local Lemma wp_hspan_node_local {X : Type} (C : M X -> M unit)
      (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (m : M X) :
    mctx C ->
    Drw ## Dro ->
    hspan_stops Drw m = false ->
    ⊢ gen_cert -∗
      hreg_frame rs Drw -∗
      hreg_frame_ro Df rs Dro -∗
      ▷ (∀ (m2 : M X) (rsM rs2 : regstate),
           ⌜reg_agree_on (Drw ∪ Dro) rs rsM⌝ -∗
           ⌜hspan_node Drw (m, rsM) (m2, rs2)⌝ -∗
           hreg_frame rs2 Drw -∗
           hreg_frame_ro Df rs2 Dro -∗
           WP (HartE gen_id cpu_id (C m2) : expr riscv_lang)) -∗
      WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hdisj Hns) "#Hcert Hrf Hro H".
    destruct m as [y|T oc k]; [discriminate Hns|].
    assert (Hoc : is_extra oc = false)
      by (destruct oc; try reflexivity; discriminate Hns).
    rewrite (HC _ oc k Hoc).
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ". destruct σ as [rsM mem0 dev0].
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (hreg_frame_agree rs Drw rsM with "Hri Hrf") as %HagW.
    iDestruct (hreg_frame_ro_agree Df rs Dro rsM with "Hri Hro") as %HagO.
    assert (Hag : reg_agree_on (Drw ∪ Dro) rs rsM).
    { intros r' Hr'. apply elem_of_union in Hr' as [Hr'|Hr'];
        [by apply HagW|by apply HagO]. }
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
      iExists (C (k tt)), (MState (register_set reg regval rsM) mem0 dev0).
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
  Local Lemma hspani_shift_local {X : Type} (D Drw : gset register)
      (rsA rsB : regstate) (m : M X) (c' : M X * regstate) :
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
    iApply (wp_hspan_node_local (fun m' : M unit => m') Drw Dro Df rs m
              mctx_id Hdisj Hns with "Hcert Hrf Hro [Hcont]").
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

  (* ==================================================================== *)
  (* 5. THE SWP BRIDGE: a pure [hval] characterization becomes ONE [swp]   *)
  (*    fact about the sub-monad.                                          *)
  (*                                                                       *)
  (* This is where the landing-set quantifier dies for good.  [wp_hart_span]*)
  (* above hands its caller the whole relational landing set and makes the  *)
  (* caller kill it with a characterization at every use; here the          *)
  (* characterization is consumed ONCE, inside the induction, and what      *)
  (* comes out mentions neither chains nor files -- just the value and the  *)
  (* re-anchored frames.                                                    *)
  (* ==================================================================== *)

  Local Lemma reg_agree_refl_local (D : gset register) (rs : regstate) :
    reg_agree_on D rs rs.
  Proof. intros r _. reflexivity. Qed.

  Local Lemma reg_agree_mono_local (D D' : gset register) (rs rs' : regstate) :
    D' ⊆ D -> reg_agree_on D rs rs' -> reg_agree_on D' rs rs'.
  Proof. intros Hsub Hag r Hr. by apply Hag, Hsub. Qed.

  Local Lemma swp_span_acc_local {X : Type} (Drw Dro : gset register)
      (Df : register -> dfrac) :
    Drw ## Dro ->
    forall (m : M X), Acc mchild m ->
    forall (rs rs' : regstate) (x : X),
    hval (Drw ∪ Dro) Drw rs m x rs' ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp m (fun v => ⌜v = x⌝ ∗ hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj m HAcc. induction HAcc as [m _ IH]. intros rs rs' x Hval.
    iIntros "#Hcert Hrf Hro". rewrite /swp. iIntros (C) "%HC Hcont".
    destruct (hspan_stops Drw m) eqn:Hs.
    - (* THE STRETCH IS ALREADY OVER.  [hval] at the empty chain forces the
         head to be [Ret x] and the file to agree with [rs'] already. *)
      destruct (Hval rs (m, rs) (reg_agree_refl_local _ _)
                  (rtc_refl _ _) Hs) as [Hm Hag].
      simpl in Hm, Hag. rewrite Hm.
      iApply ("Hcont" $! x). iSplitR; [done|].
      iSplitL "Hrf".
      + iApply (hreg_frame_ext rs rs' Drw
                  (reg_agree_mono_local _ Drw _ _ (union_subseteq_l _ _) Hag)
                 with "Hrf").
      + iApply (hreg_frame_ro_ext_local Df rs rs' Dro
                  (reg_agree_mono_local _ Dro _ _ (union_subseteq_r _ _) Hag)
                 with "Hro").
    - (* A SPAN CLASS: take the node, transport the characterization across
         it, and recurse on the subterm. *)
      iApply (wp_hspan_node_local C Drw Dro Df rs m HC Hdisj Hs
                with "Hcert Hrf Hro [Hcont]").
      iNext. iIntros (m2 rsM rs2) "%Hag %Hnode Hrf Hro".
      (* THE TRANSPORT: a chain of [m2] from any file agreeing with [rs2]
         is a chain of [m] from [rs], one step longer.  The chain starts at
         an agreeing [rs0'] rather than at [rs2] itself, so its first step
         is shifted ([hspani] constrains its start file only on [D]); with
         no first step, the one-step chain to [(m2, rs2)] is the witness
         and the files compose. *)
      assert (Hval2 : hval (Drw ∪ Dro) Drw rs2 m2 x rs').
      { intros rs0' l Hag0' Hchain Hstop.
        assert (Hstep1 : hspani (Drw ∪ Dro) Drw (m, rs) (m2, rs2)).
        { exists rsM. split;
            [intros r Hr; symmetry; exact (Hag r Hr)|exact Hnode]. }
        apply rtc_inv in Hchain as [Heq|(cmid & Hfirst & Hrest)].
        - rewrite <- Heq. rewrite <- Heq in Hstop. simpl in Hstop |- *.
          destruct (Hval rs (m2, rs2) (reg_agree_refl_local _ _)
                      (rtc_once _ _ Hstep1) Hstop) as [Hm2 Hag2].
          simpl in Hm2, Hag2. split; [exact Hm2|].
          intros r Hr. etrans; [exact (Hag0' r Hr)|exact (Hag2 r Hr)].
        - assert (Hchain' : hspan (Drw ∪ Dro) Drw (m, rs) l).
          { eapply rtc_l; [exact Hstep1|].
            eapply rtc_l; [|exact Hrest].
            exact (hspani_shift_local (Drw ∪ Dro) Drw rs0' rs2 m2 cmid
                     Hag0' Hfirst). }
          exact (Hval rs l (reg_agree_refl_local _ _) Hchain' Hstop). }
      iApply (swp_use m2 _ C HC with "[Hrf Hro] Hcont").
      iApply (IH m2 (hspan_node_mchild Drw (m, rsM) (m2, rs2) Hnode)
                rs2 rs' x Hval2 with "Hcert Hrf Hro").
  Qed.

  (* THE BRIDGE.  [Drw] is the caller's exclusive footprint (the stretch may
     write it), [Dro] the dfrac-generic read-only frame (the config bundle);
     every OTHER register the stretch reads is answered by the machine and
     its value is irrelevant -- that is what [hval] proves once per class. *)
  Lemma swp_span {X : Type} (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : M X) (x : X) :
    Drw ## Dro ->
    hval (Drw ∪ Dro) Drw rs m x rs' ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp m (fun v => ⌜v = x⌝ ∗ hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj Hval.
    exact (swp_span_acc_local Drw Dro Df Hdisj m (macc m) rs rs' x Hval).
  Qed.

End span.
