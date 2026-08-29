(* HartSpanChar.v -- the CHAIN-PEELING kit for span characterizations
   (main-cycle-port.md, worklist item 0b).

   A class's characterization lemma ("every span chain from the M-mode
   prelude's monad with the config pinned lands at THE fetch node") is
   proven by peeling the chain one node at a time.  The peels below are
   the once-proven inversion steps; a class lemma chains ~100 of them.
   Three design rules, all measured:
     - pinned values enter as EXPLICIT arguments (a D-read peel concludes
       at [hregread_resume r (register_lookup r rs) m] where [rs] is the
       class's PIN FILE) -- no register-file tower is ever normalized
       (cbn stalls on tower lookups; lazy full-normalizes dead branches);
     - off-D reads peel to a ∀-binder (the class lemma's induction carries
       them; the landing is value-insensitive, so they die unused);
     - no peel ever names a continuation (finding F8): the successor is
       spelled through HartRegNode's projections ([hregread_resume],
       [hregwrite_resume]) and the unit-silent resume below. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode HartSpan.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The unit-silent projection: one resume covering every silent class   *)
(*    (announce/fence/cache/tlb/exception/translation/cycle/message, and   *)
(*    GetCycleCount with its 0).                                           *)
(* ====================================================================== *)

Definition husilent_resume {X : Type} (m : M X) : option (M X) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (M X) with
       | Interface.InstrAnnounce _    => fun k => Some (k tt)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt)
       | Interface.Barrier _          => fun k => Some (k tt)
       | Interface.CacheOp _          => fun k => Some (k tt)
       | Interface.TlbOp _            => fun k => Some (k tt)
       | Interface.TakeException _    => fun k => Some (k tt)
       | Interface.ReturnException _  => fun k => Some (k tt)
       | Interface.TranslationStart _ => fun k => Some (k tt)
       | Interface.TranslationEnd _   => fun k => Some (k tt)
       | Interface.CycleCount         => fun k => Some (k tt)
       | Interface.Message _          => fun k => Some (k tt)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z)
       | _ => fun _ => None
       end) k
  | _ => None
  end.

(* ====================================================================== *)
(* 2. The single-step peels: what one interfered span step from each node  *)
(*    class must be.                                                       *)
(* ====================================================================== *)

Lemma hspani_usilent_inv {X : Type} (D Drw : gset register) (m m2 : M X)
    (rs : regstate) (c : M X * regstate) :
  husilent_resume m = Some m2 ->
  hspani D Drw (m, rs) c ->
  exists rs1, reg_agree_on D rs1 rs /\ c = (m2, rs1).
Proof.
  (* TODO(agent): destruct m/oc; the projection pins the class; hspani's
     ∃rs1 gives the file; hspan_node's arm gives the successor. *)
  intros Hres (rs1 & Hag & Hnode).
  destruct m as [y|T oc k]; [discriminate Hres|].
  destruct oc; simpl in Hres; try discriminate Hres;
    injection Hres as <-; simpl in Hnode;
    exists rs1; (split; [exact Hag|exact Hnode]).
Qed.

(* a read of a register IN D: the value transports through the agreement,
   so the successor is the resume at the CHAIN-side file's value *)
Lemma hspani_read_D_inv {X : Type} (D Drw : gset register) (r : register)
    (m : M X) (rs : regstate) (c : M X * regstate) :
  hregread_at r m = true ->
  r ∈ D ->
  hspani D Drw (m, rs) c ->
  exists rs1, reg_agree_on D rs1 rs /\
       c = (hregread_resume r (register_lookup r rs) m, rs1).
Proof.
  (* TODO(agent): hregread_at_inv exposes the node; hspan_node's RegRead
     arm answers from rs1; rewrite the value via the agreement at r ∈ D. *)
  intros Hat Hr (rs1 & Hag & Hnode).
  destruct (hregread_at_inv r m Hat) as (ak & K & -> & Hres).
  cbn [hspan_node fst snd] in Hnode.
  assert (Hv : register_lookup r rs1 = register_lookup r rs)
    by (apply Hag; exact Hr).
  exists rs1. split; [exact Hag|].
  rewrite Hres. rewrite Hv in Hnode. exact Hnode.
Qed.

(* a read of a register OUTSIDE D: the value is arbitrary -- the ∀-binder
   the class lemma carries *)
Lemma hspani_read_any_inv {X : Type} (D Drw : gset register) (r : register)
    (m : M X) (rs : regstate) (c : M X * regstate) :
  hregread_at r m = true ->
  hspani D Drw (m, rs) c ->
  exists (v : type_of_register r) (rs1 : regstate),
    reg_agree_on D rs1 rs /\ c = (hregread_resume r v m, rs1).
Proof.
  (* TODO(agent): as above without the transport; v := the rs1-value. *)
  intros Hat (rs1 & Hag & Hnode).
  destruct (hregread_at_inv r m Hat) as (ak & K & -> & Hres).
  cbn [hspan_node fst snd] in Hnode.
  exists (register_lookup r rs1), rs1. split; [exact Hag|].
  rewrite Hres. exact Hnode.
Qed.

(* a write of a register in Drw: the successor file is the write applied
   to the (perturbed) chain file *)
Lemma hspani_write_inv {X : Type} (D Drw : gset register) (r : register)
    (v : type_of_register r) (m : M X) (rs : regstate)
    (c : M X * regstate) :
  hregwrite_val_at r m = Some v ->
  hspani D Drw (m, rs) c ->
  r ∈ Drw /\
  exists rs1, reg_agree_on D rs1 rs /\
       c = (hregwrite_resume m, register_set r v rs1).
Proof.
  (* TODO(agent): hregwrite_val_at_inv exposes the node; the span arm
     carries the Drw gate. *)
  intros Hat (rs1 & Hag & Hnode).
  destruct (hregwrite_val_at_inv r m v Hat) as (ak & K & -> & Hres).
  cbn [hspan_node fst snd] in Hnode. destruct Hnode as [Hin Hc].
  split; [exact Hin|]. exists rs1. split; [exact Hag|].
  rewrite Hres. exact Hc.
Qed.

(* ====================================================================== *)
(* 3. The chain-level steps.                                               *)
(* ====================================================================== *)

(* a chain from a STOPPED head is the empty chain *)
Lemma hspan_stop_refl {X : Type} (D Drw : gset register) (m : M X)
    (rs : regstate) (l : M X * regstate) :
  hspan_stops Drw m = true ->
  hspan D Drw (m, rs) l ->
  l = (m, rs).
Proof.
  (* TODO(agent): rtc_inv; a first step's hspan_node is refuted arm by arm
     from the stop classifier (Ret/Mem/Choose/fail arms are False; the
     RegWrite arm contradicts bool_decide (r ∉ Drw) = true). *)
  intros Hstop Hspan.
  apply rtc_inv in Hspan as [Heq|(c & Hstep & _)]; [symmetry; exact Heq|].
  exfalso. destruct Hstep as (rs1 & _ & Hnode).
  destruct m as [y|T oc k]; simpl in Hstop, Hnode; [exact Hnode|].
  destruct oc; simpl in Hstop, Hnode; try discriminate Hstop;
    try exact Hnode.
  destruct Hnode as [Hin _].
  apply bool_decide_eq_true_1 in Hstop. exact (Hstop Hin).
Qed.

(* a chain from a NON-stopped head to a stopped landing takes a first step *)
Lemma hspan_peel {X : Type} (D Drw : gset register) (m : M X)
    (rs : regstate) (l : M X * regstate) :
  hspan_stops Drw m = false ->
  hspan_stops Drw l.1 = true ->
  hspan D Drw (m, rs) l ->
  exists c, hspani D Drw (m, rs) c /\ hspan D Drw c l.
Proof.
  (* TODO(agent): rtc_inv; the refl case contradicts the two classifier
     facts. *)
  intros Hns Hstop Hspan.
  apply rtc_inv in Hspan as [Heq|(c & Hstep & Hrest)].
  - exfalso. rewrite <- Heq in Hstop. simpl in Hstop. congruence.
  - exists c. split; [exact Hstep|exact Hrest].
Qed.

(* ====================================================================== *)
(* 4. THE COMPUTATIONAL ROUTE INTO [hval].                                 *)
(*                                                                         *)
(* [HartSpan.hfrun] is the fuel-bounded walker that refuses whatever it is *)
(* not entitled to; this is the theorem that its success certifies EVERY   *)
(* interfered chain.  Note the absence of side conditions: the walker's    *)
(* own refusals stand in for the memory-freeness / write-freeness /        *)
(* state-preservation premises an [exec]-based bridge would have needed.   *)
(* ====================================================================== *)

Lemma hfrun_hval {X : Type} (n : nat) (D Drw : gset register) (rs : regstate)
    (m : M X) (x : X) (rs' : regstate) :
  hfrun n D Drw rs m = Some (x, rs') -> hval D Drw rs m x rs'.
Proof.
  revert rs m. induction n as [|n IH]; intros rs m Hf; [discriminate Hf|].
  intros rs0 l Hag0 Hchain Hstop.
  destruct m as [y|T oc k].
  - (* [Ret]: the chain is empty and the walker's answer is the file it
       was handed *)
    cbn in Hf. injection Hf as <- <-.
    assert (Hl : l = (Interface.Ret y, rs0))
      by (apply (hspan_stop_refl D Drw _ rs0 l); [reflexivity|exact Hchain]).
    rewrite Hl. cbn. split; [reflexivity|exact Hag0].
  - destruct oc; cbn in Hf; try discriminate Hf.
    1:{ (* REGISTER READ, pinned by [D]: interference cannot change the
         answer, so the machine's successor is the walker's *)
      destruct (bool_decide (reg ∈ D)) eqn:Hin; [|discriminate Hf].
      apply bool_decide_eq_true_1 in Hin.
      apply hspan_peel in Hchain; [|reflexivity|exact Hstop].
      destruct Hchain as (c1 & (rs1 & Hag1 & Hnode) & Hchain).
      cbn [hspan_node fst snd] in Hnode. subst c1.
      assert (Hvv : register_lookup reg rs1 = register_lookup reg rs)
        by (etrans; [exact (Hag1 reg Hin)|exact (Hag0 reg Hin)]).
      rewrite Hvv in Hchain.
      exact (IH rs (k (register_lookup reg rs)) Hf rs1 l
               (reg_agree_trans D rs1 rs0 rs Hag1 Hag0) Hchain Hstop). }
    1:{ (* REGISTER WRITE inside [Drw]: the tracked file and the machine's
         move in lock-step, so the agreement survives the write *)
      destruct (bool_decide (reg ∈ Drw)) eqn:Hin; [|discriminate Hf].
      apply bool_decide_eq_true_1 in Hin.
      assert (Hns : hspan_stops Drw
                      (Interface.Next (Interface.RegWrite reg access_kind
                                         regval) k) = false)
        by (cbn; apply bool_decide_eq_false_2; intros Hnin; exact (Hnin Hin)).
      apply hspan_peel in Hchain; [|exact Hns|exact Hstop].
      destruct Hchain as (c1 & (rs1 & Hag1 & Hnode) & Hchain).
      cbn [hspan_node fst snd] in Hnode. destruct Hnode as [_ ->].
      exact (IH (register_set reg regval rs) (k tt) Hf
               (register_set reg regval rs1) l
               (reg_agree_set D reg regval rs1 rs
                  (reg_agree_trans D rs1 rs0 rs Hag1 Hag0))
               Hchain Hstop). }
    (* the twelve silent classes: the file does not move *)
    all: apply hspan_peel in Hchain; [|reflexivity|exact Hstop];
           destruct Hchain as (c1 & (rs1 & Hag1 & Hnode) & Hchain);
           cbn [hspan_node fst snd] in Hnode; subst c1;
           first [ exact (IH rs (k tt) Hf rs1 l
                            (reg_agree_trans D rs1 rs0 rs Hag1 Hag0)
                            Hchain Hstop)
                 | exact (IH rs (k 0%Z) Hf rs1 l
                            (reg_agree_trans D rs1 rs0 rs Hag1 Hag0)
                            Hchain Hstop) ].
Qed.

(* the two routes into the proof interface, side by side: [swp_span] takes
   a hand-proven [hval] (the ∀-peeled, value-insensitive stretches);
   [swp_hfrun] takes a COMPUTED one, which is the whole of the batch story
   and the whole of the decode story *)
Section swp_hfrun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_hfrun {X : Type} (n : nat) (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : M X) (x : X) :
    Drw ## Dro ->
    hfrun n (Drw ∪ Dro) Drw rs m = Some (x, rs') ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp m (fun v => ⌜v = x⌝ ∗ hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj Hf.
    exact (swp_span Drw Dro Df rs rs' m x Hdisj
             (hfrun_hval n (Drw ∪ Dro) Drw rs m x rs' Hf)).
  Qed.

  (* the two rules that fire constantly: a read of a register the caller
     PINS (in either frame), and a write of one it OWNS.  Both are
     [swp_hfrun] at fuel 2 -- the walker is the whole proof. *)
  Lemma swp_read_reg_pinned (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (r : register) :
    Drw ## Dro ->
    r ∈ Drw ∪ Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (Defs.read_reg r)
      (fun v => ⌜v = register_lookup r rs⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj Hin.
    apply (swp_hfrun 2 Drw Dro Df rs rs (Defs.read_reg r)
             (register_lookup r rs) Hdisj).
    cbn. by rewrite (bool_decide_eq_true_2 _ Hin).
  Qed.

  Lemma swp_write_reg_owned (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (r : register)
      (v : type_of_register r) :
    Drw ## Dro ->
    r ∈ Drw ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (Defs.write_reg r v)
      (fun _ => hreg_frame (register_set r v rs) Drw ∗
                hreg_frame_ro Df (register_set r v rs) Dro).
  Proof.
    intros Hdisj Hin.
    iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]"); [|iApply (swp_hfrun 2 Drw Dro Df rs
      (register_set r v rs) (Defs.write_reg r v) tt Hdisj with
      "Hcert Hrw Hro")].
    { iIntros (u) "(_ & Hrw & Hro)". iFrame. }
    cbn. by rewrite (bool_decide_eq_true_2 _ Hin).
  Qed.

End swp_hfrun.
