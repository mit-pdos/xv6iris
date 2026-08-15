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
Require Import RiscvLang RiscvPtsto RiscvExec HartLift HartRegNode HartSpan.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The unit-silent projection: one resume covering every silent class   *)
(*    (announce/fence/cache/tlb/exception/translation/cycle/message, and   *)
(*    GetCycleCount with its 0).                                           *)
(* ====================================================================== *)

Definition husilent_resume (m : M unit) : option (M unit) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (M unit) with
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

Lemma hspani_usilent_inv (D Drw : gset register) (m m2 : M unit)
    (rs : regstate) (c : M unit * regstate) :
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
Lemma hspani_read_D_inv (D Drw : gset register) (r : register)
    (m : M unit) (rs : regstate) (c : M unit * regstate) :
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
Lemma hspani_read_any_inv (D Drw : gset register) (r : register)
    (m : M unit) (rs : regstate) (c : M unit * regstate) :
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
Lemma hspani_write_inv (D Drw : gset register) (r : register)
    (v : type_of_register r) (m : M unit) (rs : regstate)
    (c : M unit * regstate) :
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
Lemma hspan_stop_refl (D Drw : gset register) (m : M unit) (rs : regstate)
    (l : M unit * regstate) :
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
Lemma hspan_peel (D Drw : gset register) (m : M unit) (rs : regstate)
    (l : M unit * regstate) :
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
