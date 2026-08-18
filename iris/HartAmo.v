(* HartAmo.v -- the FUSED-AMO WP rule: exclusive read, silent window,
   conditional write, ONE step and hence ONE invariant access.  This is what
   keeps a lock acquire atomic in the logic (main-cycle-port.md §3, the
   MANDATORY fused window; the guard story lives with the language's arms in
   RiscvLang.v).

   THE VALUE-DEPENDENCE SHAPE.  A caller (an acquire) does not know the
   loaded value [w] until it opens its invariant -- so [w] is EXISTENTIAL
   inside the fupd, and everything downstream of the read is a FUNCTION of
   [w]: the window landing is [hsil k D (rs, hread_resume (bv_unsigned w) m)]
   and the write request is [wreq w].  The ∀-[w] premises say the window
   lands on a conditional write FOR EVERY value the read could return; for
   xv6's one atomic ([amoswap.w.aq]) the window is [rX rs2] plus pure
   arithmetic, so the landing shape (and [wreq]'s pa/value) is constant in
   [w] and the premises are uniform.  (An [amocas]-style instruction whose
   WINDOW SHAPE branches on the loaded value cannot satisfy them -- it does
   not take this rule; xv6 executes none.)

   THE CALLBACK IS MEMORY-ONLY: the rule itself owns the register side (the
   window's [hreg_frame D] transport, machine file included), frames the
   device fabric, and hands the caller exactly the byte-heap window --
   [gen_heap_interp mm] in, the written map out.  The caller's [read_bytes]
   witness both certifies the arm's ∃ and pins the machine's choice of [w]. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift HartLift2 HartSwp HartSpan.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The pure window layer: the footprinted functional walk against the    *)
(*    language's unfootprinted window relation ([silent1]/[silent_run]/     *)
(*    [wr_node], RiscvLang.v).                                              *)
(* ====================================================================== *)

(* soundness: a footprinted step IS a window step *)
Lemma hsil_node_silent1 (D : gset register) (rs rs' : regstate)
    (m m' : M unit) :
  hsil_node D rs m = Some (rs', m') -> silent1 (m, rs) (m', rs').
Proof.
  (* Proof plan: destruct on the node; every hsil_node arm is a silent1
     arm with the same successor (the D-gates only restrict, never alter). *)
  intros Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; by cbn.
Qed.

(* determinism: where the footprinted step is defined, the window relation
   has no other successor.  ([hsil_node] refuses [Choose], the one
   nondeterministic silent arm, so this holds arm by arm.) *)
Lemma hsil_node_silent1_det (D : gset register) (rs rs' : regstate)
    (m m' : M unit) (c' : M unit * regstate) :
  hsil_node D rs m = Some (rs', m') -> silent1 (m, rs) c' -> c' = (m', rs').
Proof.
  intros Hnode Hsil. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; cbn in Hsil; exact Hsil.
Qed.

(* the walk is a window run *)
Lemma hrun_silent_silent_run (k : nat) (D : gset register) (rs : regstate)
    (m : M unit) :
  silent_run (m, rs) ((hrun_silent k D rs m).2, (hrun_silent k D rs m).1).
Proof.
  (* Proof plan: induction on k; empty run when the node refuses. *)
  revert rs m. induction k as [|k IH]; intros rs m; simpl.
  - apply rtc_refl.
  - destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode.
    + eapply rtc_l; [exact (hsil_node_silent1 D rs rs1 m m1 Hnode)|].
      apply IH.
    + apply rtc_refl.
Qed.

(* the far end: a projected conditional write IS a [wr_node] *)
Lemma hwin_wr_node (nw : N) (wreq : Interface.WriteReq.t nw) (m1 : M unit)
    (mem : gmap Arch.pa (bv 8)) :
  hwrite_req_at nw m1 = Some wreq ->
  dev_addr (Interface.WriteReq.pa wreq) = false ->
  ak_excl (Interface.WriteReq.access_kind wreq) = true ->
  wr_node m1 mem
    (write_bytes mem (Interface.WriteReq.pa wreq) nw
       (Interface.WriteReq.value wreq))
    (hwrite_resume m1).
Proof.
  (* Proof plan: [hwrite_req_at_inv] exhibits the continuation; the
     wr_node record is then the guards + reflexivity. *)
  intros Hw Hd Hex.
  destruct (hwrite_req_at_inv nw m1 wreq Hw) as (K & -> & Hres).
  rewrite Hres. cbn. by split_and!.
Qed.

(* THE UNIQUENESS OF THE WINDOW: when the caller's walk lands on a
   conditional write, the machine's window (any [silent_run]+[wr_node]
   decomposition) is exactly that walk.  The induction pairs the fuel with
   the rtc: at each node either the walk is over (a [MemWrite] head, where
   [silent1] has no arm, so the machine chain must stop too) or the
   footprinted step succeeds (it must -- a refused node would strand the walk
   short of a [MemWrite] head, contradicting the projection premise) and
   [hsil_node_silent1_det] forces the machine's step to match. *)
Lemma hwin_unique (k : nat) (D : gset register) (rs0 : regstate)
    (m0 : M unit) (nw : N) (wreq : Interface.WriteReq.t nw)
    (mem mem1 : gmap Arch.pa (bv 8)) (m1 m2 : M unit) (rs1 : regstate) :
  hwrite_req_at nw (hrun_silent k D rs0 m0).2 = Some wreq ->
  silent_run (m0, rs0) (m1, rs1) ->
  wr_node m1 mem mem1 m2 ->
  m1 = (hrun_silent k D rs0 m0).2 /\ rs1 = (hrun_silent k D rs0 m0).1 /\
  mem1 = write_bytes mem (Interface.WriteReq.pa wreq) nw
           (Interface.WriteReq.value wreq) /\
  m2 = hwrite_resume m1.
Proof.
  (* Proof plan: revert everything, induct on k with the rtc inverted per
     step ([rtc_inv]).  Key case facts:
     - if [hsil_node D rs0 m0 = None] and the walk still landed on a write,
       then [hrun_silent k D rs0 m0 = (rs0, m0)] and [m0] itself is the
       [MemWrite]; then [silent1 (m0, rs0) _] is False (no MemWrite arm),
       so the machine chain is refl and [wr_node]'s components compute via
       [hwrite_req_at_inv].
     - if [hsil_node D rs0 m0 = Some (rsx, mx)]: [m0] is a silent-class
       node, so [wr_node m0 ...] is False (chain cannot stop here), the
       machine chain is nonempty, its head equals [(mx, rsx)] by
       [hsil_node_silent1_det], and the IH (at k-1... careful: fuel k
       decrements on the Some branch of hrun_silent) closes it.
     - k = 0: [hrun_silent 0 D rs0 m0 = (rs0, m0)], same as the None case. *)
  revert rs0 m0. induction k as [|k IH]; intros rs0 m0 Hproj Hrun Hwr.
  - simpl in Hproj |- *.
    destruct (hwrite_req_at_inv nw m0 wreq Hproj) as (K & -> & Hres).
    apply rtc_inv in Hrun as [Heq | ([mc rsc] & Hstep & _)];
      [|by cbn in Hstep].
    injection Heq as Hm1 Hrs1. subst m1 rs1.
    cbn in Hwr. destruct Hwr as (Hd & Hex & Hmem1 & Hm2).
    split_and!; [reflexivity|reflexivity|exact Hmem1|].
    rewrite Hres. exact Hm2.
  - simpl in Hproj |- *.
    destruct (hsil_node D rs0 m0) as [[rsx mx]|] eqn:Hnode.
    + apply rtc_inv in Hrun as [Heq | ([mc rsc] & Hstep & Hrun')].
      * (* chain cannot stop at a silent-class node *)
        exfalso. injection Heq as Hm1 Hrs1. subst m1.
        destruct m0 as [y|T oc kk]; [by cbn in Hwr|].
        destruct oc; try (by cbn in Hwr); simpl in Hnode; discriminate Hnode.
      * pose proof (hsil_node_silent1_det D rs0 rsx m0 mx (mc, rsc)
                      Hnode Hstep) as Hc.
        injection Hc as -> ->.
        exact (IH rsx mx Hproj Hrun' Hwr).
    + destruct (hwrite_req_at_inv nw m0 wreq Hproj) as (K & -> & Hres).
      apply rtc_inv in Hrun as [Heq | ([mc rsc] & Hstep & _)];
        [|by cbn in Hstep].
      injection Heq as Hm1 Hrs1. subst m1 rs1.
      cbn in Hwr. destruct Hwr as (Hd & Hex & Hmem1 & Hm2).
      split_and!; [reflexivity|reflexivity|exact Hmem1|].
      rewrite Hres. exact Hm2.
Qed.

(* the agreement transport, functional both sides: two files agreeing on
   [D] walk to the SAME monad, with files still agreeing on [D].  Total --
   no success hypothesis -- because a refusal is simultaneous on both sides
   (the refusing node's class or D-membership is file-independent, and a
   [RegRead]'s answer only differs off [D]). *)
Lemma hrun_silent_agree (k : nat) (D : gset register) (rs rs0 : regstate)
    (m : M unit) :
  reg_agree_on D rs rs0 ->
  (hrun_silent k D rs0 m).2 = (hrun_silent k D rs m).2 /\
  reg_agree_on D (hrun_silent k D rs m).1 (hrun_silent k D rs0 m).1.
Proof.
  (* Proof plan: induction on k over [hsil_node_agree] (HartLift.v); note
     hsil_node_agree is stated caller→machine, match directions carefully. *)
  revert rs rs0 m. induction k as [|k IH]; intros rs rs0 m Hag.
  - simpl. by split.
  - simpl. destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode1.
    + destruct (hsil_node_agree D rs rs0 m m1 rs1 Hag Hnode1)
        as (rs2 & Hnode2 & Hag').
      rewrite Hnode2. exact (IH rs1 rs2 m1 Hag').
    + destruct (hsil_node D rs0 m) as [[rs2 m2]|] eqn:Hnode2.
      * exfalso.
        assert (Hag' : reg_agree_on D rs0 rs).
        { intros r Hr. symmetry. by apply Hag. }
        destruct (hsil_node_agree D rs0 rs m m2 rs2 Hag' Hnode2)
          as (rs3 & Hnode3 & _).
        rewrite Hnode1 in Hnode3. discriminate Hnode3.
      * by split.
Qed.

(* ====================================================================== *)
(* 2. The ghost transport: update the register bridge and the caller's      *)
(*    frame along the walk, in one bupd.                                    *)
(* ====================================================================== *)



(* ---------------------------------------------------------------------- *)
(* THE TWO WALKERS MEET.  [hsil] is the wp layer's DETERMINISTIC silent      *)
(* walk; [hspan] is the swp layer's INTERFERED one, and the port's whole     *)
(* bridge machinery ([hval], [hfrun], [swp_span]) is built on the latter.    *)
(* Every [hsil] step is an [hspan] step -- [hsil_node]'s guards are strictly *)
(* stronger ([hspan_node] reads any register; [hsil_node] wants it in [D])   *)
(* and interference is satisfied reflexively -- so a characterization proved *)
(* the swp way applies to the deterministic walk the fused rule names.       *)
(* ---------------------------------------------------------------------- *)
Lemma hsil_node_hspani {X : Type} (D : gset register) (rs rs' : regstate)
    (m m' : M X) :
  hsil_node D rs m = Some (rs', m') -> hspani D D (m, rs) (m', rs').
Proof.
  intros Hnode. exists rs. split; [intros r _; reflexivity|].
  destruct m as [y | T oc k]; [by cbn in Hnode|].
  destruct oc; cbn in Hnode |- *; try discriminate Hnode;
    first
      [ (case_decide as HrD; [|discriminate Hnode];
         injection Hnode as <- <-; split; [exact HrD | reflexivity])
      | (case_decide as HrD; [|discriminate Hnode];
         injection Hnode as <- <-; reflexivity)
      | (injection Hnode as <- <-; reflexivity) ].
Qed.

Lemma hsil_hspan {X : Type} (D : gset register) (k : nat) (rs : regstate)
    (m : M X) :
  hspan D D (m, rs) ((hsil k D (rs, m)).2, (hsil k D (rs, m)).1).
Proof.
  revert rs m. induction k as [|k IH]; intros rs m; [reflexivity|].
  cbn [hsil hrun_silent fst snd].
  destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode; [|reflexivity].
  eapply rtc_l; [exact (hsil_node_hspani D rs rs1 m m1 Hnode)|].
  exact (IH rs1 m1).
Qed.

(* ====================================================================== *)
(* 0. THE CONTEXT COMMUTATION, which is what lets the fused rule be used    *)
(*    under [swp].                                                         *)
(*                                                                        *)
(* [swp]'s context [C] is ∀-bound and opaque, so the fused rule's window    *)
(* premise -- stated about [hsil … (C m)] -- has to be discharged from a    *)
(* fact about the inner [m].  [mctx C] commutes with the head node and      *)
(* [hsil_node] looks ONLY at the head node, so the two line up exactly;     *)
(* what made this unstateable before was [hsil] being pinned at [M unit],   *)
(* which [HartLift] now generalizes.                                       *)
(* ====================================================================== *)

(* the terms a context is NOT constrained on: [mctx] says nothing about
   [C (Ret x)] (deliberately -- that is the continuation) and nothing about
   an [ExtraOutcome] (a [catch_early_return] context genuinely transforms
   one).  A window that passes through neither commutes. *)
Definition hsil_opaque {X : Type} (m : M X) : bool :=
  match m with
  | Interface.Ret _ => true
  | Interface.Next oc _ => is_extra oc
  end.

Lemma hsil_node_mctx {X : Type} (C : M X -> M unit) (D : gset register)
    (rs rs' : regstate) (m m' : M X) :
  mctx C ->
  hsil_node D rs m = Some (rs', m') ->
  hsil_node D rs (C m) = Some (rs', C m').
Proof.
  intros HC Hnode. destruct m as [y | T oc k]; [by simpl in Hnode|].
  assert (Hx : is_extra oc = false)
    by (destruct oc; cbn in Hnode |- *; try reflexivity; discriminate Hnode).
  rewrite (HC T oc k Hx).
  destruct oc; cbn in Hnode |- *; try discriminate Hnode;
    repeat (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; reflexivity.
Qed.

(* a STUCK inner node stays stuck under the context, provided it is one of
   the nodes [mctx] speaks about *)
Lemma hsil_node_mctx_none {X : Type} (C : M X -> M unit) (D : gset register)
    (rs : regstate) (m : M X) :
  mctx C ->
  hsil_opaque m = false ->
  hsil_node D rs m = None ->
  hsil_node D rs (C m) = None.
Proof.
  intros HC Hop Hnode. destruct m as [y | T oc k]; [by cbn in Hop|].
  cbn in Hop. rewrite (HC T oc k Hop).
  destruct oc; cbn in Hnode |- *;
    first [ discriminate Hop
          | (case_decide; [discriminate Hnode | reflexivity])
          | discriminate Hnode
          | reflexivity ].
Qed.

(* ...and the iteration.  The side condition is the honest one and it is met
   by the A/D write-back's window, which passes through register reads and
   ends on the conditional write node -- never a [Ret], never an early
   return. *)
Lemma hsil_mctx {X : Type} (C : M X -> M unit) (D : gset register)
    (k : nat) (rs : regstate) (m : M X) :
  mctx C ->
  (forall j : nat, (j < k)%nat -> hsil_opaque ((hsil j D (rs, m)).2) = false) ->
  hsil k D (rs, C m) = ((hsil k D (rs, m)).1, C ((hsil k D (rs, m)).2)).
Proof.
  intros HC. revert rs m. induction k as [|k IH]; intros rs m Hnr.
  - reflexivity.
  - assert (Hop0 : hsil_opaque m = false)
      by (specialize (Hnr 0%nat ltac:(lia)); cbn in Hnr; exact Hnr).
    cbn [hsil hrun_silent] in *.
    destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode.
    + cbn [fst snd] in *. rewrite Hnode.
      rewrite (hsil_node_mctx C D rs rs1 m m1 HC Hnode).
      change (hrun_silent k D rs1 (C m1)) with (hsil k D (rs1, C m1)).
      change (hrun_silent k D rs1 m1) with (hsil k D (rs1, m1)).
      apply (IH rs1 m1).
      intros j Hj. specialize (Hnr (S j) ltac:(lia)).
      cbn [hsil hrun_silent] in Hnr. rewrite Hnode in Hnr. exact Hnr.
    + cbn [fst snd] in *. rewrite Hnode.
      rewrite (hsil_node_mctx_none C D rs m HC Hop0 Hnode). reflexivity.
Qed.


(* ---- the same two facts at the TWO-footprint walker, which is the one the
   swp layer's frame split can supply.  [hsil2] reads from [Drw ∪ Dro] and
   writes only in [Drw], so its [hspan] instance is [hspan (Drw ∪ Dro) Drw]. *)

Lemma hsil_node2_hspani {X : Type} (Drw Dro : gset register)
    (rs rs' : regstate) (m m' : M X) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  hspani (Drw ∪ Dro) Drw (m, rs) (m', rs').
Proof.
  intros Hnode. exists rs. split; [intros r _; reflexivity|].
  destruct m as [y | T oc k]; [by cbn in Hnode|].
  destruct oc; cbn in Hnode |- *; try discriminate Hnode;
    first
      [ (case_decide as HrD; [|discriminate Hnode];
         injection Hnode as <- <-; split; [exact HrD | reflexivity])
      | (case_decide as HrD; [|discriminate Hnode];
         injection Hnode as <- <-; reflexivity)
      | (injection Hnode as <- <-; reflexivity) ].
Qed.

Lemma hsil2_hspan {X : Type} (Drw Dro : gset register) (k : nat)
    (rs : regstate) (m : M X) :
  hspan (Drw ∪ Dro) Drw (m, rs)
    ((hsil2 k Drw Dro (rs, m)).2, (hsil2 k Drw Dro (rs, m)).1).
Proof.
  revert rs m. induction k as [|k IH]; intros rs m; [reflexivity|].
  cbn [hsil2 hrun_silent2 fst snd].
  destruct (hsil_node2 Drw Dro rs m) as [[rs1 m1]|] eqn:Hnode; [|reflexivity].
  eapply rtc_l; [exact (hsil_node2_hspani Drw Dro rs rs1 m m1 Hnode)|].
  exact (IH rs1 m1).
Qed.

Lemma hsil_node2_mctx {X : Type} (C : M X -> M unit) (Drw Dro : gset register)
    (rs rs' : regstate) (m m' : M X) :
  mctx C ->
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  hsil_node2 Drw Dro rs (C m) = Some (rs', C m').
Proof.
  intros HC Hnode. destruct m as [y | T oc k]; [by simpl in Hnode|].
  assert (Hx : is_extra oc = false)
    by (destruct oc; cbn in Hnode |- *; try reflexivity; discriminate Hnode).
  rewrite (HC T oc k Hx).
  destruct oc; cbn in Hnode |- *; try discriminate Hnode;
    repeat (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; reflexivity.
Qed.

Lemma hsil_node2_mctx_none {X : Type} (C : M X -> M unit)
    (Drw Dro : gset register) (rs : regstate) (m : M X) :
  mctx C ->
  hsil_opaque m = false ->
  hsil_node2 Drw Dro rs m = None ->
  hsil_node2 Drw Dro rs (C m) = None.
Proof.
  intros HC Hop Hnode. destruct m as [y | T oc k]; [by cbn in Hop|].
  cbn in Hop. rewrite (HC T oc k Hop).
  destruct oc; cbn in Hnode |- *;
    first [ discriminate Hop
          | (case_decide; [discriminate Hnode | reflexivity])
          | discriminate Hnode
          | reflexivity ].
Qed.

Lemma hsil2_mctx {X : Type} (C : M X -> M unit) (Drw Dro : gset register)
    (k : nat) (rs : regstate) (m : M X) :
  mctx C ->
  (forall j : nat, (j < k)%nat ->
     hsil_opaque ((hsil2 j Drw Dro (rs, m)).2) = false) ->
  hsil2 k Drw Dro (rs, C m)
  = ((hsil2 k Drw Dro (rs, m)).1, C ((hsil2 k Drw Dro (rs, m)).2)).
Proof.
  intros HC. revert rs m. induction k as [|k IH]; intros rs m Hnr.
  - reflexivity.
  - assert (Hop0 : hsil_opaque m = false)
      by (specialize (Hnr 0%nat ltac:(lia)); cbn in Hnr; exact Hnr).
    cbn [hsil2 hrun_silent2 fst snd] in *.
    destruct (hsil_node2 Drw Dro rs m) as [[rs1 m1]|] eqn:Hnode.
    + rewrite (hsil_node2_mctx C Drw Dro rs rs1 m m1 HC Hnode).
      change (hrun_silent2 k Drw Dro rs1 (C m1))
        with (hsil2 k Drw Dro (rs1, C m1)).
      change (hrun_silent2 k Drw Dro rs1 m1) with (hsil2 k Drw Dro (rs1, m1)).
      apply (IH rs1 m1).
      intros j Hj. specialize (Hnr (S j) ltac:(lia)).
      cbn [hsil2 hrun_silent2 fst snd] in Hnr. rewrite Hnode in Hnr. exact Hnr.
    + rewrite (hsil_node2_mctx_none C Drw Dro rs m HC Hop0 Hnode). reflexivity.
Qed.

Section amo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma hreg_frame_update_run (k : nat) (D : gset register)
      (rs rs0 : regstate) (m : M unit) :
    reg_agree_on D rs rs0 ->
    reg_interp rs0 -∗ hreg_frame rs D ==∗
    reg_interp (hrun_silent k D rs0 m).1 ∗
    hreg_frame (hrun_silent k D rs m).1 D.
  Proof.
    (* Proof plan: induction on k; per node, RegWrite goes through
       [hreg_frame_update], everything else [hreg_frame_ext]; the two sides
       stay in lock-step by [hsil_node_agree]. *)
    revert rs rs0 m. induction k as [|k IH]; intros rs rs0 m Hag.
    - assert (HL : (hrun_silent 0 D rs m).1 = rs) by reflexivity.
      assert (HM : (hrun_silent 0 D rs0 m).1 = rs0) by reflexivity.
      rewrite HL HM. iIntros "Hi Hf". iModIntro. by iFrame.
    - destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode1.
      + destruct (hsil_node_agree D rs rs0 m m1 rs1 Hag Hnode1)
          as (rs2 & Hnode2 & Hag').
        assert (HL : (hrun_silent (S k) D rs m).1
                     = (hrun_silent k D rs1 m1).1)
          by (simpl; by rewrite Hnode1).
        assert (HM : (hrun_silent (S k) D rs0 m).1
                     = (hrun_silent k D rs2 m1).1)
          by (simpl; by rewrite Hnode2).
        rewrite HL HM. iIntros "Hi Hf".
        iAssert (|==> reg_interp rs2 ∗ hreg_frame rs1 D)%I
          with "[Hi Hf]" as ">[Hi Hf]".
        { destruct m as [y|T oc kk]; [by simpl in Hnode1|].
          destruct oc; simpl in Hnode1; try discriminate Hnode1;
            first
              [ (* RegWrite *)
                case_decide as HrD; [|discriminate Hnode1];
                injection Hnode1 as Hq1 Hq2; simpl in Hnode2;
                case_decide; [|discriminate Hnode2];
                injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
                iMod (hreg_frame_update rs D _ regval rs0 HrD
                        with "Hi Hf") as "[Hi Hf]";
                iModIntro; by iFrame "Hi Hf"
              | (* RegRead: the file does not move *)
                case_decide as HrD; [|discriminate Hnode1];
                injection Hnode1 as Hq1 Hq2; simpl in Hnode2;
                case_decide; [|discriminate Hnode2];
                injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
                iModIntro; iFrame "Hi"; by iApply (hreg_frame_ext rs rs D)
              | injection Hnode1 as Hq1 Hq2; simpl in Hnode2;
                injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
                iModIntro; iFrame "Hi";
                by iApply (hreg_frame_ext rs rs D) ]. }
        by iApply (IH rs1 rs2 m1 Hag' with "Hi Hf").
      + destruct (hsil_node D rs0 m) as [[rs2 m2]|] eqn:Hnode2.
        * exfalso.
          assert (Hag' : reg_agree_on D rs0 rs).
          { intros r Hr. symmetry. by apply Hag. }
          destruct (hsil_node_agree D rs0 rs m m2 rs2 Hag' Hnode2)
            as (rs3 & Hnode3 & _).
          rewrite Hnode1 in Hnode3. discriminate Hnode3.
        * assert (HL : (hrun_silent (S k) D rs m).1 = rs)
            by (simpl; by rewrite Hnode1).
          assert (HM : (hrun_silent (S k) D rs0 m).1 = rs0)
            by (simpl; by rewrite Hnode2).
          rewrite HL HM. iIntros "Hi Hf". iModIntro. by iFrame.
  Qed.


  (* ---- transporting the fused rule's premises through a context ---- *)

  Lemma hread_req_at_mctx {X : Type} (C : M X -> M unit) (n : N)
      (m : M X) (req : Interface.ReadReq.t n) :
    mctx C ->
    hread_req_at n m = Some req ->
    hread_req_at n (C m) = Some req.
  Proof.
    intros HC Hn.
    destruct (hread_req_at_inv n m req Hn) as (K & Hm & _).
    rewrite Hm (HC _ (Interface.MemRead n req) K eq_refl).
    cbn [hread_req_at].
    destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
    assert (Heq = eq_refl) as -> by apply proof_irrel.
    reflexivity.
  Qed.

  Lemma hread_resume_mctx {X : Type} (C : M X -> M unit) (n : N)
      (m : M X) (req : Interface.ReadReq.t n) (v : Z) :
    mctx C ->
    hread_req_at n m = Some req ->
    hread_resume v (C m) = C (hread_resume v m).
  Proof.
    intros HC Hn.
    destruct (hread_req_at_inv n m req Hn) as (K & Hm & _).
    rewrite Hm (HC _ (Interface.MemRead n req) K eq_refl).
    cbn [hread_resume]. reflexivity.
  Qed.

  Lemma hwrite_req_at_mctx {X : Type} (C : M X -> M unit) (n : N)
      (m : M X) (req : Interface.WriteReq.t n) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    hwrite_req_at n (C m) = Some req.
  Proof.
    intros HC Hn.
    destruct (hwrite_req_at_inv n m req Hn) as (K & Hm & _).
    rewrite Hm (HC _ (Interface.MemWrite n req) K eq_refl).
    cbn [hwrite_req_at].
    destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
    assert (Heq = eq_refl) as -> by apply proof_irrel.
    reflexivity.
  Qed.

  Lemma hwrite_resume_mctx {X : Type} (C : M X -> M unit) (n : N)
      (m : M X) (req : Interface.WriteReq.t n) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    hwrite_resume (C m) = C (hwrite_resume m).
  Proof.
    intros HC Hn.
    destruct (hwrite_req_at_inv n m req Hn) as (K & Hm & _).
    rewrite Hm (HC _ (Interface.MemWrite n req) K eq_refl).
    cbn [hwrite_resume]. reflexivity.
  Qed.

  (* ==================================================================== *)
  (* 3. THE RULE.                                                          *)
  (* ==================================================================== *)

  Lemma wp_hart_amo (D : gset register) (k : nat) (n : N)
      (req : Interface.ReadReq.t n) (m : M unit) (rs : regstate)
      (nw : N) (wreq : bv (8 * n) -> Interface.WriteReq.t nw) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    hreg_frame rs D -∗
    (* THE WINDOW IS CERTIFIED AT THE ACTUAL READ VALUE, not for every
       possible one.  Stating it as [forall w] up front is too strong to be
       dischargeable by the one caller this rule exists for: the A/D
       write-back runs [check_leaf_pte] on the RE-READ word, and a word that
       fails its checks EARLY-RETURNS, so for such a [w] the walk never
       reaches the conditional write and [hwrite_req_at] is [None].  The exec
       side has the same shape for the same reason -- [PtTreeAdue.
       exec_translate_TLB_hit_pt_upd] takes the re-read word as a BINDER and
       pins it with its check premises. *)
    (∀ mm : gmap Arch.pa (bv 8), gen_heap_interp mm ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes mm (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ⌜hwrite_req_at nw
            (hsil k D (rs, hread_resume (bv_unsigned w) m)).2 = Some (wreq w)⌝ ∗
         ⌜dev_addr (Interface.WriteReq.pa (wreq w)) = false⌝ ∗
         ⌜ak_excl (Interface.WriteReq.access_kind (wreq w)) = true⌝ ∗
         ▷ (|={∅,⊤}=> gen_heap_interp
                (write_bytes mm (Interface.WriteReq.pa (wreq w)) nw
                   (Interface.WriteReq.value (wreq w))) ∗
              (hreg_frame
                 (hsil k D (rs, hread_resume (bv_unsigned w) m)).1 D -∗
               WP (HartE gen_id cpu_id
                     (hwrite_resume
                        (hsil k D (rs, hread_resume (bv_unsigned w) m)).2)
                   : expr riscv_lang)))) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step.  Sketch:
       - destruct σ as [rsM memM devM]; split mstate_interp; feed [memM] to
         the caller's fupd; obtain w + the read_bytes fact + continuation.
       - [hread_req_at_inv] gives m = Next (MemRead n req) K and
         hread_resume (bv_unsigned w) m = K (inl (w, None)) =: m0.
       - THE WITNESS: the fused arm at w, with
         silent_run  := [hrun_silent_silent_run k D rsM m0],
         wr_node     := [hwin_wr_node] at the MACHINE landing -- whose monad
         equals the caller-side landing by [hrun_silent_agree] (the files
         agree on D by [hreg_frame_agree]) -- and the byte lookups from
         [read_bytes_spec].
       - THE INVERSION (∀ successors): the arm's w' equals w by
         [read_bytes_spec] + [bv_eq_of_bytes]; then [hwin_unique] (at the
         machine file) pins (m1, rs1, mem1, m'); rewrite the machine landing
         monad to the caller-side one by [hrun_silent_agree].
       - ghost: [hreg_frame_update_run] moves the register bridge to the
         machine landing file and the caller's frame to the caller landing
         file; the caller's continuation supplies the written byte heap;
         [dev_interp] is framed.
       - re-assemble mstate_interp (MState (machine landing).1 written devM). *)
    intros Hrd Hdva Hex.
    destruct (hread_req_at_inv n m req Hrd) as (K & -> & Hres).
    iIntros "#Hcert Hrf Hcb".
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ". destruct σ as [rsM memM devM].
    iDestruct "Hσ" as "(Hri & Hmem & Hdv)".
    iDestruct (hreg_frame_agree rs D rsM with "Hri Hrf") as %Hag.
    iMod ("Hcb" $! memM with "Hmem") as (w) "(%Hrb & %HwinW1 & %Hwdev1 & %Hwex1 & Hk)".
    (* normalise the caller-side landing to hrun_silent form *)
    assert (Hhsil : hsil k D (rs, K (inl (w, None)))
                    = hrun_silent k D rs (K (inl (w, None)))) by reflexivity.
    iEval (rewrite (Hres w) Hhsil) in "Hk".
    pose proof HwinW1 as HwinW.
    rewrite (Hres w) Hhsil in HwinW.
    destruct (hrun_silent_agree k D rs rsM (K (inl (w, None))) Hag)
      as [Hmeq _].
    pose proof HwinW as HwinM. rewrite -Hmeq in HwinM.
    pose proof (read_bytes_spec memM (Interface.ReadReq.pa req) n w Hrb)
      as Hbytes.
    pose proof (hrun_silent_silent_run k D rsM (K (inl (w, None)))) as HsilM.
    pose proof (hwin_wr_node nw (wreq w)
                  (hrun_silent k D rsM (K (inl (w, None)))).2 memM
                  HwinM Hwdev1 Hwex1) as HwrM.
    iModIntro.
    iExists (hwrite_resume (hrun_silent k D rsM (K (inl (w, None)))).2),
      (MState (hrun_silent k D rsM (K (inl (w, None)))).1
         (write_bytes memM (Interface.WriteReq.pa (wreq w)) nw
            (Interface.WriteReq.value (wreq w))) devM).
    iSplitR.
    { iPureIntro. simpl. rewrite Hdva. right.
      split; [exact Hex|].
      exists w, (hrun_silent k D rsM (K (inl (w, None)))).2,
        (hrun_silent k D rsM (K (inl (w, None)))).1,
        (write_bytes memM (Interface.WriteReq.pa (wreq w)) nw
           (Interface.WriteReq.value (wreq w))).
      split_and!; [exact Hbytes|exact HsilM|exact HwrM|reflexivity]. }
    iNext. iIntros (m' σ') "%Hstep".
    simpl in Hstep. rewrite Hdva in Hstep.
    destruct Hstep as [[Hex0 _] |
      (_ & w' & m1 & rs1 & mem1 & Hbytes' & Hsil' & Hwr' & Hσ')];
      [congruence|].
    assert (Hweq : w' = w).
    { apply bv_eq_of_bytes. intros j Hj.
      pose proof (Hbytes' j Hj) as Hb1. pose proof (Hbytes j Hj) as Hb2.
      rewrite Hb2 in Hb1. apply (inj Some) in Hb1. symmetry. exact Hb1. }
    subst w'.
    destruct (hwin_unique k D rsM (K (inl (w, None))) nw (wreq w)
                memM mem1 m1 m' rs1 HwinM Hsil' Hwr')
      as (Hm1 & Hrs1 & Hmem1 & Hm2).
    subst.
    iMod (hreg_frame_update_run k D rs rsM (K (inl (w, None))) Hag
            with "Hri Hrf") as "[Hri Hrf]".
    iMod "Hk" as "[Hmem' HWP]".
    iModIntro.
    iSplitR "HWP Hrf".
    { rewrite /mstate_interp /=. iFrame "Hri Hmem' Hdv". }
    rewrite Hmeq.
    by iApply "HWP".
  Qed.


  (* ==================================================================== *)
  (* 4. THE [swp] FACE, which is the whole point of §0.                    *)
  (*                                                                      *)
  (* [HartEvents] turns each [wp_hart_*] event rule into an [swp] one the  *)
  (* same way; what is special here is only that the fused rule names its  *)
  (* window with [hsil], so the context has to be pushed through the walk  *)
  (* ([hsil_mctx]) and not merely through a single node.                   *)
  (* ==================================================================== *)
  Lemma swp_hart_amo {X : Type} (D : gset register) (k : nat) (n : N)
      (req : Interface.ReadReq.t n) (m : M X) (rs : regstate)
      (nw : N) (wreq : bv (8 * n) -> Interface.WriteReq.t nw)
      (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = true ->
    gen_cert -∗
    hreg_frame rs D -∗
    (* every per-value fact rides INSIDE the fupd, at the ACTUAL read value:
       the window, the write's two classifiers, and the [hsil_opaque]
       condition the context transport needs.  See [wp_hart_amo]'s note for
       why none of them can be a [forall w] premise. *)
    (∀ mm : gmap Arch.pa (bv 8), gen_heap_interp mm ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes mm (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ⌜hwrite_req_at nw
            (hsil k D (rs, hread_resume (bv_unsigned w) m)).2 = Some (wreq w)⌝ ∗
         ⌜dev_addr (Interface.WriteReq.pa (wreq w)) = false⌝ ∗
         ⌜ak_excl (Interface.WriteReq.access_kind (wreq w)) = true⌝ ∗
         ⌜forall j : nat, (j < k)%nat ->
            hsil_opaque
              ((hsil j D (rs, hread_resume (bv_unsigned w) m)).2) = false⌝ ∗
         ▷ (|={∅,⊤}=> gen_heap_interp
                (write_bytes mm (Interface.WriteReq.pa (wreq w)) nw
                   (Interface.WriteReq.value (wreq w))) ∗
              (hreg_frame
                 (hsil k D (rs, hread_resume (bv_unsigned w) m)).1 D -∗
               swp (hwrite_resume
                      (hsil k D (rs, hread_resume (bv_unsigned w) m)).2) Φ))) -∗
    swp m Φ.
  Proof.
    intros Hproj Hdev Hexcl.
    iIntros "#Hcert Hrf H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_amo D k n req (C m) rs nw wreq
              (hread_req_at_mctx C n m req HC Hproj) Hdev Hexcl
              with "Hcert Hrf [H Hcont]").
    iIntros (mm) "Hmm".
    iMod ("H" $! mm with "Hmm") as (w) "(%Hrb & %Hwin & %Hwdev & %Hwex & %Hop & Hk)".
    (* the window, transported through the context at THIS [w] *)
    assert (Hstep : hsil k D (rs, hread_resume (bv_unsigned w) (C m))
                    = ((hsil k D (rs, hread_resume (bv_unsigned w) m)).1,
                       C (hsil k D (rs, hread_resume (bv_unsigned w) m)).2)).
    { rewrite (hread_resume_mctx C n m req (bv_unsigned w) HC Hproj).
      exact (hsil_mctx C D k rs (hread_resume (bv_unsigned w) m) HC Hop). }
    iModIntro. iExists w. iSplitR; [done|].
    iSplitR.
    { iPureIntro. rewrite Hstep. cbn [snd].
      exact (hwrite_req_at_mctx C nw _ (wreq w) HC Hwin). }
    iSplitR; [done|]. iSplitR; [done|].
    iNext. iMod "Hk" as "[Hmm Hcl]". iModIntro. iFrame "Hmm".
    rewrite Hstep. cbn [fst snd].
    iIntros "Hrf'".
    rewrite (hwrite_resume_mctx C nw _ (wreq w) HC Hwin).
    iApply (swp_use _ Φ C HC with "[Hcl Hrf'] Hcont").
    by iApply "Hcl".
  Qed.

End amo.
