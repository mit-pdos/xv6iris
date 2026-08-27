(* HartLift2.v -- the TWO-FOOTPRINT functional batch: silent stretches
   whose reads split into exclusively-owned registers ([Drw], frame at
   DfracOwn 1, writable) and read-only pinned ones ([Dro], dfrac-generic
   frame, never written).  The leaf-side stretch of a cycle (decode +
   execute + the tail prefix) is exactly this shape: GPRs/PC/nextPC in
   [Drw], the config bundle (misa, elp, mstatus, cur_privilege, mseccfg,
   ...) in [Dro] at the caller's fractions -- every read pinnable, no
   ∀-values, hence FUNCTIONAL stepping (unlike the span).

   Sits beside HartLift (the one-footprint batch) rather than replacing
   it: a new leaf file costs nothing, editing HartLift recompiles the
   whole Hart* cone.  [hreg_frame_ro] is HartSpan's. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift HartSpan.
(* [pwmsg]/[agent]: the node bridge below carries the memory-model state *)
Require Import TsoMemPa.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The stepper.                                                         *)
(* ====================================================================== *)

(* X-GENERIC, for the reason [HartLift]'s [hsil_node] is: the swp layer's
   inner monad is an [M X], and the fused AMO rule's window has to be
   commuted with an opaque context there. *)
Definition hsil_node2 {X : Type} (Drw Dro : gset register) (rs : regstate)
    (m : M X) : option (regstate * M X) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (regstate * M X) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ Drw ∪ Dro)
           then Some (rs, k (register_lookup r rs)) else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ Drw)
           then Some (register_set r v rs, k tt) else None
       | Interface.InstrAnnounce _    => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _ => fun k => Some (rs, k tt)
       | Interface.Barrier _          => fun k => Some (rs, k tt)
       | Interface.CacheOp _          => fun k => Some (rs, k tt)
       | Interface.TlbOp _            => fun k => Some (rs, k tt)
       | Interface.TakeException _    => fun k => Some (rs, k tt)
       | Interface.ReturnException _  => fun k => Some (rs, k tt)
       | Interface.TranslationStart _ => fun k => Some (rs, k tt)
       | Interface.TranslationEnd _   => fun k => Some (rs, k tt)
       | Interface.CycleCount         => fun k => Some (rs, k tt)
       | Interface.Message _          => fun k => Some (rs, k tt)
       | Interface.GetCycleCount      => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Fixpoint hrun_silent2 {X : Type} (n : nat) (Drw Dro : gset register)
    (rs : regstate) (m : M X) : regstate * M X :=
  match n with
  | 0%nat => (rs, m)
  | S n' =>
      match hsil_node2 Drw Dro rs m with
      | Some (rs', m') => hrun_silent2 n' Drw Dro rs' m'
      | None => (rs, m)
      end
  end.

Definition hsil2 {X : Type} (n : nat) (Drw Dro : gset register)
    (x : hcurX X) : hcurX X :=
  hrun_silent2 n Drw Dro x.1 x.2.

(* ---------------------------------------------------------------------- *)
(* STEPPING [hsil2] BY REWRITE -- [HartLift]'s [hsil_read_in] family at the *)
(* TWO-footprint walker, which is the one the swp layer can actually use:   *)
(* it reads from [Drw ∪ Dro] but writes only in [Drw], matching the frame   *)
(* split ([hreg_frame] full / [hreg_frame_ro] fractional) exactly.          *)
(* ---------------------------------------------------------------------- *)
Lemma hsil2_ret {X : Type} (n : nat) (Drw Dro : gset register)
    (rs : regstate) (x : X) :
  hsil2 n Drw Dro (rs, Interface.Ret x) = (rs, Interface.Ret x).
Proof. destruct n; reflexivity. Qed.

Lemma hsil2_read_in {X : Type} (n : nat) (Drw Dro : gset register)
    (rs : regstate) (r : register) (ak : option unit)
    (k : type_of_register r -> M X) :
  r ∈ Drw ∪ Dro ->
  hsil2 (S n) Drw Dro (rs, Interface.Next (Interface.RegRead r ak) k)
  = hsil2 n Drw Dro (rs, k (register_lookup r rs)).
Proof.
  intros HD. unfold hsil2. cbn [fst snd hrun_silent2 hsil_node2].
  rewrite (decide_True_pi HD). reflexivity.
Qed.

Lemma hsil2_write_in {X : Type} (n : nat) (Drw Dro : gset register)
    (rs : regstate) (r : register) (ak : option unit)
    (v : type_of_register r) (k : unit -> M X) :
  r ∈ Drw ->
  hsil2 (S n) Drw Dro (rs, Interface.Next (Interface.RegWrite r ak v) k)
  = hsil2 n Drw Dro (register_set r v rs, k tt).
Proof.
  intros HD. unfold hsil2. cbn [fst snd hrun_silent2 hsil_node2].
  rewrite (decide_True_pi HD). reflexivity.
Qed.

Lemma hsil2_stuck {X : Type} (n : nat) (Drw Dro : gset register)
    (rs : regstate) (m : M X) :
  hsil_node2 Drw Dro rs m = None -> hsil2 n Drw Dro (rs, m) = (rs, m).
Proof.
  intros Hnode. destruct n; [reflexivity|].
  cbn [hsil2 hrun_silent2]. by rewrite Hnode.
Qed.

Lemma hsil2_add {X : Type} (a b : nat) (Drw Dro : gset register)
    (rs : regstate) (m : M X) :
  hsil2 (a + b) Drw Dro (rs, m) = hsil2 b Drw Dro (hsil2 a Drw Dro (rs, m)).
Proof.
  revert rs m. induction a as [|a IH]; intros rs m; [reflexivity|].
  cbn [Nat.add hsil2 hrun_silent2 fst snd].
  destruct (hsil_node2 Drw Dro rs m) as [[rs1 m1]|] eqn:Hnode.
  - change (hrun_silent2 (a + b) Drw Dro rs1 m1)
      with (hsil2 (a + b) Drw Dro (rs1, m1)).
    change (hrun_silent2 a Drw Dro rs1 m1) with (hsil2 a Drw Dro (rs1, m1)).
    exact (IH rs1 m1).
  - symmetry. exact (hsil2_stuck b Drw Dro rs m Hnode).
Qed.

Definition hsil2D (Drw Dro : gset register)
    (x y : M unit * regstate) : Prop :=
  hsil_node2 Drw Dro x.2 x.1 = Some (y.2, y.1).

Lemma hrun_silent2_sound (n : nat) (Drw Dro : gset register)
    (rs : regstate) (m : M unit) (rs' : regstate) (m' : M unit) :
  hrun_silent2 n Drw Dro rs m = (rs', m') ->
  rtc (hsil2D Drw Dro) (m, rs) (m', rs').
Proof.
  revert rs m. induction n as [|n IH]; intros rs m Heq.
  { simpl in Heq. by injection Heq as <- <-. }
  simpl in Heq. destruct (hsil_node2 Drw Dro rs m) as [[rs1 m1]|] eqn:Hnode.
  - apply (rtc_l (hsil2D Drw Dro) (m, rs) (m1, rs1)); [exact Hnode|].
    by apply IH.
  - by injection Heq as <- <-.
Qed.

(* the semantic bridge, as HartLift's: a two-footprint silent node IS an
   [mnode_step], and the only one there *)
(* the view rides along exactly as in HartLift ([hsil_tv]): the DRAINING
   BARRIER is the one silent node with a memory-model effect. *)
Lemma hsil_node2_mnode (Drw Dro : gset register) (rs rs' : regstate)
    (m m' : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  forall (oth : gset Arch.pa) (h : agent) (img : gmap Arch.pa (bv 8))
         (log : list pwmsg) (tv : nat) (r : option resv),
    mnode_step oth h img (MState rs mem dev) log tv r m m'
      (MState rs' mem dev) log (hsil_tv h log m tv) r.
Proof.
  intros Hnode oth h img log tv r. destruct m as [y|T oc k];
    [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; by split_and!.
Qed.

Lemma hsil_node2_mnode_inv (Drw Dro : gset register) (rs rs' : regstate)
    (m m' m2 : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state)
    (σ2 : mstate) (oth : gset Arch.pa) (h : agent)
    (img : gmap Arch.pa (bv 8)) (log log2 : list pwmsg) (tv tv2 : nat)
    (r r2 : option resv) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  mnode_step oth h img (MState rs mem dev) log tv r m m2 σ2 log2 tv2 r2 ->
  m2 = m' /\ σ2 = MState rs' mem dev /\ log2 = log /\
  tv2 = hsil_tv h log m tv /\ r2 = r.
Proof.
  intros Hnode Hstep. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hstep as (-> & -> & -> & -> & ->);
    by split_and!.
Qed.

(* a silent node never touches the hart's reservation -- the side condition
   of the reservation-agnostic [wp_hart_step] *)
Lemma hsil_node2_pres (Drw Dro : gset register) (rs rs' : regstate)
    (m m' : M unit) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  forall (oth : gset Arch.pa) (h : agent) (img : gmap Arch.pa (bv 8))
         (s : mstate) (log : list pwmsg) (tv : nat) (r : option resv)
         (m2 : M unit) (s2 : mstate) (log2 : list pwmsg) (tv2 : nat)
         (r2 : option resv),
    mnode_step oth h img s log tv r m m2 s2 log2 tv2 r2 -> r2 = r.
Proof.
  intros Hnode oth h img s log tv r m2 s2 log2 tv2 r2 Hstep.
  destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hstep as (_ & _ & _ & _ & ->);
    reflexivity.
Qed.

Lemma hsil_node2_agree {X : Type} (Drw Dro : gset register) (rs1 rs2 : regstate)
    (m m1 : M X) (rs1' : regstate) :
  reg_agree_on (Drw ∪ Dro) rs1 rs2 ->
  hsil_node2 Drw Dro rs1 m = Some (rs1', m1) ->
  exists rs2', hsil_node2 Drw Dro rs2 m = Some (rs2', m1) /\
       reg_agree_on (Drw ∪ Dro) rs1' rs2'.
Proof.
  intros Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    first
      [ (* RegRead: answered from the file, which agrees on the union *)
        case_decide as HrD; [|discriminate Hnode];
        injection Hnode as <- <-; rewrite (Hag _ HrD); exists rs2; by split
      | (* RegWrite: the same register moves on both sides *)
        case_decide as HrD; [|discriminate Hnode];
        injection Hnode as <- <-; eexists; (split; [done|]);
        intros r' Hr'; destruct (decide (r' = reg)) as [->|Hne];
        [ by rewrite !register_lookup_set
        | rewrite !(irrelevant_register_set r' reg _ regval
                      (register_beq_false r' reg Hne)); by apply Hag ]
      | injection Hnode as <- <-; exists rs2; by split ].
Qed.

(* ====================================================================== *)
(* 2. The batched WP rule.                                                 *)
(* ====================================================================== *)

Section batch2.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* local helper (HartSpan's [hreg_frame_ro_ext_local] is Local there;
     re-derived here, mirroring [hreg_frame_ext]): the ro-frame only reads
     the footprint's lookups, so it re-anchors across any file agreeing on
     [Dro]. *)
  Local Lemma hreg_frame_ro_ext_local (Df : register -> dfrac)
      (rs rs' : regstate) (Dro : gset register) :
    reg_agree_on Dro rs rs' ->
    hreg_frame_ro Df rs Dro ⊣⊢ hreg_frame_ro Df rs' Dro.
  Proof.
    intros Hag. rewrite /hreg_frame_ro. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  Lemma wp_hsil2_node (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs1 : regstate) (m m1 : M unit) :
    Drw ## Dro ->
    hsil_node2 Drw Dro rs m = Some (rs1, m1) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    ▷ (hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       WP (HartE gen_id cpu_id m1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros (Hdisj Hnode) "#Hcert Hrf Hro H".
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 tv0 r0 m'0 σ'0 log'0 tv'0 r'0 Hs.
      exact (hsil_node2_pres Drw Dro rs rs1 m m1 Hnode oth0 h0 img0 σ0 log0
               tv0 r0 m'0 σ'0 log'0 tv'0 r'0 Hs). }
    iIntros (σ oth r img log tv V) "%Htv Hσ Htso".
    destruct σ as [rs0 mem0 dev0].
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (hreg_frame_agree rs Drw rs0 with "Hri Hrf") as %HagW.
    iDestruct (hreg_frame_ro_agree Df rs Dro rs0 with "Hri Hro") as %HagO.
    assert (Hag : reg_agree_on (Drw ∪ Dro) rs rs0).
    { intros r' Hr'. apply elem_of_union in Hr' as [Hr'|Hr'];
        [by apply HagW|by apply HagO]. }
    destruct (hsil_node2_agree Drw Dro rs rs0 m m1 rs1 Hag Hnode)
      as (rs2 & Hnode2 & Hag2).
    (* the draining barrier is the one silent node with a memory-model
       effect (HartLift's [hsil_tv]); pay its monotone view advance here *)
    iAssert (⌜(tv <= length log)%nat⌝)%I as %Htvlen.
    { iDestruct "Htso" as (TM LM) "(_&_&_&_&_&_&_&_&%Hb&_)".
      iPureIntro. rewrite -Htv. apply Hb. }
    assert (Hadv : (V (hart_agent cpu_id)
                    <= hsil_tv (hart_agent cpu_id) log m tv)%nat)
      by (rewrite Htv; apply hsil_tv_ge).
    iMod (tso_interp_of_advance _ img mem0 log V (hart_agent cpu_id)
            (hsil_tv (hart_agent cpu_id) log m tv)
            (fin_to_nat_lt cpu_id) Hadv (hsil_tv_le _ _ _ _ Htvlen)
           with "Htso") as "Htso".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iExists m1, (MState rs2 mem0 dev0), log,
      (hsil_tv (hart_agent cpu_id) log m tv), r.
    iSplitR.
    { iPureIntro.
      exact (hsil_node2_mnode Drw Dro rs0 rs2 m m1 mem0 dev0 Hnode2 oth
               (hart_agent cpu_id) img log tv r). }
    iNext. iIntros (m' σ' log' tv' r') "%Hstep".
    destruct (hsil_node2_mnode_inv Drw Dro rs0 rs2 m m1 m' mem0 dev0 σ' oth
                (hart_agent cpu_id) img log log' tv tv' r r' Hnode2 Hstep)
      as (-> & -> & -> & -> & ->).
    (* re-establish: for a RegWrite one [Drw] register moves (the ro-frame
       re-anchors through disjointness), otherwise the file is untouched *)
    iAssert (|==> reg_interp rs2 ∗ hreg_frame rs1 Drw ∗
                  hreg_frame_ro Df rs1 Dro)%I
      with "[Hri Hrf Hro]" as ">(Hri & Hrf & Hro)".
    { destruct m as [y|T oc k]; [by simpl in Hnode|].
      (* SPLIT INTO ITS OWN SENTENCES so the per-sentence profile can say
         which of the four steps over the node type's constructors costs what
         -- as one sentence it read as a flat 16.1 s. *)
      destruct oc.
      all: simpl in Hnode.
      all: try discriminate Hnode.
      (* CHEAP-FAILING BRANCH FIRST (optimization.md, "Smaller traps"): the
         cost of a branch that FAILS grows with what it did before failing,
         and [first] re-tries from the top on every one of the node type's
         constructors.  The RegWrite branch fails only after two
         [case_decide]s, two [injection]s, a [set_solver] and an [iMod], so
         leading with it charged every announce-class and RegRead goal that
         whole prefix: 16.2 s for this one sentence.  Ordered
         announce < RegRead < RegWrite, each still closing its own goal, so
         [first] commits only on a branch that finishes. *)
      all:
        first
          [ (* the announce class: the file does not move *)
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; by iFrame "Hri Hrf Hro"
          | (* RegRead: the file does not move *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; by iFrame "Hri Hrf Hro"
          | (* RegWrite: [reg ∈ Drw], hence [reg ∉ Dro] *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            assert (HrO : reg ∉ Dro) by set_solver;
            assert (HagO' : reg_agree_on Dro rs (register_set reg regval rs))
              by (intros r' Hr';
                  assert (Hne : r' <> reg) by (intros ->; by apply HrO);
                  by rewrite (irrelevant_register_set r' reg rs regval
                                (register_beq_false r' reg Hne)));
            iMod (hreg_frame_update rs Drw reg regval rs0 HrD
                    with "Hri Hrf") as "[Hri Hrf]";
            iModIntro; iFrame "Hri Hrf";
            by iApply (hreg_frame_ro_ext_local Df rs
                         (register_set reg regval rs) Dro HagO') ]. }
    iMod "Hmask" as "_". iModIntro.
    iSplitR "H Hrf Hro Htso"; [iFrame "Hri Hmem Hdev"|].
    iSplitL "Htso"; [iExact "Htso"|].
    iApply ("H" with "Hrf Hro").
  Qed.

  Lemma wp_hsil2_rtc (Drw Dro : gset register) (Df : register -> dfrac)
      (x y : M unit * regstate) :
    Drw ## Dro ->
    rtc (hsil2D Drw Dro) x y ->
    gen_cert -∗
    hreg_frame x.2 Drw -∗
    hreg_frame_ro Df x.2 Dro -∗
    (hreg_frame y.2 Drw -∗ hreg_frame_ro Df y.2 Dro -∗
       WP (HartE gen_id cpu_id y.1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.1 : expr riscv_lang).
  Proof.
    intros Hdisj Hrtc. induction Hrtc as [x|x y0 z Hxy _ IH].
    - iIntros "#Hcert Hrf Hro H". by iApply ("H" with "Hrf Hro").
    - destruct x as [m0 rs0], y0 as [m1 rs1]. simpl in Hxy |- *.
      iIntros "#Hcert Hrf Hro H".
      iApply (wp_hsil2_node Drw Dro Df rs0 rs1 m0 m1 Hdisj Hxy
                with "Hcert Hrf Hro").
      iNext. iIntros "Hrf Hro". by iApply (IH with "Hcert Hrf Hro").
  Qed.

  (* the call-site form, F8 shape *)
  Lemma wp_hart_batch2 (Drw Dro : gset register) (Df : register -> dfrac)
      (n : nat) (x : hcur) :
    Drw ## Dro ->
    gen_cert -∗
    hreg_frame x.1 Drw -∗
    hreg_frame_ro Df x.1 Dro -∗
    (hreg_frame (hsil2 n Drw Dro x).1 Drw -∗
     hreg_frame_ro Df (hsil2 n Drw Dro x).1 Dro -∗
       WP (HartE gen_id cpu_id (hsil2 n Drw Dro x).2 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.2 : expr riscv_lang).
  Proof.
    intros Hdisj.
    exact (wp_hsil2_rtc Drw Dro Df (x.2, x.1)
             ((hsil2 n Drw Dro x).2, (hsil2 n Drw Dro x).1) Hdisj
             (hrun_silent2_sound n Drw Dro x.1 x.2
                (hsil2 n Drw Dro x).1 (hsil2 n Drw Dro x).2
                (surjective_pairing (hrun_silent2 n Drw Dro x.1 x.2)))).
  Qed.

End batch2.

(* ====================================================================== *)
(* 3. The text-byte fetch witness (the F7 byte bridge): the [read_bytes]   *)
(*    fact from persistent kernel-text cells.  [text_pointsto] carries the *)
(*    identity mapping ([pa_of ppn a = a]), so the physical lookup is at   *)
(*    the cell's own address.                                              *)
(* ====================================================================== *)

(* local helper (RiscvFetchExec.read_bytes_ne re-derived: that file is not
   in this leaf's import cone): read_bytes is non-None when all n bytes are
   present. *)
Local Lemma read_bytes_ne_local (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N ->
     mm !! pa_add pa j = Some (nth_byte w j)) ->
  read_bytes mm pa n <> None.
Proof.
  intros Hb. unfold read_bytes.
  case_match eqn:Hm; [congruence|].
  exfalso.
  apply stdpp.list_monad.mapM_None_1, List.Exists_exists in Hm.
  destruct Hm as (j & Hj & Hnone).
  apply List.in_seq in Hj.
  assert (Hjn : (N.of_nat j < n)%N) by lia.
  rewrite (Hb j Hjn) in Hnone. congruence.
Qed.

Section textbytes.
  Context `{!riscvGS Σ}.

  (* local helper: per-byte lookup from a persistent text cell, generalized
     over the index list (mirrors HartPilot.phys_bytes_lookup; the identity
     conjunct of [text_pointsto_acc] moves the lookup from [pa_of ppn a]
     to the cell's own address). *)
  Local Lemma text_bytes_lookup_local (mm : gmap Arch.pa (bv 8))
      (pa : Arch.pa) {m : N} (w : bv m) (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ l, (pa_add pa j) ↦ₓ□ nth_byte w j) -∗
    ⌜forall j, j ∈ l -> mm !! pa_add pa j = Some (nth_byte w j)⌝.
  Proof.
    iInduction l as [|x xs] "IH"; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. by apply elem_of_nil in Hj.
    - iIntros "Hm [Ha Hrest]".
      iDestruct (text_pointsto_acc with "Ha")
        as (ppn) "(_ & _ & _ & %Hid & Hp & _)".
      iDestruct (gen_heap_valid with "Hm Hp") as %Hx.
      rewrite Hid in Hx.
      iDestruct ("IH" with "Hm Hrest") as %Hxs.
      iPureIntro. intros j Hj.
      apply elem_of_cons in Hj as [->|Hj]; [exact Hx|exact (Hxs j Hj)].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE TSO TWIN (tso-machine-flip.md A6.43).  Post-overruling a fetch    *)
  (* takes the plain arm, so the flat [read_bytes] fact above no longer    *)
  (* pays for it: what is owed is a [tso_read_bytes] at EVERY reachable    *)
  (* view.  Kernel text pays it because a text byte is an ERA-IMAGE byte,  *)
  (* and [text_pointsto] now carries the resource that says so -- the      *)
  (* DISCARDED timestamp element at 0.  So the same [↦ₓ□] window that      *)
  (* proved the flat fact proves the view-indexed one, with no new premise *)
  (* anywhere above.  Note the conclusion quantifies over EVERY agent and  *)
  (* EVERY view: a caller needs to know neither its hart nor its view.     *)
  (* ------------------------------------------------------------------ *)
  Local Lemma text_byte_phys_pristine (a : Arch.pa) (b : bv 8) :
    a ↦ₓ□ b -∗ phys_pointsto a DfracDiscarded b ∗ TsoCtx.pristine_byte a.
  Proof.
    iIntros "Ha".
    iDestruct (text_pointsto_acc with "Ha")
      as (ppn) "(_ & _ & %Htx & %Hid & Hp & #Hts & _)".
    rewrite Hid in Htx. iEval (rewrite Hid) in "Hp".
    iEval (rewrite Hid) in "Hts".
    rewrite /phys_pointsto /TsoCtx.pristine_byte /pristine_elem. iFrame "Hp Hts".
    iPureIntro. exact (addr_is_text_ram a Htx).
  Qed.

  Lemma text_tso_read_bytes (g : gstate) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) :
    gen_heap_interp (hG:=riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₓ□ nth_byte w j) -∗
    ⌜forall (h : agent) (tv : nat),
       tso_read_bytes g.(gimg) g.(glog) h tv pa n w⌝.
  Proof.
    iIntros "Hgh Hint #Hb".
    iAssert ([∗ list] j ∈ seq 0 (N.to_nat n),
               phys_pointsto (pa_add pa j) DfracDiscarded (nth_byte w j))%I
      as "#Hp".
    { iApply big_sepL_intro. iIntros "!>" (k j Hk).
      iDestruct (big_sepL_lookup _ _ k j Hk with "Hb") as "Hbj".
      iDestruct (text_byte_phys_pristine with "Hbj") as "[$ _]". }
    iAssert (TsoCtx.pristine_win pa (N.to_nat n))%I as "#Hpr".
    { rewrite /TsoCtx.pristine_win. iApply big_sepL_intro. iIntros "!>" (k j Hk).
      iDestruct (big_sepL_lookup _ _ k j Hk with "Hb") as "Hbj".
      iDestruct (text_byte_phys_pristine with "Hbj") as "[_ $]". }
    iApply (TsoCtx.pristine_read_bytes_ok g pa n w DfracDiscarded
              with "Hgh Hint Hp Hpr").
  Qed.

  Lemma text_read_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₓ□ nth_byte w j) -∗
    ⌜read_bytes mm pa n = Some w⌝.
  Proof.
    iIntros "Hm Hb".
    iDestruct (text_bytes_lookup_local with "Hm Hb") as %Hl.
    iPureIntro.
    assert (Hbytes : forall j : nat, (N.of_nat j < n)%N ->
              mm !! pa_add pa j = Some (nth_byte w j)).
    { intros j Hj. apply Hl, elem_of_seq. lia. }
    destruct (read_bytes mm pa n) as [w'|] eqn:Hrb.
    - f_equal. apply bv_eq_of_bytes. intros j Hj.
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
      pose proof (Hbytes j Hj) as H1.
      rewrite H0 in H1. apply Some_inj in H1. exact H1.
    - exfalso. exact (read_bytes_ne_local mm pa n w Hbytes Hrb).
  Qed.

End textbytes.
