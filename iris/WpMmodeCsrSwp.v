(* WpMmodeCsrSwp.v -- the CSR-write instructions' [swp] machinery.

   [execute_CSRReg csr rs1 zreg CSRRW] splits into exactly three kinds of
   step, and each gets the route its kind allows:

   - [check_CSR_result csr Machine CSRWrite] is READ-ONLY (its exec fact
     returns the state unchanged) but four levels of guarded recursion deep
     ([currentlyEnabled Ext_S] is a nested [and_boolM] chain).  So it goes
     through [HartGoodb.hval_of_goodb], exactly as [update_elp_state] does in
     WpMmodeJump: [goodb] is [vm_compute]d at [dstateM] and the exec fact is
     the one the exec-based stack already proved.  Its read set is
     [WpDecodeBridge.D_m] = cur_privilege / mseccfg / misa, which is why
     [cw_Dro] is exactly those three and no widening is needed.

   - [rX_bits rs1] is at a SYMBOLIC index, so no walker takes it; the leaf
     peels it with [HartMFrame.swp_rX_file].

   - [write_CSR csr v] WRITES, so [goodb] is unavailable -- but at a CONCRETE
     csr it reduces to three nodes at that one register, so [hfrun] walks it.
     That is the only per-CSR work, ~10 lines each.

   [csr_id_write_callback csr d] needs no route at all: at a concrete csr it
   is [returnM tt] by [vm_compute], a pure term equation. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartSpanChar HartRegNode HartMCycle RegFile WpGpr.
Require Import RiscvExtras RiscvFetchExec WpMmodeLeafBase HartMFrame
        ExecCommon HartMRun HartGoodb WpDecodeBridge.
Local Open Scope Z_scope.

(* collapse the closed [Z.eqb] tests of the model's rX/wX cascades *)
Local Ltac zt :=

  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let x := eval vm_compute in b in
      lazymatch x with true => change b with true
                     | false => change b with false end
  end.


Require Import WpMmodeJump.
Require Import TsoCtx.

Section csrw.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the file: the written CSR on top of the three config pins *)
  Definition cw_rs (r : register) (v0 : type_of_register r) : regstate :=
    register_set r v0
      (register_set misa MISA_C
         (register_set mseccfg (Values.mword_of_int 0)
            (register_set cur_privilege Machine init_regstate))).

  (* "the written register is none of the three config pins" -- every CSR leaf
     discharges this by [vm_compute] *)
  Definition cw_fresh (r : register) : Prop :=
    register_beq misa r = false /\
    register_beq mseccfg r = false /\
    register_beq cur_privilege r = false.

  Lemma cw_fresh_ne (r : register) :
    cw_fresh r ->
    (misa : register) <> r /\ (mseccfg : register) <> r /\
    (cur_privilege : register) <> r.
  Proof.
    intros (H1 & H2 & H3). split_and!; intro Heq; rewrite -Heq in H1, H2, H3;
      first [ vm_compute in H1; discriminate
            | vm_compute in H2; discriminate
            | vm_compute in H3; discriminate ].
  Qed.

  Lemma cw_rs_r (r : register) (v0 : type_of_register r) :
    register_lookup r (cw_rs r v0) = v0.
  Proof. rewrite /cw_rs. apply register_lookup_set. Qed.

  Lemma cw_rs_misa (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup misa (cw_rs r v0) = MISA_C.
  Proof.
    intros (H1 & _ & _). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H1|].
    apply register_lookup_set.
  Qed.

  Lemma cw_rs_sec (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup mseccfg (cw_rs r v0) = Values.mword_of_int 0.
  Proof.
    intros (_ & H2 & _). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H2|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Lemma cw_rs_priv (r : register) (v0 : type_of_register r) :
    cw_fresh r -> register_lookup cur_privilege (cw_rs r v0) = Machine.
  Proof.
    intros (_ & _ & H3). rewrite /cw_rs.
    etransitivity; [apply irrelevant_register_set; exact H3|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Definition cw_Df (dq : dfrac) : register -> dfrac := fun r' =>
    if decide (r' = (misa : register)) then DfracDiscarded
    else if decide (r' = (mseccfg : register)) then DfracDiscarded
    else dq.

  Ltac cwdf :=
    unfold cw_Df;
    repeat first [ rewrite decide_True; [reflexivity|reflexivity]
                 | rewrite decide_False; [|discriminate] ];
    reflexivity.

  Lemma cw_Df_misa dq : cw_Df dq misa = DfracDiscarded.
  Proof. cwdf. Qed.
  Lemma cw_Df_sec dq : cw_Df dq mseccfg = DfracDiscarded.
  Proof. cwdf. Qed.
  Lemma cw_Df_priv dq : cw_Df dq cur_privilege = dq.
  Proof. cwdf. Qed.

  Lemma cw_disj (r : register) : cw_fresh r -> cw_Drw r ## cw_Dro.
  Proof.
    intros (H1 & H2 & H3). rewrite /cw_Drw /cw_Dro.
    apply disjoint_singleton_l. intro Hin.
    repeat (apply elem_of_union in Hin as [Hin|Hin]);
      apply elem_of_singleton in Hin; subst r.
    all: first [ vm_compute in H1; discriminate
               | vm_compute in H2; discriminate
               | vm_compute in H3; discriminate ].
  Qed.

  Lemma cw_w_r (r : register) : r ∈ cw_Drw r.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw_in_r (r : register) : r ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw_in_priv (r : register) : (cur_privilege : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cw_in_sec (r : register) : (mseccfg : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cw_in_misa (r : register) : (misa : register) ∈ cw_Drw r ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.

  (* cells <-> the four-cell frame *)
  Lemma cw_frames (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto r (DfracOwn 1) v0 ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr.
    rewrite /hreg_frame /hreg_frame_ro /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite cw_rs_r (cw_rs_priv r v0 Hfr) (cw_rs_sec r v0 Hfr)
      (cw_rs_misa r v0 Hfr).
    rewrite (cw_Df_priv dq) (cw_Df_sec dq) (cw_Df_misa dq).
    by rewrite !bi.sep_assoc.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE EXTRA READ CELL.  Three of the csrw leaves compute the written     *)
  (* value from a SECOND register: sie from mideleg, satp from mstatus       *)
  (* (via [architecture Supervisor]), pmpaddr0 from pmpcfg_n.  None of the   *)
  (* three values is pinned at the reference state, so [goodb] cannot        *)
  (* transport those reads and the cell must be in the footprint -- one      *)
  (* extra cell, at its own fraction, on top of [cw_*].                      *)
  (* ------------------------------------------------------------------ *)
  Definition cw2_Dro (r2 : register) : gset register := {[ r2 ]} ∪ cw_Dro.

  Definition cw2_rs (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) : regstate :=
    register_set r2 v2 (cw_rs r v0).

  Definition cw2_Df (dq dq2 : dfrac) (r2 : register) : register -> dfrac :=
    fun r' =>
      if decide (r' = (misa : register)) then DfracDiscarded
      else if decide (r' = (mseccfg : register)) then DfracDiscarded
      else if decide (r' = r2) then dq2 else dq.

  (* "the second cell is neither a config pin nor the written cell" *)
  Definition cw2_ok (r r2 : register) : Prop :=
    cw_fresh r /\ cw_fresh r2 /\ r <> r2.

  Lemma cw2_disj (r r2 : register) :
    cw2_ok r r2 -> cw_Drw r ## cw2_Dro r2.
  Proof.
    intros (Hfr & Hfr2 & Hne). rewrite /cw_Drw /cw2_Dro /cw_Dro.
    apply disjoint_singleton_l. intro Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. exact (Hne Hin).
    - destruct Hfr as (H1 & H2 & H3).
      repeat (apply elem_of_union in Hin as [Hin|Hin]);
        apply elem_of_singleton in Hin; subst r.
      all: first [ vm_compute in H1; discriminate
                 | vm_compute in H2; discriminate
                 | vm_compute in H3; discriminate ].
  Qed.

  Lemma cw2_w_r (r r2 : register) : r ∈ cw_Drw r.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw2_in_r (r r2 : register) : r ∈ cw_Drw r ∪ cw2_Dro r2.
  Proof. rewrite /cw_Drw. set_solver. Qed.
  Lemma cw2_in_r2 (r r2 : register) : r2 ∈ cw_Drw r ∪ cw2_Dro r2.
  Proof. rewrite /cw2_Dro. set_solver. Qed.
  Lemma cw2_in_priv (r r2 : register) :
    (cur_privilege : register) ∈ cw_Drw r ∪ cw2_Dro r2.
  Proof. rewrite /cw2_Dro /cw_Dro. set_solver. Qed.
  Lemma cw2_in_sec (r r2 : register) :
    (mseccfg : register) ∈ cw_Drw r ∪ cw2_Dro r2.
  Proof. rewrite /cw2_Dro /cw_Dro. set_solver. Qed.
  Lemma cw2_in_misa (r r2 : register) :
    (misa : register) ∈ cw_Drw r ∪ cw2_Dro r2.
  Proof. rewrite /cw2_Dro /cw_Dro. set_solver. Qed.

  Local Ltac c2lk := rewrite /cw2_rs;
    etransitivity; [ apply irrelevant_register_set; vm_compute; reflexivity |].

  Lemma cw2_rs_r2 (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    register_lookup r2 (cw2_rs r v0 r2 v2) = v2.
  Proof. rewrite /cw2_rs. apply register_lookup_set. Qed.
  Lemma cw2_rs_r (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 -> register_lookup r (cw2_rs r v0 r2 v2) = v0.
  Proof.
    intros (_ & _ & Hne). rewrite /cw2_rs.
    etransitivity;
      [apply irrelevant_register_set; exact (register_beq_false r r2 Hne)|].
    apply cw_rs_r.
  Qed.
  Lemma cw2_rs_priv (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 -> register_lookup cur_privilege (cw2_rs r v0 r2 v2) = Machine.
  Proof.
    intros (Hfr & (_ & _ & H3) & _). rewrite /cw2_rs.
    etransitivity; [apply irrelevant_register_set; exact H3|].
    apply (cw_rs_priv r v0 Hfr).
  Qed.
  Lemma cw2_rs_sec (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    register_lookup mseccfg (cw2_rs r v0 r2 v2) = Values.mword_of_int 0.
  Proof.
    intros (Hfr & (_ & H2 & _) & _). rewrite /cw2_rs.
    etransitivity; [apply irrelevant_register_set; exact H2|].
    apply (cw_rs_sec r v0 Hfr).
  Qed.
  Lemma cw2_rs_misa (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 -> register_lookup misa (cw2_rs r v0 r2 v2) = MISA_C.
  Proof.
    intros (Hfr & (H1 & _ & _) & _). rewrite /cw2_rs.
    etransitivity; [apply irrelevant_register_set; exact H1|].
    apply (cw_rs_misa r v0 Hfr).
  Qed.

  Lemma cw2_Df_misa dq dq2 r2 : cw2_Df dq dq2 r2 misa = DfracDiscarded.
  Proof. rewrite /cw2_Df. repeat case_decide; congruence. Qed.
  Lemma cw2_Df_sec dq dq2 r2 : cw2_Df dq dq2 r2 mseccfg = DfracDiscarded.
  Proof. rewrite /cw2_Df. repeat case_decide; congruence. Qed.
  Lemma cw2_Df_r2 dq dq2 (r2 : register) :
    cw_fresh r2 -> cw2_Df dq dq2 r2 r2 = dq2.
  Proof.
    intros Hfr2. pose proof (cw_fresh_ne r2 Hfr2) as (Nmisa & Nsec & _).
    rewrite /cw2_Df. repeat case_decide; congruence.
  Qed.
  Lemma cw2_Df_r dq dq2 (r r2 : register) :
    cw2_ok r r2 -> cw2_Df dq dq2 r2 r = dq.
  Proof.
    intros (Hfr & _ & Nr2). pose proof (cw_fresh_ne r Hfr) as (Nmisa & Nsec & _).
    rewrite /cw2_Df. repeat case_decide; congruence.
  Qed.
  Lemma cw2_Df_priv dq dq2 (r2 : register) :
    cw_fresh r2 -> cw2_Df dq dq2 r2 cur_privilege = dq.
  Proof.
    intros Hfr2. pose proof (cw_fresh_ne r2 Hfr2) as (_ & _ & Npriv).
    rewrite /cw2_Df. repeat case_decide; congruence.
  Qed.

  Lemma cw2_frames (dq dq2 : dfrac) (r : register) (v0 : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    (hreg_frame (cw2_rs r v0 r2 v2) (cw_Drw r) ∗
     hreg_frame_ro (cw2_Df dq dq2 r2) (cw2_rs r v0 r2 v2) (cw2_Dro r2)
     : iProp Σ)
    ⊣⊢ (reg_pointsto r (DfracOwn 1) v0 ∗
        reg_pointsto r2 dq2 v2 ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hok. pose proof Hok as (Hfr & Hfr2 & _).
    rewrite /hreg_frame /hreg_frame_ro /cw_Drw /cw2_Dro.
    rewrite (big_sepS_union _ ({[r2]} : gset register) cw_Dro).
    2:{ destruct (cw_fresh_ne r2 Hfr2) as (N1 & N2 & N3).
        rewrite /cw_Dro. apply disjoint_singleton_l. intro Hin.
        repeat (apply elem_of_union in Hin as [Hin|Hin]);
          apply elem_of_singleton in Hin;
          first [ exact (N3 (eq_sym Hin)) | exact (N1 (eq_sym Hin))
                | exact (N2 (eq_sym Hin)) ]. }
    rewrite /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite (cw2_rs_r r v0 r2 v2 Hok) (cw2_rs_r2 r v0 r2 v2)
      (cw2_rs_priv r v0 r2 v2 Hok) (cw2_rs_sec r v0 r2 v2 Hok)
      (cw2_rs_misa r v0 r2 v2 Hok).
    rewrite (cw2_Df_r2 dq dq2 r2 Hfr2) (cw2_Df_priv dq dq2 r2 Hfr2)
      (cw2_Df_sec dq dq2 r2) (cw2_Df_misa dq dq2 r2).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma cw2_frames_in (dq dq2 : dfrac) (r : register)
      (v0 : type_of_register r) (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    reg_pointsto r (DfracOwn 1) v0 -∗
    reg_pointsto r2 dq2 v2 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (cw2_rs r v0 r2 v2) (cw_Drw r) ∗
     hreg_frame_ro (cw2_Df dq dq2 r2) (cw2_rs r v0 r2 v2) (cw2_Dro r2)
     : iProp Σ).
  Proof.
    intros Hok. iIntros "H1 H2 H3 H4 H5".
    rewrite (cw2_frames dq dq2 r v0 r2 v2 Hok). iFrame.
  Qed.

  Lemma cw2_frames_out (dq dq2 : dfrac) (r : register)
      (v0 : type_of_register r) (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    (hreg_frame (cw2_rs r v0 r2 v2) (cw_Drw r) ∗
     hreg_frame_ro (cw2_Df dq dq2 r2) (cw2_rs r v0 r2 v2) (cw2_Dro r2)
     : iProp Σ) -∗
    (reg_pointsto r (DfracOwn 1) v0 ∗
     reg_pointsto r2 dq2 v2 ∗
     reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hok. rewrite (cw2_frames dq dq2 r v0 r2 v2 Hok).
    iIntros "H". iExact "H".
  Qed.

  (* the post-write file at the parametric tower, [cw_set_agree]'s twin *)
  Lemma cw2_set_agree (r : register) (v0 vnew : type_of_register r)
      (r2 : register) (v2 : type_of_register r2) :
    cw2_ok r r2 ->
    reg_agree_on (cw_Drw r ∪ cw2_Dro r2)
      (register_set r vnew (cw2_rs r v0 r2 v2)) (cw2_rs r vnew r2 v2).
  Proof.
    intros Hok. pose proof Hok as (Hfr & Hfr2 & Hne).
    pose proof Hfr as (H1 & H2 & H3).
    destruct (cw_fresh_ne r2 Hfr2) as (N1 & N2 & N3).
    intros q Hq. rewrite /cw_Drw /cw2_Dro /cw_Dro in Hq.
    repeat (apply elem_of_union in Hq as [Hq|Hq]);
      apply elem_of_singleton in Hq; subst q.
    - etransitivity; [apply register_lookup_set|].
      symmetry. apply (cw2_rs_r r vnew r2 v2 Hok).
    - etransitivity;
        [apply irrelevant_register_set;
         exact (register_beq_false r2 r (fun H => Hne (eq_sym H)))|].
      etransitivity; [apply (cw2_rs_r2 r v0 r2 v2)|].
      symmetry. apply (cw2_rs_r2 r vnew r2 v2).
    - etransitivity; [apply irrelevant_register_set; exact H3|].
      etransitivity; [apply (cw2_rs_priv r v0 r2 v2 Hok)|].
      symmetry. apply (cw2_rs_priv r vnew r2 v2 Hok).
    - etransitivity; [apply irrelevant_register_set; exact H2|].
      etransitivity; [apply (cw2_rs_sec r v0 r2 v2 Hok)|].
      symmetry. apply (cw2_rs_sec r vnew r2 v2 Hok).
    - etransitivity; [apply irrelevant_register_set; exact H1|].
      etransitivity; [apply (cw2_rs_misa r v0 r2 v2 Hok)|].
      symmetry. apply (cw2_rs_misa r vnew r2 v2 Hok).
  Qed.

  Lemma cw2_rw_ext (r : register) (rs rs' : regstate) :
    reg_agree_on (cw_Drw r) rs rs' ->
    hreg_frame rs (cw_Drw r) -∗ (hreg_frame rs' (cw_Drw r) : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ (cw_Drw r) Hag).
    iIntros "H". iExact "H".
  Qed.

  Lemma cw2_ro_ext (dq dq2 : dfrac) (r2 : register) (rs rs' : regstate) :
    reg_agree_on (cw2_Dro r2) rs rs' ->
    hreg_frame_ro (cw2_Df dq dq2 r2) rs (cw2_Dro r2) -∗
    (hreg_frame_ro (cw2_Df dq dq2 r2) rs' (cw2_Dro r2) : iProp Σ).
  Proof.
    intros Hag.
    rewrite (hreg_frame_ro_ext (cw2_Df dq dq2 r2) _ _ (cw2_Dro r2) Hag).
    iIntros "H". iExact "H".
  Qed.

  (* the read-only prefix, transported by [goodb] from the exec stack's fact.
     Access-type-generic: the legality check reads the same three cells at
     CSRRead as at CSRWrite, and nothing in the transport looks at the type. *)
  Lemma hval_check_CSR_result (D Drw : gset register) (rs : regstate)
      (csr : SailStdpp.Values.mword 12) (at_ : CSRAccessType) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    goodb D_m (check_CSR_result csr Machine at_) dstateM = true ->
    exec (check_CSR_result csr Machine at_) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    hval D Drw rs (check_CSR_result csr Machine at_)
      (CSR_Check_OK tt) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm Hgb Hex.
    exact (hval_of_goodb D_m D Drw _ dstateM rs (CSR_Check_OK tt)
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm) Hgb Hex).
  Qed.

  (* [Ox"..."] is not available in this import context (stdpp's monadic
     pattern notation shadows the literal syntaxes), so the two mip/sip CSR
     numbers are spelled out. *)
  Local Notation csr344 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "344" 0)).
  Local Notation csr144 :=
    (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 12)
       (HexString.Raw.to_N "144" 0)).

  (* ------------------------------------------------------------------ *)
  (* [doCSR] at CSRRW with rd = x0, peeled.  Mirrors                      *)
  (* [WpGprCsrwCommon.exec_doCSR_csrw_p] step for step; the per-CSR facts  *)
  (* (the check's goodb + exec, the write's hfrun, the callback's pure     *)
  (* equation) are premises, so this lemma is written once for all ten.    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_doCSR_csrw (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs' : regstate) (csr : SailStdpp.Values.mword 12)
      (v cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    ext_check_CSR csr Machine CSRWrite = true ->
    goodb D_m (check_CSR_result csr Machine CSRWrite) dstateM = true ->
    exec (check_CSR_result csr Machine CSRWrite) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    (if eq_vec csr csr344 then read_mip IncludePlatformInterrupts
     else if eq_vec csr csr144 then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64)) = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* the write as an OBLIGATION, not an [hfrun] fact: medeleg and mcounteren
       are three nodes at one register and discharge it by [swp_hfrun], but
       menvcfg and mepc wrap a READ-ONLY legalization several [hartSupports] /
       [currentlyEnabled] levels deep around their store -- goodb territory --
       and since that sits INSIDE a function that writes, goodb cannot take
       [write_CSR] whole.  So the lemma stops naming HOW the write happens. *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr v)
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    swp (doCSR csr v zreg CSRRW CSRWrite)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext Hgb Hex Hmip Hcb.
    iIntros "#Hcert Hrw Hro Hwr".
    unfold doCSR.
    (* 1. cur_privilege *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p) "(-> & Hrw & Hro)". rewrite Hpriv.
    (* 2. the legality check, goodb-transported *)
    iApply (swp_bind_use (check_CSR_result csr Machine CSRWrite) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj
                (hval_check_CSR_result (Drw ∪ Dro) Drw rs csr CSRWrite HDpriv
                   HDsec HDmisa Hpriv Hsec Hmisa Hgb Hex)
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    (* 3. cur_privilege again, then the pure gates *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p2) "(-> & Hrw & Hro)". rewrite Hpriv Hext.
    change (Riscv.rv64d.not true) with false. cbn match.
    replace (if Instances.generic_neq CSRWrite CSRWrite then read_CSR csr
             else returnM (zeros' 64))
      with (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) by reflexivity.
    iApply (swp_bind_use (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = zeros' 64⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (rv) "(-> & Hrw & Hro)".
    rewrite Hmip.
    iApply (swp_bind_use (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = zeros' 64⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (rv2) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRWrite CSRRead) with false
      by reflexivity. cbn match.
    (* 4. the write -- a computed walk at the ONE concrete CSR *)
    iApply (swp_bind_use (write_CSR csr v) _ _ _ with "[Hwr Hrw Hro] [-]").
    { iApply ("Hwr" with "Hrw Hro"). }
    iIntros (wres) "(-> & Hrw & Hro)". cbn match.
    (* 5. the discarded x0 write and the pure callback *)
    iApply (swp_bind0_use _ _
              (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I _
                with "[Hrw Hro] [-]").
      { change (wX_bits zreg (zeros' 64)) with (Defs.returnm tt : M unit).
        iApply swp_ret. by iFrame. }
      iIntros (u) "[Hrw Hro]". rewrite Hcb. iApply swp_ret. by iFrame. }
    iIntros (u2) "[Hrw Hro]". iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [execute_CSRReg csr rs1 x0 CSRRW]: peel the ONE symbolic-index node    *)
  (* and hand the rest to [swp_doCSR_csrw].  [gpr_file] rides beside the    *)
  (* frame -- the GPRs are deliberately NOT in the footprint.               *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_CSRReg_csrw (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (rs1 : SailStdpp.Values.mword 5)
      (cfinal : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = Values.mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    ext_check_CSR csr Machine CSRWrite = true ->
    goodb D_m (check_CSR_result csr Machine CSRWrite) dstateM = true ->
    exec (check_CSR_result csr Machine CSRWrite) dstateM
      = Some (CSR_Check_OK tt, dstateM) ->
    (if eq_vec csr csr344 then read_mip IncludePlatformInterrupts
     else if eq_vec csr csr144 then read_sip IncludePlatformInterrupts
     else returnM (zeros' 64)) = (returnM (zeros' 64) : M (SailStdpp.Values.mword 64)) ->
    csr_id_write_callback csr cfinal = Defs.returnm tt ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (write_CSR csr (m !!! Regidx rs1))
         (fun x => ⌜x = Values.Ok cfinal⌝ ∗
                   hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)) -∗
    swp (execute_CSRReg csr (Regidx rs1) zreg CSRRW)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext Hgb Hex Hmip Hcb.
    iIntros "#Hcert Hf Hrw Hro Hwr".
    unfold execute_CSRReg.
    replace (csr_access_type CSRRW (Instances.generic_eq zreg zreg)
               (Instances.generic_eq (Regidx rs1) zreg))
      with CSRWrite
      by (replace (Instances.generic_eq zreg zreg) with true by reflexivity;
          reflexivity).
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (v) "[-> Hf]".
    iApply (swp_mono with "[Hf] [Hrw Hro Hwr]");
      [| iApply (swp_doCSR_csrw Drw Dro Df rs rs' csr (m !!! Regidx rs1)
                   cfinal Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa Hext
                   Hgb Hex Hmip Hcb with "Hcert Hrw Hro Hwr") ].
    iIntros (e) "(-> & Hrw & Hro)". iSplitR; [done|]. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE READ-SIDE FOOTPRINT.  A csrr writes no register at all: the CSR   *)
  (* is read and rd lives in [gpr_file], which is outside every frame.     *)
  (* So the writable half is EMPTY and the read set is the three config    *)
  (* pins plus the CSR cell -- i.e. exactly [cw_Drw r ∪ cw_Dro], the same  *)
  (* set the csrw side reads, with the CSR moved to the read-only side.    *)
  (*                                                                      *)
  (* Two fractions, not one: the config pins arrive as a fraction of       *)
  (* [mmode_config] the leaf kept back, while the CSR cell is whatever the *)
  (* leaf happens to hold (full, for a cell of its own).                   *)
  (* ------------------------------------------------------------------ *)
  Definition cr_Dro (r : register) : gset register := cw_Drw r ∪ cw_Dro.

  Definition cr_Df (dqp dqc : dfrac) (r : register) : register -> dfrac :=
    fun r' =>
      if decide (r' = (misa : register)) then DfracDiscarded
      else if decide (r' = (mseccfg : register)) then DfracDiscarded
      else if decide (r' = r) then dqc else dqp.

  Lemma cr_disj (r : register) : (∅ : gset register) ## cr_Dro r.
  Proof. set_solver. Qed.

  Lemma cr_in_r (r : register) : r ∈ (∅ : gset register) ∪ cr_Dro r.
  Proof. rewrite /cr_Dro /cw_Drw. set_solver. Qed.
  Lemma cr_in_priv (r : register) :
    (cur_privilege : register) ∈ (∅ : gset register) ∪ cr_Dro r.
  Proof. rewrite /cr_Dro /cw_Dro. set_solver. Qed.
  Lemma cr_in_sec (r : register) :
    (mseccfg : register) ∈ (∅ : gset register) ∪ cr_Dro r.
  Proof. rewrite /cr_Dro /cw_Dro. set_solver. Qed.
  Lemma cr_in_misa (r : register) :
    (misa : register) ∈ (∅ : gset register) ∪ cr_Dro r.
  Proof. rewrite /cr_Dro /cw_Dro. set_solver. Qed.

  (* the empty writable frame, which is what "writes nothing" costs *)
  Lemma hreg_frame_empty (rs : regstate) :
    ⊢ (hreg_frame rs ∅ : iProp Σ).
  Proof. rewrite /hreg_frame big_sepS_empty. auto. Qed.

  Lemma cr_Df_misa dqp dqc r : cr_Df dqp dqc r misa = DfracDiscarded.
  Proof. rewrite /cr_Df. repeat case_decide; congruence. Qed.
  Lemma cr_Df_sec dqp dqc r : cr_Df dqp dqc r mseccfg = DfracDiscarded.
  Proof. rewrite /cr_Df. repeat case_decide; congruence. Qed.
  Lemma cr_Df_priv dqp dqc r :
    cw_fresh r -> cr_Df dqp dqc r cur_privilege = dqp.
  Proof.
    intros Hfr. pose proof (cw_fresh_ne r Hfr) as (_ & _ & Npriv).
    rewrite /cr_Df. repeat case_decide; congruence.
  Qed.
  Lemma cr_Df_r dqp dqc r : cw_fresh r -> cr_Df dqp dqc r r = dqc.
  Proof.
    intros Hfr. pose proof (cw_fresh_ne r Hfr) as (Nmisa & Nsec & _).
    rewrite /cr_Df. repeat case_decide; congruence.
  Qed.

  Lemma cr_frames (dqp dqc : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame_ro (cr_Df dqp dqc r) (cw_rs r v0) (cr_Dro r) : iProp Σ)
    ⊣⊢ (reg_pointsto r dqc v0 ∗
        reg_pointsto cur_privilege dqp Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr.
    rewrite /hreg_frame_ro /cr_Dro.
    rewrite (big_sepS_union _ (cw_Drw r) cw_Dro (cw_disj r Hfr)).
    rewrite /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite cw_rs_r (cw_rs_priv r v0 Hfr) (cw_rs_sec r v0 Hfr)
      (cw_rs_misa r v0 Hfr).
    rewrite (cr_Df_r dqp dqc r Hfr) (cr_Df_priv dqp dqc r Hfr)
      (cr_Df_sec dqp dqc r) (cr_Df_misa dqp dqc r).
    by rewrite !bi.sep_assoc.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE THREE PINS ALONE, for a csrr whose CSR cell the leaf does NOT     *)
  (* own ([time]).  The read of that cell is then UNPINNED -- outside       *)
  (* [Drw ∪ Dro] -- which the span allows and [swp_read_reg_any] takes.     *)
  (* ------------------------------------------------------------------ *)
  Definition cr0_rs : regstate :=
    register_set misa MISA_C
      (register_set mseccfg (Values.mword_of_int 0)
         (register_set cur_privilege Machine init_regstate)).

  Lemma cr0_rs_misa : register_lookup misa cr0_rs = MISA_C.
  Proof. rewrite /cr0_rs. apply register_lookup_set. Qed.
  Lemma cr0_rs_sec : register_lookup mseccfg cr0_rs = Values.mword_of_int 0.
  Proof.
    rewrite /cr0_rs.
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.
  Lemma cr0_rs_priv : register_lookup cur_privilege cr0_rs = Machine.
  Proof.
    rewrite /cr0_rs.
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
    apply register_lookup_set.
  Qed.

  Lemma cr0_disj : (∅ : gset register) ## cw_Dro.
  Proof. set_solver. Qed.
  Lemma cr0_in_priv : (cur_privilege : register) ∈ (∅ : gset register) ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cr0_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.
  Lemma cr0_in_misa : (misa : register) ∈ (∅ : gset register) ∪ cw_Dro.
  Proof. rewrite /cw_Dro. set_solver. Qed.

  Lemma cr0_frames (dqp : dfrac) :
    (hreg_frame_ro (cw_Df dqp) cr0_rs cw_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto cur_privilege dqp Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame_ro /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite cr0_rs_priv cr0_rs_sec cr0_rs_misa.
    rewrite (cw_Df_priv dqp) (cw_Df_sec dqp) (cw_Df_misa dqp).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma cr0_frames_in (dqp : dfrac) :
    reg_pointsto cur_privilege dqp Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame cr0_rs ∅ ∗
     hreg_frame_ro (cw_Df dqp) cr0_rs cw_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3". iSplitR; [iApply hreg_frame_empty|].
    rewrite (cr0_frames dqp). iFrame.
  Qed.

  Lemma cr0_frames_out (dqp : dfrac) :
    (hreg_frame_ro (cw_Df dqp) cr0_rs cw_Dro : iProp Σ) -∗
    (reg_pointsto cur_privilege dqp Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. rewrite (cr0_frames dqp). iIntros "H". iExact "H". Qed.

  Lemma cr_frames_in (dqp dqc : dfrac) (r : register)
      (v0 : type_of_register r) :
    cw_fresh r ->
    reg_pointsto r dqc v0 -∗
    reg_pointsto cur_privilege dqp Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (cw_rs r v0) ∅ ∗
     hreg_frame_ro (cr_Df dqp dqc r) (cw_rs r v0) (cr_Dro r) : iProp Σ).
  Proof.
    intros Hfr. iIntros "H1 H2 H3 H4".
    iSplitR; [iApply hreg_frame_empty|].
    rewrite (cr_frames dqp dqc r v0 Hfr). iFrame.
  Qed.

  Lemma cr_frames_out (dqp dqc : dfrac) (r : register)
      (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame_ro (cr_Df dqp dqc r) (cw_rs r v0) (cr_Dro r) : iProp Σ) -∗
    (reg_pointsto r dqc v0 ∗
     reg_pointsto cur_privilege dqp Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hfr. rewrite (cr_frames dqp dqc r v0 Hfr). iIntros "H". iExact "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* TWO [hval] PEELS, for the stretches [hfrun] cannot walk.              *)
  (*                                                                      *)
  (* [hfrun] answers a read from the pinned file, so every register it      *)
  (* reads must be in [D] -- i.e. owned.  A stretch whose RESULT does not   *)
  (* depend on what it read needs neither: the span's read case is          *)
  (* ungated, so the value is simply ∀-quantified.  This is the [tk_peel_   *)
  (* any] move of [HartMCycle.tick_clock_hvalE], as a lemma rather than an  *)
  (* Ltac.  (Both belong in HartSpanChar once a second family wants them.)  *)
  (* ------------------------------------------------------------------ *)
  Lemma hval_ret {X : Type} (D Drw : gset register) (rs : regstate) (x : X) :
    hval D Drw rs (Interface.Ret x) x rs.
  Proof.
    intros rs0 l Hag Hchain Hstop.
    rewrite (hspan_stop_refl D Drw (Interface.Ret x) rs0 l
               (eq_refl : hspan_stops Drw (Interface.Ret x) = true) Hchain).
    cbn.
    split; [reflexivity | exact Hag].
  Qed.

  Lemma hval_read_any {X : Type} (D Drw : gset register) (r : register)
      (rs : regstate) (m : M X) (x : X) (rs' : regstate) :
    hregread_at r m = true ->
    (forall v : type_of_register r,
       hval D Drw rs (hregread_resume r v m) x rs') ->
    hval D Drw rs m x rs'.
  Proof.
    intros Hat Hrest rs0 l Hag Hchain Hstop.
    assert (Hns : hspan_stops Drw m = false).
    { destruct (hregread_at_inv r m Hat) as (ak & K & -> & _). reflexivity. }
    apply hspan_peel in Hchain; [| exact Hns | exact Hstop].
    destruct Hchain as (c & Hstep & Hchain).
    destruct (hspani_read_any_inv D Drw r m rs0 c Hat Hstep)
      as (v & rs1 & Hag1 & ->).
    apply (Hrest v rs1 l); [| exact Hchain | exact Hstop].
    intros q Hq. rewrite (Hag1 q Hq). exact (Hag q Hq).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [doCSR] at CSRRS with rs1 = x0 -- a plain [csrr rd, csr].            *)
  (*                                                                      *)
  (* [swp_doCSR_csrw]'s mirror, and the CSR READ is an obligation for the  *)
  (* same reason the write is one.  [read_CSR] is read-only, so [goodb]    *)
  (* certifies its SHAPE -- but its VALUE is the caller's own register     *)
  (* content, and [hval_of_goodb] transports only reads whose values are   *)
  (* pinned at the reference state.  So the lemma stops naming what the    *)
  (* CSR reads, exactly as the csrw one stops naming how the write         *)
  (* happens.                                                             *)
  (*                                                                      *)
  (* [rs1_val] is universally quantified: the read path never uses it, so  *)
  (* the caller need not know what x0 reads as.                           *)
  (*                                                                      *)
  (* The rd write is INSIDE [doCSR] on this path (unlike csrw, where it is *)
  (* at x0 and vanishes), so [gpr_file] is threaded through here.          *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_doCSR_csrr_gen (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (m : regfile) (csr : SailStdpp.Values.mword 12)
      (rd : SailStdpp.Values.mword 5)
      (rs1_val : SailStdpp.Values.mword 64)
      (Q : SailStdpp.Values.mword 64 -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    uint rd <> 0 ->
    ext_check_CSR csr Machine CSRRead = true ->
    (* THE LEGALITY CHECK, as an [hval] rather than as a [goodb] transport:
       [time]'s check reads the counter-enable cells, which no leaf owns, so
       its route into [hval] is a ∀-peel and not the reference-state
       transport.  The engine only needs the conclusion. *)
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr Machine CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => Q x ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (doCSR csr rs1_val (Regidx rd) CSRRS CSRRead)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ x : SailStdpp.Values.mword 64, Q x ∗
                gpr_file (<[Regidx rd := regval_into_reg x]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    unfold doCSR.
    (* 1. cur_privilege *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p) "(-> & Hrw & Hro)". rewrite Hpriv.
    (* 2. the legality check, goodb-transported *)
    iApply (swp_bind_use (check_CSR_result csr Machine CSRRead) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ (CSR_Check_OK tt) Hdisj Hchk
                with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". cbn match.
    (* 3. cur_privilege again, then the pure gate *)
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs cur_privilege Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (p2) "(-> & Hrw & Hro)". rewrite Hpriv Hext.
    change (Riscv.rv64d.not true) with false. cbn match.
    (* 4. the CSR read -- the caller's obligation *)
    replace (if Instances.generic_neq CSRRead CSRWrite then read_CSR csr
             else returnM (zeros' 64))
      with (read_CSR csr : M (SailStdpp.Values.mword 64)) by reflexivity.
    iApply (swp_bind_use (read_CSR csr) _ _ _ with "[Hrdcsr Hrw Hro] [-]").
    { iApply ("Hrdcsr" with "Hrw Hro"). }
    iIntros (rv) "(HQ & Hrw & Hro)".
    (* 5. NOT mip/sip, so [dest_val] is the value just read *)
    rewrite H344 H144.
    iApply (swp_bind_use (returnM rv : M (SailStdpp.Values.mword 64)) _
              (fun x => ⌜x = rv⌝ ∗ hreg_frame rs Drw ∗
                        hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
    { iApply swp_ret. by iFrame. }
    iIntros (dv) "(-> & Hrw & Hro)".
    replace (Instances.generic_eq CSRRead CSRRead) with true
      by reflexivity. cbn match.
    (* 6. the pure callback, then the rd write *)
    iApply (swp_bind0_use _ _
              (fun _ => gpr_file (<[Regidx rd := regval_into_reg rv]> m) ∗
                        hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hf Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => gpr_file m ∗
                          hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hf Hrw Hro] [-]").
      { rewrite (Hcb rv). iApply swp_ret. by iFrame. }
      iIntros (u) "(Hf & Hrw & Hro)".
      iApply (swp_mono with "[Hrw Hro] [-]");
        [| iApply (swp_wX_file rd m rv Hrd with "Hcert Hf") ].
      iIntros (u2) "Hf". by iFrame. }
    iIntros (u3) "(Hf & Hrw & Hro)". iApply swp_ret.
    iSplitR; [done|]. iExists rv. iFrame.
  Qed.

  (* [execute_CSRReg csr x0 rd CSRRS]: peel the x0 source read and hand the
     rest to [swp_doCSR_csrr_gen].  The value read is irrelevant (see above),
     so nothing here needs to know that x0 reads as zero. *)
  Lemma swp_execute_CSRReg_csrr_gen (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (rd : SailStdpp.Values.mword 5)
      (Q : SailStdpp.Values.mword 64 -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    uint rd <> 0 ->
    ext_check_CSR csr Machine CSRRead = true ->
    (* THE LEGALITY CHECK, as an [hval] rather than as a [goodb] transport:
       [time]'s check reads the counter-enable cells, which no leaf owns, so
       its route into [hval] is a ∀-peel and not the reference-state
       transport.  The engine only needs the conclusion. *)
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr Machine CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => Q x ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (execute_CSRReg csr zreg (Regidx rd) CSRRS)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                ∃ x : SailStdpp.Values.mword 64, Q x ∗
                gpr_file (<[Regidx rd := regval_into_reg x]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    unfold execute_CSRReg.
    (* [csr_access_type]'s arguments are (rd = x0, rs1 = x0): here rs1 IS x0,
       and CSRRS with a zero SOURCE is a read whatever rd is. *)
    replace (csr_access_type CSRRS (Instances.generic_eq (Regidx rd) zreg)
               (Instances.generic_eq zreg zreg))
      with CSRRead
      by (replace (Instances.generic_eq zreg zreg) with true by reflexivity;
          destruct (Instances.generic_eq (Regidx rd) zreg); reflexivity).
    (* the x0 SOURCE read, peeled at [cli_rs1] (the zero index by name --
       [WpMmodeLeafBase]; the literal syntax is not available in this import
       context, see the csr344 note above) *)
    change zreg with (Regidx cli_rs1).
    iApply (swp_bind_use (rX_bits (Regidx cli_rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file cli_rs1 m with "Hcert Hf"). }
    iIntros (v) "[-> Hf]".
    iApply (swp_doCSR_csrr_gen Drw Dro Df rs m csr rd _ Q Hdisj HDpriv
              Hpriv Hrd Hext Hchk H344 H144 Hcb
              with "Hcert Hf Hrw Hro Hrdcsr").
  Qed.

  (* the PINNED corollary, which is what a leaf holding the CSR cell wants:
     the read value is named, so the continuation's GPR file is concrete and
     no existential reaches the leaf statement. *)
  Lemma swp_execute_CSRReg_csrr (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (m : regfile)
      (csr : SailStdpp.Values.mword 12) (rd : SailStdpp.Values.mword 5)
      (readval : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    uint rd <> 0 ->
    ext_check_CSR csr Machine CSRRead = true ->
    (* THE LEGALITY CHECK, as an [hval] rather than as a [goodb] transport:
       [time]'s check reads the counter-enable cells, which no leaf owns, so
       its route into [hval] is a ∀-peel and not the reference-state
       transport.  The engine only needs the conclusion. *)
    hval (Drw ∪ Dro) Drw rs (check_CSR_result csr Machine CSRRead)
      (CSR_Check_OK tt) rs ->
    eq_vec csr csr344 = false ->
    eq_vec csr csr144 = false ->
    (forall x, csr_id_read_callback csr x = Defs.returnm tt) ->
    gen_cert -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_CSR csr)
         (fun x => ⌜x = readval⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (execute_CSRReg csr zreg (Regidx rd) CSRRS)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg readval]> m) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv Hpriv Hrd Hext Hchk H344 H144 Hcb.
    iIntros "#Hcert Hf Hrw Hro Hrdcsr".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_execute_CSRReg_csrr_gen Drw Dro Df rs m csr rd
                   (fun x => ⌜x = readval⌝)%I Hdisj HDpriv
                   Hpriv Hrd Hext Hchk H344 H144 Hcb
                   with "Hcert Hf Hrw Hro Hrdcsr") ].
    iIntros (e) "(-> & H)".
    iDestruct "H" as (x) "(-> & Hf & Hrw & Hro)". by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* READING A REGISTER NOBODY OWNS.  [swp_read_reg_cell] reads a cell the *)
  (* leaf holds and pins the value; [swp_read_reg_pinned] does the same at  *)
  (* a frame.  A csrr of [time] can do neither: mtime is written by the     *)
  (* clock tick, so it lives in the WRAPPER's writable frame and no leaf     *)
  (* can hold a fraction of it.  The node still steps -- the span's read     *)
  (* case is ungated -- it just returns a value the leaf cannot name, which  *)
  (* is exactly why [wp_csrr_time_gpr]'s continuation quantifies it.         *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_read_reg_any (r : register) (Φ : type_of_register r -> iProp Σ) :
    gen_cert -∗ (∀ v : type_of_register r, Φ v) -∗ swp (Defs.read_reg r) Φ.
  Proof.
    iIntros "#Hcert HΦ".
    iApply (swp_hart_regread with "Hcert").
    { cbn [hregread_at]. apply bool_decide_eq_true_2. reflexivity. }
    iIntros (σ) "Hsi".
    iApply fupd_mask_intro; [apply empty_subseteq|].
    iIntros "Hcl". iNext. iMod "Hcl" as "_". iModIntro. iFrame "Hsi".
    rewrite hregread_resume_red.
    iApply swp_ret. iApply "HΦ".
  Qed.

  (* the post-write file: [write_CSR] leaves a [register_set], which agrees
     with the tower that simply NAMES the new value *)
  Lemma cw_set_agree (r : register) (v0 vnew : type_of_register r) :
    cw_fresh r ->
    reg_agree_on (cw_Drw r ∪ cw_Dro)
      (register_set r vnew (cw_rs r v0)) (cw_rs r vnew).
  Proof.
    intros Hfr r' Hr'.
    pose proof Hfr as Hfr2. destruct Hfr2 as (H1 & H2 & H3).
    rewrite /cw_Drw /cw_Dro in Hr'.
    repeat (apply elem_of_union in Hr' as [Hr'|Hr']);
      apply elem_of_singleton in Hr'; subst r'.
    - etransitivity; [apply register_lookup_set|]. symmetry. apply cw_rs_r.
    - etransitivity; [apply irrelevant_register_set; exact H3|].
      etransitivity; [apply (cw_rs_priv r v0 Hfr)|].
      symmetry. apply (cw_rs_priv r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H2|].
      etransitivity; [apply (cw_rs_sec r v0 Hfr)|].
      symmetry. apply (cw_rs_sec r vnew Hfr).
    - etransitivity; [apply irrelevant_register_set; exact H1|].
      etransitivity; [apply (cw_rs_misa r v0 Hfr)|].
      symmetry. apply (cw_rs_misa r vnew Hfr).
  Qed.

  Lemma cw_frames_in (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    reg_pointsto r (DfracOwn 1) v0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ).
  Proof. intros Hfr. iIntros "H1 H2 H3 H4". rewrite (cw_frames dq r v0 Hfr). iFrame. Qed.

  Lemma cw_frames_out (dq : dfrac) (r : register) (v0 : type_of_register r) :
    cw_fresh r ->
    (hreg_frame (cw_rs r v0) (cw_Drw r) ∗
     hreg_frame_ro (cw_Df dq) (cw_rs r v0) cw_Dro : iProp Σ) -∗
    (reg_pointsto r (DfracOwn 1) v0 ∗
     reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. intros Hfr. rewrite (cw_frames dq r v0 Hfr). iIntros "H". iExact "H". Qed.

  Lemma cw_rw_ext (r : register) (rs rs' : regstate) :
    reg_agree_on (cw_Drw r) rs rs' ->
    hreg_frame rs (cw_Drw r) -∗ (hreg_frame rs' (cw_Drw r) : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ (cw_Drw r) Hag).
    iIntros "H". iExact "H".
  Qed.

  Lemma cw_ro_ext (dq : dfrac) (rs rs' : regstate) :
    reg_agree_on cw_Dro rs rs' ->
    hreg_frame_ro (cw_Df dq) rs cw_Dro -∗
    (hreg_frame_ro (cw_Df dq) rs' cw_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext (cw_Df dq) _ _ cw_Dro Hag).
    iIntros "H". iExact "H".
  Qed.

End csrw.
