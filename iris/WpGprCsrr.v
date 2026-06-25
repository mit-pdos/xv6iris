From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Register-generic CSR-read execute: csrr rd, mhartid (= csrrs rd,mhartid,x0).*)
(* The CSR read (mhartid) and the x0 source stay fixed; only the           *)
(* destination [rd] is generalized.  CSRRS with a zero source always yields  *)
(* access type CSRRead, independent of rd.                                   *)
(* ====================================================================== *)
Lemma csr_access_type_CSRRS_true (b : bool) : csr_access_type CSRRS b true = CSRRead.
Proof. destruct b; reflexivity. Qed.

Lemma exec_execute_CSRReg_gpr_aux (rd : mword 5) s s_w :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs))) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr_csrr (Regidx i_rs1_csrr) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hwx.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS (generic_eq (Regidx rd) zreg)
             (generic_eq (Regidx i_rs1_csrr) zreg)) with CSRRead
    by (replace (generic_eq (Regidx i_rs1_csrr) zreg) with true by (vm_compute; reflexivity);
        symmetry; apply csr_access_type_CSRRS_true).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 i_rs1_csrr s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_csrr s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (not (ext_check_CSR csr_csrr Machine CSRRead)) with false
    by (vm_compute; reflexivity).
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr_csrr else returnM (zeros' 64))
    with (read_CSR csr_csrr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_csrr s)).
  match goal with |- exec (Defs.bind ?D ?K) s = _ =>
    replace D with (returnM (register_lookup mhartid s.(sregs)) : M (mword 64))
      by (vm_compute; reflexivity) end.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (register_lookup mhartid s.(sregs)) s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity.
  rewrite (exec_bind0_Some _ _ _ _ _ (_ :
    exec (Defs.bind0 (csr_id_read_callback csr_csrr (register_lookup mhartid s.(sregs)))
            (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs)))) s
      = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
        (exec_csr_id_read_callback_csrr s (register_lookup mhartid s.(sregs)))).
      exact Hwx. }
  apply exec_returnM.
Qed.

Lemma exec_execute_CSRReg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_csrr (Regidx i_rs1_csrr) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))).
Proof.
  intros Hrd Hpriv.
  apply (exec_execute_CSRReg_gpr_aux rd s
           (set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))) Hpriv).
  rewrite (exec_wX_bits_gpr rd (register_lookup mhartid s.(sregs)) s).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

(* ====================================================================== *)
(* exec-level register-generic csrr step (32-bit, F_Base, 4-aligned form).  *)
(* ====================================================================== *)
Section ForwardCsrrGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS), s0).

  Definition sAcg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pccg : mstate := set_reg sAcg nextPC (add_vec_int pc 4).
  Definition sXcg : mstate :=
    set_reg s_pccg (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (register_lookup mhartid s_pccg.(sregs))).
  Definition sTcg : mstate := set_reg sXcg PC (register_lookup nextPC sXcg.(sregs)).
  Definition sFcg' : mstate :=
    if b then set_reg sTcg minstret (add_vec_int (register_lookup minstret sTcg.(sregs)) 1)
         else sTcg.

  Lemma forward_exec_csrr_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFcg').
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAcg.(sregs) = pc).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAcg.(sregs) = Machine).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAcg.(sregs) = HART_ACTIVE tt).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAcg.(sregs) = zeros' 64).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAcg.(sregs))) ('b"1") = false).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAcg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAcg = Some (None, sAcg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAcg _ (exec_currentlyEnabled_S sAcg) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAcg = Some (F_Base w, sAcg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAcg
              = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS), sAcg))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege s_pccg.(sregs) = Machine).
    { unfold s_pccg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LprivA | vm_compute; reflexivity ]. }
    assert (HexecC : exec (execute (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS))) s_pccg
              = Some (RETIRE_SUCCESS, sXcg)).
    { change (execute (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_csrr (Regidx i_rs1_csrr) (Regidx rd) CSRRS).
      unfold sXcg. exact (exec_execute_CSRReg_gpr rd s_pccg Hrd0 LprivC). }
    assert (Hha : exec (run_hart_active 0) sAcg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcg)).
    { exact (exec_hart_active_progress sAcg sAcg sXcg sAcg w
               (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXcg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcg, s_pccg, sAcg; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcg, s_pccg, sAcg; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrrGpr.

(* mhartid is untouched by the post-fetch sets, so its value carries through. *)
Lemma mhartid_s_pccg (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mhartid s.(sregs) = v ->
  register_lookup mhartid (s_pccg s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccg, sAcg, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Ltac reg_ne_c := solve [ vm_compute; reflexivity
                       | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Ltac tmic := rewrite irrelevant_register_set; [ | reg_ne_c ].

Section CleanCsrrGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (mst0 : mword 64).
  Definition base_upd_cg : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (register_lookup mhartid (s_pccg s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccg : mstate :=
    if b then set_reg base_upd_cg minstret (add_vec_int mst0 1) else base_upd_cg.

  Lemma sFcg'_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcg' s pc b rd = sFccg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcg s pc b rd).(sregs) = add_vec_int pc 4).
    { unfold sXcg; cbv zeta. unfold set_reg; cbn [sregs].
      tmic. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcg s pc b rd = base_upd_cg).
    { unfold sTcg. rewrite Enpc. unfold sXcg, s_pccg, sAcg; cbv zeta.
      unfold base_upd_cg, s_pccg, sAcg. reflexivity. }
    unfold sFcg', sFccg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cg.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cg, set_reg; cbn [sregs]. do 4 tmic. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrrGpr.

(* ====================================================================== *)
(* The register-GENERIC csrr WP: ONE lemma for `csrr rd, mhartid`, ANY rd.  *)
(* GPRs held as the single [gpr_file]; mhartid and other CSRs separate.     *)
(* ====================================================================== *)
Section WpCsrrGpr.
  Context `{!riscvGS Σ}.

  Lemma wp_csrr_gpr (pc : mword 64) (w : mword 32) (rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd mhartid_in : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mhartid ↦ᵣ mhartid_in -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg mhartid_in]> m) -∗
        mhartid ↦ᵣ mhartid_in -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmh")    as %Lmh.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmhv : register_lookup mhartid (s_pccg s pc b1).(sregs) = mhartid_in)
      by (apply mhartid_s_pccg; exact Lmh).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccg s pc b1 rd mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcg'_eq s pc b1 rd mst0 Lpc Lmst).
      apply (forward_exec_csrr_gpr s pc b1 w rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (register_lookup mhartid (s_pccg s pc b1).(sregs))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmhv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg mhartid_in) with "Hrdc") as "Hfile".
    unfold sFccg, base_upd_cg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_csrr_gpr] serves many destination regs.    *)
(* ====================================================================== *)
Section WpCsrrGprDemo.
  Context `{!riscvGS Σ}.
  Definition wp_csrr_x5  (pc : mword 64) (w : mword 32) := wp_csrr_gpr pc w (mword_of_int 5).
  Definition wp_csrr_x28 (pc : mword 64) (w : mword 32) := wp_csrr_gpr pc w (mword_of_int 28).
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpCsrrGprDemo.
