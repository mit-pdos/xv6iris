From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
Local Open Scope Z_scope.

(* ---- base execute lemmas (take rX/wX facts), mirror exec_execute_ITYPE_ADDI ---- *)
Lemma exec_execute_SHIFTIOP_SLLI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SLLI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SLLI))) with (execute_SHIFTIOP shamt rs1 rd SLLI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Lemma exec_execute_SHIFTIOP_SRLI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SRLI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SRLI))) with (execute_SHIFTIOP shamt rs1 rd SRLI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Lemma exec_execute_ADDIW_base (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0))) s = Some (tt, s') ->
  exec (execute (ADDIW (imm, rs1, rd))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (ADDIW (imm, rs1, rd))) with (execute_ADDIW imm rs1 rd).
  unfold execute_ADDIW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

(* ---- register-generic value functions + execute lemmas ---- *)
Definition gpr_src (rs1 : mword 5) (s : mstate) : mword 64 :=
  if Z.eqb (uint rs1) 0 then zero_reg
  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs).

Definition gpr_slli_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_left (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).
Definition gpr_srli_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_right (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).
Definition gpr_addiw_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec (add_vec (gpr_src rs1 s) (sign_extend' 64 imm)) 31 0).

Lemma exec_execute_SHIFTIOP_SLLI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_slli_val rs1 shamt s))).
Proof.
  unfold gpr_slli_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SLLI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma exec_execute_SHIFTIOP_SRLI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srli_val rs1 shamt s))).
Proof.
  unfold gpr_srli_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SRLI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma exec_execute_ADDIW_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ADDIW (imm, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_addiw_val rs1 imm s))).
Proof.
  unfold gpr_addiw_val, gpr_src.
  eapply exec_execute_ADDIW_base.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.


(* ===== slli ===== *)
Lemma slli_val_file (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (shamt : mword 6) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_slli_val rs1 shamt (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
  = shift_bits_left va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).
Proof.
  intros H1 Lva. unfold gpr_slli_val, gpr_src.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section Forward_slli.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (shamt : mword 6).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI), s0).

  Definition sA_slli : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pc_slli : mstate := set_reg sA_slli nextPC (add_vec_int pc 4).
  Definition sX_slli : mstate :=
    set_reg s_pc_slli (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_slli_val rs1 shamt s_pc_slli)).
  Definition sT_slli : mstate := set_reg sX_slli PC (register_lookup nextPC sX_slli.(sregs)).
  Definition sF_slli : mstate :=
    if b then set_reg sT_slli minstret (add_vec_int (register_lookup minstret sT_slli.(sregs)) 1)
         else sT_slli.

  Lemma forward_exec_slli_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF_slli).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sA_slli.(sregs) = pc).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sA_slli.(sregs) = Machine).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sA_slli.(sregs) = HART_ACTIVE tt).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sA_slli.(sregs))) ('b"1") = true).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sA_slli.(sregs))) ('b"1") = false).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sA_slli.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sA_slli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sA_slli = Some (None, sA_slli)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sA_slli _ (exec_currentlyEnabled_S sA_slli) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sA_slli = Some (F_Base w, sA_slli)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sA_slli = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI), sA_slli)) by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))) s_pc_slli = Some (RETIRE_SUCCESS, sX_slli)).
    { rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s_pc_slli).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sA_slli
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX_slli)).
    { exact (exec_hart_active_progress sA_slli sA_slli sX_slli sA_slli w
               (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sX_slli w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sX_slli, s_pc_slli, sA_slli; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sX_slli, s_pc_slli, sA_slli; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End Forward_slli.

Section Clean_slli.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (shamt : mword 6) (mst0 : mword 64).
  Definition baseupd_slli : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_slli_val rs1 shamt (s_pc_slli s pc b))))
            PC (add_vec_int pc 4).
  Definition sFc_slli : mstate :=
    if b then set_reg baseupd_slli minstret (add_vec_int mst0 1) else baseupd_slli.
  Lemma sF_slli_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sF_slli s pc b rs1 rd shamt = sFc_slli.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sX_slli s pc b rs1 rd shamt).(sregs) = add_vec_int pc 4).
    { unfold sX_slli; cbv zeta. unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sT_slli s pc b rs1 rd shamt = baseupd_slli).
    { unfold sT_slli. rewrite Enpc. unfold sX_slli, s_pc_slli, sA_slli; cbv zeta.
      unfold baseupd_slli, s_pc_slli, sA_slli. reflexivity. }
    unfold sF_slli, sFc_slli. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret baseupd_slli.(sregs) = register_lookup minstret s.(sregs)).
    { unfold baseupd_slli, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End Clean_slli.

Section Wp_slli.
  Context `{!riscvGS Σ}.
  Lemma wp_slli_gpr (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (shamt : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (shift_bits_left va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
        misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hr1 Hrd Hm1 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (st ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) st = Some (b1, st)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg st Lmc Lmcfg). }
    assert (Hav : gpr_slli_val rs1 shamt (s_pc_slli st pc b1) = shift_bits_left va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
      by (apply (slli_val_file st pc b1 rs1 shamt va Hr1 Lrs1)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 st
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFc_slli st pc b1 rs1 rd shamt mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sF_slli_eq st pc b1 rs1 rd shamt mst0 Lpc Lmst).
      apply (forward_exec_slli_gpr st pc b1 w rs1 rd shamt Hfetch_at Hsi_s Hrd Hdec Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_slli_val rs1 shamt (s_pc_slli st pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (shift_bits_left va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) with "Hrdc") as "Hfile".
    unfold sFc_slli, baseupd_slli. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End Wp_slli.


(* ===== srli ===== *)
Lemma srli_val_file (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (shamt : mword 6) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_srli_val rs1 shamt (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
  = shift_bits_right va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).
Proof.
  intros H1 Lva. unfold gpr_srli_val, gpr_src.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section Forward_srli.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (shamt : mword 6).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI), s0).

  Definition sA_srli : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pc_srli : mstate := set_reg sA_srli nextPC (add_vec_int pc 4).
  Definition sX_srli : mstate :=
    set_reg s_pc_srli (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srli_val rs1 shamt s_pc_srli)).
  Definition sT_srli : mstate := set_reg sX_srli PC (register_lookup nextPC sX_srli.(sregs)).
  Definition sF_srli : mstate :=
    if b then set_reg sT_srli minstret (add_vec_int (register_lookup minstret sT_srli.(sregs)) 1)
         else sT_srli.

  Lemma forward_exec_srli_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF_srli).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sA_srli.(sregs) = pc).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sA_srli.(sregs) = Machine).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sA_srli.(sregs) = HART_ACTIVE tt).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sA_srli.(sregs))) ('b"1") = true).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sA_srli.(sregs))) ('b"1") = false).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sA_srli.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sA_srli, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sA_srli = Some (None, sA_srli)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sA_srli _ (exec_currentlyEnabled_S sA_srli) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sA_srli = Some (F_Base w, sA_srli)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sA_srli = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI), sA_srli)) by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))) s_pc_srli = Some (RETIRE_SUCCESS, sX_srli)).
    { rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s_pc_srli).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sA_srli
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX_srli)).
    { exact (exec_hart_active_progress sA_srli sA_srli sX_srli sA_srli w
               (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sX_srli w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sX_srli, s_pc_srli, sA_srli; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sX_srli, s_pc_srli, sA_srli; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End Forward_srli.

Section Clean_srli.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (shamt : mword 6) (mst0 : mword 64).
  Definition baseupd_srli : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srli_val rs1 shamt (s_pc_srli s pc b))))
            PC (add_vec_int pc 4).
  Definition sFc_srli : mstate :=
    if b then set_reg baseupd_srli minstret (add_vec_int mst0 1) else baseupd_srli.
  Lemma sF_srli_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sF_srli s pc b rs1 rd shamt = sFc_srli.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sX_srli s pc b rs1 rd shamt).(sregs) = add_vec_int pc 4).
    { unfold sX_srli; cbv zeta. unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sT_srli s pc b rs1 rd shamt = baseupd_srli).
    { unfold sT_srli. rewrite Enpc. unfold sX_srli, s_pc_srli, sA_srli; cbv zeta.
      unfold baseupd_srli, s_pc_srli, sA_srli. reflexivity. }
    unfold sF_srli, sFc_srli. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret baseupd_srli.(sregs) = register_lookup minstret s.(sregs)).
    { unfold baseupd_srli, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End Clean_srli.

Section Wp_srli.
  Context `{!riscvGS Σ}.
  Lemma wp_srli_gpr (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (shamt : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (shift_bits_right va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
        misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hr1 Hrd Hm1 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (st ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) st = Some (b1, st)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg st Lmc Lmcfg). }
    assert (Hav : gpr_srli_val rs1 shamt (s_pc_srli st pc b1) = shift_bits_right va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
      by (apply (srli_val_file st pc b1 rs1 shamt va Hr1 Lrs1)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 st
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFc_srli st pc b1 rs1 rd shamt mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sF_srli_eq st pc b1 rs1 rd shamt mst0 Lpc Lmst).
      apply (forward_exec_srli_gpr st pc b1 w rs1 rd shamt Hfetch_at Hsi_s Hrd Hdec Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_srli_val rs1 shamt (s_pc_srli st pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (shift_bits_right va (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) with "Hrdc") as "Hfile".
    unfold sFc_srli, baseupd_srli. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End Wp_srli.


(* ===== addiw ===== *)
Lemma addiw_val_file (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (immv : mword 12) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_addiw_val rs1 immv (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
  = sign_extend' 64 (subrange_vec_dec (add_vec va (sign_extend' 64 immv)) 31 0).
Proof.
  intros H1 Lva. unfold gpr_addiw_val, gpr_src.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section Forward_addiw.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (immv : mword 12).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (ADDIW (immv, Regidx rs1, Regidx rd), s0).

  Definition sA_addiw : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pc_addiw : mstate := set_reg sA_addiw nextPC (add_vec_int pc 4).
  Definition sX_addiw : mstate :=
    set_reg s_pc_addiw (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_addiw_val rs1 immv s_pc_addiw)).
  Definition sT_addiw : mstate := set_reg sX_addiw PC (register_lookup nextPC sX_addiw.(sregs)).
  Definition sF_addiw : mstate :=
    if b then set_reg sT_addiw minstret (add_vec_int (register_lookup minstret sT_addiw.(sregs)) 1)
         else sT_addiw.

  Lemma forward_exec_addiw_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF_addiw).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sA_addiw.(sregs) = pc).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sA_addiw.(sregs) = Machine).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sA_addiw.(sregs) = HART_ACTIVE tt).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sA_addiw.(sregs))) ('b"1") = true).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sA_addiw.(sregs))) ('b"1") = false).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sA_addiw.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sA_addiw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sA_addiw = Some (None, sA_addiw)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sA_addiw _ (exec_currentlyEnabled_S sA_addiw) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sA_addiw = Some (F_Base w, sA_addiw)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sA_addiw = Some (ADDIW (immv, Regidx rs1, Regidx rd), sA_addiw)) by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (ADDIW (immv, Regidx rs1, Regidx rd))) s_pc_addiw = Some (RETIRE_SUCCESS, sX_addiw)).
    { rewrite (exec_execute_ADDIW_gpr rs1 rd immv s_pc_addiw).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sA_addiw
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX_addiw)).
    { exact (exec_hart_active_progress sA_addiw sA_addiw sX_addiw sA_addiw w
               (ADDIW (immv, Regidx rs1, Regidx rd)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sX_addiw w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sX_addiw, s_pc_addiw, sA_addiw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sX_addiw, s_pc_addiw, sA_addiw; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End Forward_addiw.

Section Clean_addiw.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (immv : mword 12) (mst0 : mword 64).
  Definition baseupd_addiw : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_addiw_val rs1 immv (s_pc_addiw s pc b))))
            PC (add_vec_int pc 4).
  Definition sFc_addiw : mstate :=
    if b then set_reg baseupd_addiw minstret (add_vec_int mst0 1) else baseupd_addiw.
  Lemma sF_addiw_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sF_addiw s pc b rs1 rd immv = sFc_addiw.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sX_addiw s pc b rs1 rd immv).(sregs) = add_vec_int pc 4).
    { unfold sX_addiw; cbv zeta. unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sT_addiw s pc b rs1 rd immv = baseupd_addiw).
    { unfold sT_addiw. rewrite Enpc. unfold sX_addiw, s_pc_addiw, sA_addiw; cbv zeta.
      unfold baseupd_addiw, s_pc_addiw, sA_addiw. reflexivity. }
    unfold sF_addiw, sFc_addiw. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret baseupd_addiw.(sregs) = register_lookup minstret s.(sregs)).
    { unfold baseupd_addiw, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End Clean_addiw.

Section Wp_addiw.
  Context `{!riscvGS Σ}.
  Lemma wp_addiw_gpr (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (immv : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (ADDIW (immv, Regidx rs1, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec va (sign_extend' 64 immv)) 31 0))]> m) -∗
        misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hr1 Hrd Hm1 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (st ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) st = Some (b1, st)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg st Lmc Lmcfg). }
    assert (Hav : gpr_addiw_val rs1 immv (s_pc_addiw st pc b1) = sign_extend' 64 (subrange_vec_dec (add_vec va (sign_extend' 64 immv)) 31 0))
      by (apply (addiw_val_file st pc b1 rs1 immv va Hr1 Lrs1)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 st
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFc_addiw st pc b1 rs1 rd immv mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sF_addiw_eq st pc b1 rs1 rd immv mst0 Lpc Lmst).
      apply (forward_exec_addiw_gpr st pc b1 w rs1 rd immv Hfetch_at Hsi_s Hrd Hdec Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addiw_val rs1 immv (s_pc_addiw st pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec va (sign_extend' 64 immv)) 31 0))) with "Hrdc") as "Hfile".
    unfold sFc_addiw, baseupd_addiw. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End Wp_addiw.


(* Demonstrations: ONE lemma per type serves many register operands. *)
Section WpGprShiftDemo.
  Context `{!riscvGS Σ}.
  Definition wp_slli_x5_x6  (pc : mword 64) (w : mword 32) (sh : mword 6) :=
    wp_slli_gpr pc w (mword_of_int 6) (mword_of_int 5) sh.    (* slli x5, x6, sh *)
  Definition wp_slli_x28_x1 (pc : mword 64) (w : mword 32) (sh : mword 6) :=
    wp_slli_gpr pc w (mword_of_int 1) (mword_of_int 28) sh.   (* slli x28, x1, sh *)
  Definition wp_srli_x5_x6  (pc : mword 64) (w : mword 32) (sh : mword 6) :=
    wp_srli_gpr pc w (mword_of_int 6) (mword_of_int 5) sh.
  Definition wp_srli_x28_x1 (pc : mword 64) (w : mword 32) (sh : mword 6) :=
    wp_srli_gpr pc w (mword_of_int 1) (mword_of_int 28) sh.
  Definition wp_sextw_x15_x15 (pc : mword 64) (w : mword 32) :=
    wp_addiw_gpr pc w (mword_of_int 15) (mword_of_int 15) (mword_of_int 0).  (* sext.w x15,x15 *)
  Definition wp_addiw_x5_x6 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_addiw_gpr pc w (mword_of_int 6) (mword_of_int 5) imm.
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 15 : mword 5)) = x15
    /\ uint (mword_of_int 28 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpGprShiftDemo.
