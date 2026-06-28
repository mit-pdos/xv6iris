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

(* register-generic ADDI execute: reads rs1 + immediate, writes rd, via the
   file-generic rX/wX lemmas -- works for ANY rd/rs1. *)
Definition gpr_addi_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (sign_extend' 64 imm).

Lemma exec_execute_ITYPE_ADDI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addi_val rs1 imm s))).
Proof.
  unfold gpr_addi_val.
  eapply exec_execute_ITYPE_ADDI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma gpr_addi_val_lookup (rs1 : mword 5) (imm : mword 12) (t : mstate) :
  uint rs1 <> 0 ->
  gpr_addi_val rs1 imm t
  = add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (sign_extend' 64 imm).
Proof.
  intros H1. unfold gpr_addi_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  reflexivity.
Qed.

(* exec-level register-generic ADDI step (32-bit, F_Base): one lemma, ANY rd/rs1. *)
Section ForwardAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0).

  Definition sAi : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pci : mstate := set_reg sAi nextPC (add_vec_int pc 4).
  Definition sXi : mstate :=
    set_reg s_pci (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_addi_val rs1 imm s_pci)).
  Definition sTi : mstate := set_reg sXi PC (register_lookup nextPC sXi.(sregs)).
  Definition sFi : mstate :=
    if b then set_reg sTi minstret (add_vec_int (register_lookup minstret sTi.(sregs)) 1)
         else sTi.

  Lemma forward_exec_addi_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFi).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAi.(sregs) = pc).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAi.(sregs) = Machine).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAi.(sregs) = HART_ACTIVE tt).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAi.(sregs))) ('b"1") = true).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAi.(sregs))) ('b"1") = false).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAi.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAi, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAi = Some (None, sAi)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAi _ (exec_currentlyEnabled_S sAi) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAi = Some (F_Base w, sAi)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAi
              = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), sAi))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) s_pci
              = Some (RETIRE_SUCCESS, sXi)).
    { rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pci).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAi
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXi)).
    { exact (exec_hart_active_progress sAi sAi sXi sAi w
               (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXi w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXi, s_pci, sAi; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXi, s_pci, sAi; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardAddiGpr.

Lemma gpr_addi_val_file (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (imm : mword 12) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_addi_val rs1 imm (s_pci s pc b) = add_vec va (sign_extend' 64 imm).
Proof.
  intros H1 Lva.
  rewrite (gpr_addi_val_lookup rs1 imm (s_pci s pc b) H1).
  unfold s_pci, sAi. unfold set_reg; cbn [sregs].
  do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section CleanAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (imm : mword 12) (mst0 : mword 64).
  Definition base_upd_i : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_addi_val rs1 imm (s_pci s pc b))))
      PC (add_vec_int pc 4).
  Definition sFci : mstate :=
    if b then set_reg base_upd_i minstret (add_vec_int mst0 1) else base_upd_i.

  Lemma sFi_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFi s pc b rs1 rd imm = sFci.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXi s pc b rs1 rd imm).(sregs) = add_vec_int pc 4).
    { unfold sXi; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTi s pc b rs1 rd imm = base_upd_i).
    { unfold sTi. rewrite Enpc. unfold sXi, s_pci, sAi; cbv zeta.
      unfold base_upd_i, s_pci, sAi. reflexivity. }
    unfold sFi, sFci. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_i.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_i, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanAddiGpr.

(* ====================================================================== *)
(* The register-GENERIC addi WP: ONE lemma for `addi rd,rs1,imm`, ANY      *)
(* rd/rs1, with all GPRs held as the single [gpr_file] resource.           *)
(* ====================================================================== *)
Section WpAddiGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_addi_gpr (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec va (sign_extend' 64 imm))]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hr1 Hrd Hm1 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rs1 imm (s_pci s pc b1) = add_vec va (sign_extend' 64 imm))
      by (apply (gpr_addi_val_file s pc b1 rs1 imm va Hr1 Lrs1)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFci s pc b1 rs1 rd imm mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFi_eq s pc b1 rs1 rd imm mst0 Lpc Lmst).
      apply (forward_exec_addi_gpr s pc b1 w rs1 rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val rs1 imm (s_pci s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec va (sign_extend' 64 imm))) with "Hrdc") as "Hfile".
    unfold sFci, base_upd_i. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpAddiGpr.

(* Demonstration: ONE lemma [wp_addi_gpr] serves many (rd,rs1) pairs. *)
Section WpAddiGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition wp_addi_x5_x6 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_addi_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 6) (mword_of_int 5) imm.   (* addi x5, x6, imm *)
  Definition wp_addi_x28_x1 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_addi_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 1) (mword_of_int 28) imm.  (* addi x28, x1, imm *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 1 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpAddiGprDemo.
