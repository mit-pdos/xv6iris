From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprAddi WpGprLui WpGprShift.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Register-generic RVC (compressed) WPs.  c.li and c.addi both expand    *)
(* via ExecuteAs to ITYPE(.,.,ADDI), so they reuse gpr_addi_val /         *)
(* exec_execute_ITYPE_ADDI_gpr from WpGprAddi, wrapped in the RVC fetch    *)
(* (fetch_from_pts_minstret_RVC2, 2-aligned) + exec_hart_active_progress_  *)
(* RVC (nextPC := pc+2) + exec_riscv_step_gen.                             *)
(* ===================================================================== *)

(* c.li rd,imm  =  ITYPE(sign_ext imm, zreg, rd, ADDI).  zreg = Regidx 0. *)
Definition cli_rs1 : mword 5 := zero_extend' 5 ('b"00").

Lemma exec_execute_C_LI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LI (imm, rd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, zreg, rd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LI. apply exec_returnM. Qed.

(* the value c.li writes to rd (rs1=zreg contributes zero_reg). *)
Definition cli_wval (imm : mword 6) : mword 64 :=
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)).

Lemma gpr_addi_val_cli (imm : mword 6) (t : mstate) :
  gpr_addi_val cli_rs1 (sign_extend' 12 imm) t = cli_wval imm.
Proof.
  unfold gpr_addi_val, cli_wval, cli_rs1.
  replace (Z.eqb (uint (zero_extend' 5 ('b"00"))) 0) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* exec-level forward step for a generic c.li (RVC, 2-byte).               *)
(* ---------------------------------------------------------------------- *)
Section ForwardCliGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (C_LI (imm6, Regidx rd), s0).

  Definition sAl : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcl : mstate := set_reg sAl nextPC (add_vec_int pc 2).
  Definition sXl : mstate :=
    set_reg s_pcl (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_addi_val cli_rs1 (sign_extend' 12 imm6) s_pcl)).
  Definition sTl : mstate := set_reg sXl PC (register_lookup nextPC sXl.(sregs)).
  Definition sFl : mstate :=
    if b then set_reg sTl minstret (add_vec_int (register_lookup minstret sTl.(sregs)) 1)
         else sTl.

  Lemma forward_exec_cli_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFl).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAl.(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAl.(sregs) = zeros' 64).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAl.(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAl = Some (None, sAl)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAl _ (exec_currentlyEnabled_S sAl) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAl = Some (F_RVC w16, sAl)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) sAl = Some (C_LI (imm6, Regidx rd), sAl))
      by (apply Hcdec; exact LmisaA).
    assert (Hexec1 : exec (execute (C_LI (imm6, Regidx rd))) s_pcl
                   = Some (ExecuteAs (ITYPE (sign_extend' 12 imm6, zreg, Regidx rd, ADDI)), s_pcl))
      by apply exec_execute_C_LI.
    assert (Hexec2 : exec (execute (ITYPE (sign_extend' 12 imm6, zreg, Regidx rd, ADDI))) s_pcl
                   = Some (RETIRE_SUCCESS, sXl)).
    { change zreg with (Regidx cli_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr cli_rs1 rd (sign_extend' 12 imm6) s_pcl).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      unfold sXl. reflexivity. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAl = Some (true, sAl))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXl)).
    { exact (exec_hart_active_progress_RVC sAl sXl w16 (C_LI (imm6, Regidx rd))
               (ITYPE (sign_extend' 12 imm6, zreg, Regidx rd, ADDI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen s sXl (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXl, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXl, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCliGpr.

Section CleanCliGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm6 : mword 6) (mst0 : mword 64).
  Definition base_upd_l : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 2))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_addi_val cli_rs1 (sign_extend' 12 imm6) (s_pcl s pc b))))
      PC (add_vec_int pc 2).
  Definition sFcl : mstate :=
    if b then set_reg base_upd_l minstret (add_vec_int mst0 1) else base_upd_l.

  Lemma sFl_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFl s pc b rd imm6 = sFcl.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXl s pc b rd imm6).(sregs) = add_vec_int pc 2).
    { unfold sXl; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTl s pc b rd imm6 = base_upd_l).
    { unfold sTl. rewrite Enpc. unfold sXl, s_pcl, sAl; cbv zeta.
      unfold base_upd_l, s_pcl, sAl. reflexivity. }
    unfold sFl, sFcl. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_l.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_l, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCliGpr.

(* ===================================================================== *)
(* The register-GENERIC c.li WP (2-aligned RVC fetch), gpr_file resource.  *)
(* ===================================================================== *)
Section WpCliGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_cli_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (cli_wval imm6)]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val cli_rs1 (sign_extend' 12 imm6) (s_pcl s pc b1) = cli_wval imm6)
      by apply gpr_addi_val_cli.
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcl s pc b1 rd imm6 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc b1 rd imm6 mst0 Lpc Lmst).
      apply (forward_exec_cli_gpr s pc b1 w16 rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val cli_rs1 (sign_extend' 12 imm6) (s_pcl s pc b1)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (cli_wval imm6)) with "Hrdc") as "Hfile".
    unfold sFcl, base_upd_l. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCliGpr.

(* ===================================================================== *)
(* c.addi rd,imm = ITYPE(sign_ext imm, rd, rd, ADDI): rd += sign_ext imm. *)
(* Reuses exec_execute_C_ADDI (WpEntry) + exec_execute_ITYPE_ADDI_gpr.     *)
(* ===================================================================== *)
Lemma gpr_addi_val_caddi_file (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm6 : mword 6) (va : mword 64) :
  uint rd <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) s.(sregs) = va ->
  gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b) = add_vec va (sign_extend' 64 (sign_extend' 12 imm6)).
Proof.
  intros H1 Lva.
  rewrite (gpr_addi_val_lookup rd (sign_extend' 12 imm6) (s_pcl s pc b) H1).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs].
  do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section ForwardCaddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0).

  Definition sXa : mstate :=
    set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.

  Lemma forward_exec_caddi_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) (sAl s b).(sregs) = zeros' 64).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (C_ADDI (imm6, Regidx rd), (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hexec1 : exec (execute (C_ADDI (imm6, Regidx rd))) (s_pcl s pc b)
                   = Some (ExecuteAs (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI)), (s_pcl s pc b)))
      by apply exec_execute_C_ADDI.
    assert (Hexec2 : exec (execute (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI))) (s_pcl s pc b)
                   = Some (RETIRE_SUCCESS, sXa)).
    { rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm6) (s_pcl s pc b)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      unfold sXa. reflexivity. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXa)).
    { exact (exec_hart_active_progress_RVC (sAl s b) sXa w16 (C_ADDI (imm6, Regidx rd))
               (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen s sXa (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXa, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXa, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCaddiGpr.

Section CleanCaddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm6 : mword 6) (mst0 : mword 64).
  Definition base_upd_a : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 2))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b))))
      PC (add_vec_int pc 2).
  Definition sFca : mstate :=
    if b then set_reg base_upd_a minstret (add_vec_int mst0 1) else base_upd_a.
  Lemma sFa_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFa s pc b rd imm6 = sFca.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXa s pc b rd imm6).(sregs) = add_vec_int pc 2).
    { unfold sXa; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTa s pc b rd imm6 = base_upd_a).
    { unfold sTa. rewrite Enpc. unfold sXa, s_pcl, sAl; cbv zeta.
      unfold base_upd_a, s_pcl, sAl. reflexivity. }
    unfold sFa, sFca. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_a.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_a, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCaddiGpr.

Section WpCaddiGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_caddi_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)
                  = add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))
      by (apply (gpr_addi_val_caddi_file s pc b1 rd imm6 vd Hrd Lrd)).
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFca s pc b1 rd imm6 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFa_eq s pc b1 rd imm6 mst0 Lpc Lmst).
      apply (forward_exec_caddi_gpr s pc b1 w16 rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))) with "Hrdc") as "Hfile".
    unfold sFca, base_upd_a. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddiGpr.

(* ===================================================================== *)
(* GENERIC RVC gpr-write engine: any compressed instr that ExecuteAs-      *)
(* expands to a base instr writing ONE gpr rd (value wval). Reuses         *)
(* s_pcl/sAl from the c.li section. Forward + clean, parameterized.        *)
(* ===================================================================== *)
Section ForwardRvcGprWrite.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (wrd : mword 5) (wval : mword 64).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (cinstr, s0).
  Hypothesis Hcexec1 : exec (execute cinstr) (s_pcl s pc b)
                       = Some (ExecuteAs base, s_pcl s pc b).
  Hypothesis Hcexec2 : exec (execute base) (s_pcl s pc b)
    = Some (RETIRE_SUCCESS,
            set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval)).

  Definition sXg : mstate :=
    set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval).
  Definition sTg : mstate := set_reg sXg PC (register_lookup nextPC sXg.(sregs)).
  Definition sFg : mstate :=
    if b then set_reg sTg minstret (add_vec_int (register_lookup minstret sTg.(sregs)) 1)
         else sTg.

  Lemma forward_exec_rvc_gpr_write :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFg).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) (sAl s b).(sregs) = zeros' 64).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (cinstr, (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXg)).
    { exact (exec_hart_active_progress_RVC (sAl s b) sXg w16 cinstr base pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    apply (exec_riscv_step_gen s sXg (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXg, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXg, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardRvcGprWrite.

Section CleanRvcGprWrite.
  Context (s : mstate) (pc : mword 64) (b : bool) (wrd : mword 5) (wval : mword 64) (mst0 : mword 64).
  Definition base_upd_g : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 2))
         (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval))
      PC (add_vec_int pc 2).
  Definition sFcg : mstate :=
    if b then set_reg base_upd_g minstret (add_vec_int mst0 1) else base_upd_g.
  Lemma sFg_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFg s pc b wrd wval = sFcg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXg s pc b wrd wval).(sregs) = add_vec_int pc 2).
    { unfold sXg; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTg s pc b wrd wval = base_upd_g).
    { unfold sTg. rewrite Enpc. unfold sXg, s_pcl, sAl; cbv zeta.
      unfold base_upd_g, s_pcl, sAl. reflexivity. }
    unfold sFg, sFcg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_g.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_g, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanRvcGprWrite.

(* ===================================================================== *)
(* c.lui rd,imm = LUI rd (UTYPE).  Write-only (no rs read).               *)
(* ===================================================================== *)
Section WpCluiGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_clui_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LUI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (luival (sign_extend' 20 imm6))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hcexec1 : exec (execute (C_LUI (imm6, Regidx rd))) (s_pcl s pc b1)
                    = Some (ExecuteAs (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI)), s_pcl s pc b1))
      by apply exec_execute_C_LUI.
    assert (Hcexec2 : exec (execute (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (luival (sign_extend' 20 imm6))))).
    { change (execute (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI)))
        with (execute_UTYPE (sign_extend' 20 imm6) (Regidx rd) LUI).
      rewrite (exec_execute_UTYPE_LUI_gpr rd (sign_extend' 20 imm6) (s_pcl s pc b1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg s pc b1 rd (luival (sign_extend' 20 imm6)) mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (luival (sign_extend' 20 imm6)) mst0 Lpc Lmst).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_LUI (imm6, Regidx rd))
               (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI)) rd (luival (sign_extend' 20 imm6))
               Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCluiGpr.

(* ===================================================================== *)
(* c.srli rsd',shamt = SRLI (SHIFTIOP).  rsd = creg2reg_idx crsd (x8-x15). *)
(* ===================================================================== *)
Lemma exec_execute_C_SRLI (shamt : mword 6) (crsd : cregidx) s :
  exec (execute (C_SRLI (shamt, crsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SRLI. cbn zeta. apply exec_returnM. Qed.

Definition csrli_wval (shamt : mword 6) (vsd : mword 64) : mword 64 :=
  shift_bits_right vsd (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma gpr_srli_val_file (s : mstate) (pc : mword 64) (b : bool) (rsd : mword 5) (shamt : mword 6) (vsd : mword 64) :
  uint rsd <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rsd))) s.(sregs) = vsd ->
  gpr_srli_val rsd shamt (s_pcl s pc b) = csrli_wval shamt vsd.
Proof.
  intros H1 Lva. unfold gpr_srli_val, gpr_src, csrli_wval.
  replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section WpCsrliGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_csrli_gpr (pc : mword 64) (w16 : mword 16) (shamt : mword 6) (crsd : cregidx) (rsd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsd misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    creg2reg_idx crsd = Regidx rsd ->
    uint rsd <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vsd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_SRLI (shamt, crsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (csrli_wval shamt vsd)]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hcrsd Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_srli_val rsd shamt (s_pcl s pc b1) = csrli_wval shamt vsd)
      by (apply (gpr_srli_val_file s pc b1 rsd shamt vsd Hrd Lrd)).
    assert (Hcexec1 : exec (execute (C_SRLI (shamt, crsd))) (s_pcl s pc b1)
                    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)), s_pcl s pc b1))
      by apply exec_execute_C_SRLI.
    assert (Hcexec2 : exec (execute (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_srli_val rsd shamt (s_pcl s pc b1))))).
    { rewrite Hcrsd. rewrite (exec_execute_SHIFTIOP_SRLI_gpr rsd rsd shamt (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) mst0 Lpc Lmst).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_SRLI (shamt, crsd))
               (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)) rsd
               (gpr_srli_val rsd shamt (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_srli_val rsd shamt (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (csrli_wval shamt vsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrliGpr.

(* ===================================================================== *)
(* c.mv rd,rs2 = ADD rd,x0,rs2 (RTYPE).  rd := rs2.  Reads rs2, writes rd. *)
(* ===================================================================== *)
Lemma exec_execute_C_MV (rd rs2 : regidx) s :
  exec (execute (C_MV (rd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_MV. apply exec_returnM. Qed.

Definition cmv_wval (vs2 : mword 64) : mword 64 := add_vec zero_reg vs2.

Lemma gpr_mv_val_file (s : mstate) (pc : mword 64) (b : bool) (rs2 : mword 5) (vs2 : mword 64) :
  uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vs2 ->
  gpr_rd_val rs2 cli_rs1 (s_pcl s pc b) = cmv_wval vs2.
Proof.
  intros H1 Lva. unfold gpr_rd_val, cmv_wval, cli_rs1.
  replace (Z.eqb (uint (zero_extend' 5 ('b"00"))) 0) with true by (vm_compute; reflexivity).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section WpCmvGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_cmv_gpr (pc : mword 64) (w16 : mword 16) (rd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd vs2 misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rs2) = Some vs2 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_MV (Regidx rd, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (cmv_wval vs2)]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hrs2 Hms2 Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfile") as "[Hrs2c Hfb]".
    iDestruct (reg_valid with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1) = cmv_wval vs2)
      by (apply (gpr_mv_val_file s pc b1 rs2 vs2 Hrs2 Lrs2)).
    assert (Hcexec1 : exec (execute (C_MV (Regidx rd, Regidx rs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)), s_pcl s pc b1))
      by apply exec_execute_C_MV.
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1))))).
    { change zreg with (Regidx cli_rs1).
      change (execute (RTYPE (Regidx rs2, Regidx cli_rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx cli_rs1) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 cli_rs1 rd (s_pcl s pc b1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg s pc b1 rd (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) mst0 Lpc Lmst).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_MV (Regidx rd, Regidx rs2))
               (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) rd
               (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (cmv_wval vs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCmvGpr.

(* ===================================================================== *)
(* c.addi16sp / c.addi4spn = ITYPE ADDI on sp (=x2).                       *)
(* ===================================================================== *)
Definition csp_rs1 : mword 5 := zero_extend' 5 ('b"10").
Definition caddi16sp_imm (imm : mword 6) : mword 12 := sign_extend' 12 (concat_vec imm (Ox"0")).
Definition caddi4spn_imm (nzimm : mword 8) : mword 12 := concat_vec ('b"00") (concat_vec nzimm ('b"00")).

Lemma gpr_addi_val_file_l (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (imm12 : mword 12) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_addi_val rs1 imm12 (s_pcl s pc b) = add_vec va (sign_extend' 64 imm12).
Proof.
  intros H1 Lva. rewrite (gpr_addi_val_lookup rs1 imm12 (s_pcl s pc b) H1).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Lemma exec_execute_C_ADDI16SP (imm : mword 6) s :
  exec (execute (C_ADDI16SP imm)) s
    = Some (ExecuteAs (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI16SP, caddi16sp_imm. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI4SPN (rdc : cregidx) (nzimm : mword 8) s :
  exec (execute (C_ADDI4SPN (rdc, nzimm))) s
    = Some (ExecuteAs (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx rdc, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI4SPN, caddi4spn_imm. cbn zeta. apply exec_returnM. Qed.

Section WpCaddi16spGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_caddi16sp_gpr (pc : mword 64) (w16 : mword 16) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vsp misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI16SP imm6, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint csp_rs1) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hmsp Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb]".
    iDestruct (reg_valid with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb" with "Hspc") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)
                  = add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))
      by (apply (gpr_addi_val_file_l s pc b1 csp_rs1 (caddi16sp_imm imm6) vsp ltac:(vm_compute; discriminate) Lsp)).
    assert (Hcexec1 : exec (execute (C_ADDI16SP imm6)) (s_pcl s pc b1)
                    = Some (ExecuteAs (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)), s_pcl s pc b1))
      by apply exec_execute_C_ADDI16SP.
    assert (Hcexec2 : exec (execute (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint csp_rs1)))
                (regval_into_reg (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1))))).
    { change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)).
      replace (Z.eqb (uint csp_rs1) 0) with false by (vm_compute; reflexivity). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) mst0 Lpc Lmst).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADDI16SP imm6)
               (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) csp_rs1
               (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc2 Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) _
            (regval_into_reg (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1))) with "Hreg Hspc2") as "[Hreg Hspc2]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hspc2".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))) with "Hspc2") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddi16spGpr.

Section WpCaddi4spnGpr.
  Context `{!riscvGS Σ}.
  Lemma wp_caddi4spn_gpr (pc : mword 64) (w16 : mword 16) (nzimm : mword 8) (crdc : cregidx) (rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsp vd misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    creg2reg_idx crdc = Regidx rd ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI4SPN (crdc, nzimm), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hcrdc Hrd Hmsp Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
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
    iDestruct (reg_valid with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb]".
    iDestruct (reg_valid with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb" with "Hspc") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)
                  = add_vec vsp (sign_extend' 64 (caddi4spn_imm nzimm)))
      by (apply (gpr_addi_val_file_l s pc b1 csp_rs1 (caddi4spn_imm nzimm) vsp ltac:(vm_compute; discriminate) Lsp)).
    assert (Hcexec1 : exec (execute (C_ADDI4SPN (crdc, nzimm))) (s_pcl s pc b1)
                    = Some (ExecuteAs (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx crdc, ADDI)), s_pcl s pc b1))
      by apply exec_execute_C_ADDI4SPN.
    assert (Hcexec2 : exec (execute (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx crdc, ADDI))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1))))).
    { change sp with (Regidx csp_rs1). rewrite Hcrdc.
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) (s_pcl s pc b1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg s pc b1 rd (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) mst0 Lpc Lmst).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADDI4SPN (crdc, nzimm))
               (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx crdc, ADDI)) rd
               (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vsp (sign_extend' 64 (caddi4spn_imm nzimm)))) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddi4spnGpr.
