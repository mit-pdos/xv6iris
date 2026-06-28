From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprAddi WpGprLui WpGprShift WpGprLogic WpGprLoad WpGprJalr WpGprStore.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
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
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFl).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAl.(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAl.(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAl = Some (None, sAl)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAl _ (exec_currentlyEnabled_S sAl) LSA LmIEA). }
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
  Context {dqc : dfrac}.
  Lemma wp_cli_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (cli_wval imm6)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val cli_rs1 (sign_extend' 12 imm6) (s_pcl s pc b1) = cli_wval imm6)
      by apply gpr_addi_val_cli.
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcl s pc b1 rd imm6 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc b1 rd imm6 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_cli_gpr s pc b1 w16 rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
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
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
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
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LSA LmIEA). }
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
  Context {dqc : dfrac}.
  Lemma wp_caddi_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)
                  = add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))
      by (apply (gpr_addi_val_caddi_file s pc b1 rd imm6 vd Hrd Lrd)).
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFca s pc b1 rd imm6 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFa_eq s pc b1 rd imm6 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_caddi_gpr s pc b1 w16 rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
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
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
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
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFg).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LSA LmIEA). }
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
  Context {dqc : dfrac}.
  Lemma wp_clui_gpr (pc : mword 64) (w16 : mword 16) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LUI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (luival (sign_extend' 20 imm6))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
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
    iModIntro.
    iExists (sFcg s pc b1 rd (luival (sign_extend' 20 imm6)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (luival (sign_extend' 20 imm6)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_LUI (imm6, Regidx rd))
               (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI)) rd (luival (sign_extend' 20 imm6))
               Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
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
  Context {dqc : dfrac}.
  Lemma wp_csrli_gpr (pc : mword 64) (w16 : mword 16) (shamt : mword 6) (crsd : cregidx) (rsd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_SRLI (shamt, crsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (csrli_wval shamt vsd)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrsd Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
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
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_SRLI (shamt, crsd))
               (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)) rsd
               (gpr_srli_val rsd shamt (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_srli_val rsd shamt (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (csrli_wval shamt vsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
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
  Context {dqc : dfrac}.
  Lemma wp_cmv_gpr (pc : mword 64) (w16 : mword 16) (rd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd vs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_MV (Regidx rd, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (cmv_wval vs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hrs2 Hms2 Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfile") as "[Hrs2c Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
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
    iModIntro.
    iExists (sFcg s pc b1 rd (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_MV (Regidx rd, Regidx rs2))
               (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) rd
               (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_rd_val rs2 cli_rs1 (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (cmv_wval vs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
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
  Context {dqc : dfrac}.
  Lemma wp_caddi16sp_gpr (pc : mword 64) (w16 : mword 16) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vsp misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI16SP imm6, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint csp_rs1) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hmsp Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hspc") as %Lsp.
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
    iModIntro.
    iExists (sFcg s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADDI16SP imm6)
               (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) csp_rs1
               (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc2 Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) _
            (regval_into_reg (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1))) with "Hreg Hspc2") as "[Hreg Hspc2]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hspc2".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))) with "Hspc2") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddi16spGpr.

Section WpCaddi4spnGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_caddi4spn_gpr (pc : mword 64) (w16 : mword 16) (nzimm : mword 8) (crdc : cregidx) (rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsp vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDI4SPN (crdc, nzimm), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrdc Hrd Hmsp Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hspc") as %Lsp.
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
    iModIntro.
    iExists (sFcg s pc b1 rd (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADDI4SPN (crdc, nzimm))
               (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx crdc, ADDI)) rd
               (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_addi_val csp_rs1 (caddi4spn_imm nzimm) (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vsp (sign_extend' 64 (caddi4spn_imm nzimm)))) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddi4spnGpr.

(* ===================================================================== *)
(* c.slli rsd,shamt = SLLI (SHIFTIOP). rsd is a FULL regidx (not creg).    *)
(* ===================================================================== *)
Lemma exec_execute_C_SLLI (shamt : mword 6) (rsd : regidx) s :
  exec (execute (C_SLLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SLLI. apply exec_returnM. Qed.

Definition cslli_wval (shamt : mword 6) (vsd : mword 64) : mword 64 :=
  shift_bits_left vsd (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma gpr_slli_val_file (s : mstate) (pc : mword 64) (b : bool) (rsd : mword 5) (shamt : mword 6) (vsd : mword 64) :
  uint rsd <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rsd))) s.(sregs) = vsd ->
  gpr_slli_val rsd shamt (s_pcl s pc b) = cslli_wval shamt vsd.
Proof.
  intros H1 Lva. unfold gpr_slli_val, gpr_src, cslli_wval.
  replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section WpCslliGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cslli_gpr (pc : mword 64) (w16 : mword 16) (shamt : mword 6) (rsd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
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
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_SLLI (shamt, Regidx rsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (cslli_wval shamt vsd)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_slli_val rsd shamt (s_pcl s pc b1) = cslli_wval shamt vsd)
      by (apply (gpr_slli_val_file s pc b1 rsd shamt vsd Hrd Lrd)).
    assert (Hcexec1 : exec (execute (C_SLLI (shamt, Regidx rsd))) (s_pcl s pc b1)
                    = Some (ExecuteAs (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI)), s_pcl s pc b1))
      by apply exec_execute_C_SLLI.
    assert (Hcexec2 : exec (execute (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_slli_val rsd shamt (s_pcl s pc b1))))).
    { rewrite (exec_execute_SHIFTIOP_SLLI_gpr rsd rsd shamt (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_slli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_slli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_SLLI (shamt, Regidx rsd))
               (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI)) rsd
               (gpr_slli_val rsd shamt (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_slli_val rsd shamt (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (cslli_wval shamt vsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCslliGpr.

(* ===================================================================== *)
(* c.add rsd,rs2 = RTYPE ADD (rd:=rsd+rs2). Reads rsd+rs2, writes rsd.     *)
(* ===================================================================== *)
Lemma gpr_rd_val_file_l (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_rd_val rs2 rs1 (s_pcl s pc b) = add_vec va vb.
Proof.
  intros H1 H2 Lva Lvb. unfold gpr_rd_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 4 gpr_trans. rewrite Lva. rewrite Lvb. reflexivity.
Qed.

Section WpCaddGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cadd_gpr (pc : mword 64) (w16 : mword 16) (rsd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rsd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADD (Regidx rsd, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (add_vec vrsd vrs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hrs2 Hmrd Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hrs2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_rd_val rs2 rsd (s_pcl s pc b1) = add_vec vrsd vrs2)
      by (apply (gpr_rd_val_file_l s pc b1 rs2 rsd vrsd vrs2 Hrd Hrs2 Lrd Lrs2)).
    assert (Hcexec1 : exec (execute (C_ADD (Regidx rsd, Regidx rs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)), s_pcl s pc b1))
      by apply exec_execute_C_ADD.
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_rd_val rs2 rsd (s_pcl s pc b1))))).
    { change (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rsd) (Regidx rsd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rsd rsd (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_rd_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_rd_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADD (Regidx rsd, Regidx rs2))
               (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)) rsd
               (gpr_rd_val rs2 rsd (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_rd_val rs2 rsd (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vrsd vrs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddGpr.

(* ===================================================================== *)
(* c.or crsd,crs2 = RTYPE OR (rsd:=rsd|rs2). cregidx operands.            *)
(* ===================================================================== *)
Lemma exec_execute_C_OR (rsd rs2 : cregidx) s :
  exec (execute (C_OR (rsd, rs2))) s
  = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, OR)), s).
Proof. unfold execute. cbn match. unfold execute_C_OR. apply exec_returnM. Qed.

Lemma gpr_or_val_file_l (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_or_val rs2 rs1 (s_pcl s pc b) = or_vec va vb.
Proof.
  intros H1 H2 Lva Lvb. rewrite (gpr_or_val_lookup rs2 rs1 (s_pcl s pc b) H1 H2).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 4 gpr_trans. rewrite Lva. rewrite Lvb. reflexivity.
Qed.

Section WpCorGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cor_gpr (pc : mword 64) (w16 : mword 16) (crsd crs2 : cregidx) (rsd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    creg2reg_idx crsd = Regidx rsd -> creg2reg_idx crs2 = Regidx rs2 ->
    uint rsd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_OR (crsd, crs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (or_vec vrsd vrs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrsd Hcrs2 Hrd Hrs2 Hmrd Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hrs2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_or_val rs2 rsd (s_pcl s pc b1) = or_vec vrsd vrs2)
      by (apply (gpr_or_val_file_l s pc b1 rs2 rsd vrsd vrs2 Hrd Hrs2 Lrd Lrs2)).
    assert (Hcexec1 : exec (execute (C_OR (crsd, crs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)), s_pcl s pc b1)).
    { rewrite exec_execute_C_OR. rewrite Hcrsd. rewrite Hcrs2. reflexivity. }
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_or_val rs2 rsd (s_pcl s pc b1))))).
    { change (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)))
        with (execute_RTYPE (Regidx rs2) (Regidx rsd) (Regidx rsd) OR).
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rsd rsd (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_or_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_or_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_OR (crsd, crs2))
               (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)) rsd
               (gpr_or_val rs2 rsd (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_or_val rs2 rsd (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec vrsd vrs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCorGpr.

(* ===================================================================== *)
(* c.ld rdc,uimm(rsc) = LOAD 8 (rd := mem[rs1+imm]).  cregidx operands.   *)
(* ===================================================================== *)
Lemma exec_execute_C_LD (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LD (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LD. cbn zeta. apply exec_returnM. Qed.

Section WpCldGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cld_gpr (pc : mword 64) (w16 : mword 16) (uimm : mword 5) (crsc crdc : cregidx)
      (rs1 rd : mword 5) (m : gmap register_bitvector_64 (mword 64))
      (vrs1 vd misa0 mdv0 : mword 64) (b1 : bool) (v : bv 64)
      (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let imm_l := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vrs1 offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    creg2reg_idx crsc = Regidx rs1 -> creg2reg_idx crdc = Regidx rd ->
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LD (uimm, crsc, crdc), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN imm_l offset ea a8 pa data2 Hcrsc Hcrdc Hrs1 Hrd Hmrs1 Hmrd Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HisRVC Hmisa HS Hdl Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & Hread & _).
    iIntros "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (sP := s_pcl s pc b1).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) sP.(sregs) = vrs1).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lrs1. }
    assert (Lprivp : register_lookup cur_privilege sP.(sregs) = Machine).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus sP.(sregs) = mstatus0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg sP.(sregs) = mseccfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n sP.(sregs) = pmpcfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions sP.(sregs) = pmar0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base sP.(sregs) = None).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 sP (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 sP (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 sP Lhtifp) as Hwh.
    assert (Hcexec2 :
      exec (execute (LOAD (imm_l, Regidx rs1, Regidx rd, false, 8))) sP
      = Some (RETIRE_SUCCESS, set_reg sP (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8_gpr rs1 rd imm_l v region sP Hrs1 Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hpmm.
      - rewrite Lrs1p. exact Halign.
      - intro j. rewrite Lpmpcp. exact (Hpmpf j).
      - rewrite Lpmap Lrs1p. exact Hmatch.
      - rewrite Lrs1p. exact Hpalign.
      - exact Hread.
      - rewrite Lrs1p. apply Hwc.
      - rewrite Lrs1p. apply Hws.
      - rewrite Lrs1p. apply Hwh.
      - intros j Hj. rewrite Lrs1p. exact (Hbytesf j Hj). }
    assert (Hcexec1 : exec (execute (C_LD (uimm, crsc, crdc))) sP
       = Some (ExecuteAs (LOAD (imm_l, Regidx rs1, Regidx rd, false, 8)), sP)).
    { rewrite exec_execute_C_LD. rewrite Hcrsc. rewrite Hcrdc. reflexivity. }
    iModIntro.
    iExists (sFcg s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_LD (uimm, crsc, crdc))
               (LOAD (imm_l, Regidx rs1, Regidx rd, false, 8)) rd
               (extend_value false data2) Hfetch_at Hsi_s Hdl Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpCldGpr.


(* ===================================================================== *)
(* c.ret = c.jr ra = JALR (0, ra, x0). Control flow: PC := ra. No GPR wr. *)
(* ===================================================================== *)
Lemma exec_execute_C_JR (rs1 : regidx) s :
  exec (execute (C_JR rs1)) s = Some (ExecuteAs (JALR (zeros' 12, rs1, zreg)), s).
Proof. unfold execute. cbn match. unfold execute_C_JR. apply exec_returnM. Qed.

Section ForwardCretJalr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16) (ra : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hra0 : uint ra <> 0.
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (C_JR (Regidx ra), s0).
  Hypothesis Hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs))) = false.

  Definition cret_tgt : mword 64 :=
    update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) (s_pcl s pc b).(sregs))
                            (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0").
  Definition sXcr : mstate := set_reg (s_pcl s pc b) nextPC cret_tgt.
  Definition sTcr : mstate := set_reg sXcr PC (register_lookup nextPC sXcr.(sregs)).
  Definition sFcr : mstate :=
    if b then set_reg sTcr minstret (add_vec_int (register_lookup minstret sTcr.(sregs)) 1) else sTcr.

  Lemma forward_exec_cret :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (access_vec_dec cret_tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec cret_tgt 1) = false ->
    exec riscv_step s = Some (tt, sFcr).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Lmisa Halign Hbit1.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (C_JR (Regidx ra), (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) (s_pcl s pc b) = Some (false, s_pcl s pc b)).
    { apply exec_cE_zicfilp_false.
      - unfold s_pcl, sAl, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity].
      - unfold s_pcl, sAl, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Hmlpe | vm_compute; reflexivity]. }
    assert (Hcexec1 : exec (execute (C_JR (Regidx ra))) (s_pcl s pc b)
              = Some (ExecuteAs (JALR (zeros' 12, Regidx ra, Regidx cli_rs1)), s_pcl s pc b)).
    { rewrite exec_execute_C_JR. change zreg with (Regidx cli_rs1). reflexivity. }
    assert (Hcexec2 : exec (execute (JALR (zeros' 12, Regidx ra, Regidx cli_rs1))) (s_pcl s pc b)
              = Some (RETIRE_SUCCESS, sXcr)).
    { change (execute (JALR (zeros' 12, Regidx ra, Regidx cli_rs1)))
        with (execute_JALR (zeros' 12) (Regidx ra) (Regidx cli_rs1)).
      rewrite (exec_execute_JALR_ret (zeros' 12) ra cli_rs1 (s_pcl s pc b) Hra0
                 ltac:(vm_compute; reflexivity) Hzic Halign Hbit1).
      unfold sXcr, cret_tgt. reflexivity. }
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXcr)).
    { exact (exec_hart_active_progress_RVC (sAl s b) sXcr w16 (C_JR (Regidx ra))
               (JALR (zeros' 12, Regidx ra, Regidx cli_rs1)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    apply (exec_riscv_step_gen s sXcr (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcr, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcr, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCretJalr.

Section CleanCret.
  Context (s : mstate) (pc : mword 64) (b : bool) (ra : mword 5) (mst0 : mword 64).
  Definition sFccr : mstate :=
    if b then set_reg (sTcr s pc b ra) minstret (add_vec_int mst0 1) else sTcr s pc b ra.
  Lemma sFcr_eq :
    register_lookup minstret s.(sregs) = mst0 -> sFcr s pc b ra = sFccr.
  Proof.
    intro LmstS. unfold sFcr, sFccr. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret (sTcr s pc true ra).(sregs) = register_lookup minstret s.(sregs)).
    { unfold sTcr, sXcr, s_pcl, sAl, set_reg; cbn [sregs]. tmig. tmig. tmig. tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCret.

Lemma cret_tgt_eq (s : mstate) (pc : mword 64) (b : bool) (ra : mword 5) (vra : mword 64) :
  register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) (s_pcl s pc b).(sregs) = vra ->
  cret_tgt s pc b ra = update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0").
Proof. intro L. unfold cret_tgt. rewrite L. reflexivity. Qed.

Section WpCretGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cret (pc : mword 64) (w16 : mword 16) (ra : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vra misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 mseccfg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let tgt := update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0") in
    uint ra <> 0 ->
    m !! gpr_of_Z (uint ra) = Some vra ->
    bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_JR (Regidx ra), s0)) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto mseccfg dqc mseccfg0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ tgt -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ tgt -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto mseccfg dqc mseccfg0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN tgt Hra Hmra Hmlpe Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hal0 Hal1 Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmra with "Hfile") as "[Hrac Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrac") as %Lra.
    iDestruct ("Hfb" with "Hrac") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmlpe_s : bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs))) = false)
      by (rewrite Lsec; exact Hmlpe).
    assert (Lrap : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) (s_pcl s pc b1).(sregs) = vra).
    { unfold s_pcl, sAl. gpr_trans. trans_mi. exact Lra. }
    assert (Htgt : cret_tgt s pc b1 ra = tgt) by (apply cret_tgt_eq; exact Lrap).
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFccr s pc b1 ra (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFcr_eq s pc b1 ra (register_lookup minstret s.(sregs)) eq_refl).
      apply (forward_exec_cret s pc b1 w16 ra Hfetch_at Hsi_s Hra Hdec Hmlpe_s Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa.
      - rewrite Htgt. exact Hal0.
      - rewrite Htgt. exact Hal1. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (cret_tgt s pc b1 ra) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (cret_tgt s pc b1 ra) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Htgt) in "Hpc". iEval (rewrite Htgt) in "Hnpc".
    unfold sFccr, sTcr, sXcr. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold s_pcl, sAl, set_reg; cbn [sregs mem]. rewrite register_lookup_set. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro.
      unfold s_pcl, sAl, set_reg; cbn [sregs mem]. rewrite register_lookup_set. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCretGpr.

(* ===================================================================== *)
(* Generic RVC step with arbitrary post-execute state sX (memory or other  *)
(* non-PC effects). nextPC stays pc+2 (sequential). Reusable for stores.   *)
(* ===================================================================== *)
Section ForwardRvcStep.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (sX : mstate) (mst0 : mword 64).
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
                       = Some (RETIRE_SUCCESS, sX).
  Hypothesis HhartX : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt.
  Hypothesis HmiX : register_lookup (R_bool minstret_increment) sX.(sregs) = b.
  Hypothesis Hnpc_sX : register_lookup nextPC sX.(sregs) = add_vec_int pc 2.
  Hypothesis Hmst_sX : register_lookup minstret sX.(sregs) = mst0.

  Lemma forward_exec_rvc_step :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s
    = Some (tt, if b then set_reg (set_reg sX PC (add_vec_int pc 2)) minstret (add_vec_int mst0 1)
                     else set_reg sX PC (add_vec_int pc 2)).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAl s b).(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAl s b) = Some (None, (sAl s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAl s b) _ (exec_currentlyEnabled_S (sAl s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (cinstr, (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sX)).
    { exact (exec_hart_active_progress_RVC (sAl s b) sX w16 cinstr base pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    rewrite (exec_riscv_step_gen s sX (zero_extend' 32 w16) b Lpriv Hsi_s LhsA Hha HhartX HmiX
               ltac:(reflexivity)).
    f_equal. f_equal. rewrite Hnpc_sX. destruct b; [|reflexivity].
    f_equal. f_equal. tmig. exact Hmst_sX.
  Qed.
End ForwardRvcStep.

(* ===================================================================== *)
(* c.sdsp rs2,uimm(sp) = STORE 8 (mem[sp+imm] := rs2). rs1=sp.            *)
(* ===================================================================== *)
Lemma exec_execute_C_SDSP (uimm : mword 6) (rs2 : regidx) s :
  exec (execute (C_SDSP (uimm, rs2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), rs2, sp, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SDSP. cbn zeta. apply exec_returnM. Qed.

Section WpCsdspGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csdsp (pc : mword 64) (w16 : mword 16) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsp vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (vold : bv 64) (npc0 mstatus0 mseccfg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let imm_l := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vsp offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    uint rs2 <> 0 ->
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_SDSP (uimm, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN imm_l offset ea a8 pa Hrs2 Hmsp Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HisRVC Hmisa HS Hds Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & _ & Hwrite).
    iIntros "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (sP := s_pcl s pc b1).
    assert (Lspp : register_lookup (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) sP.(sregs) = vsp).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lsp. }
    assert (Lrs2p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) sP.(sregs) = vrs2).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lrs2. }
    assert (Lprivp : register_lookup cur_privilege sP.(sregs) = Machine).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus sP.(sregs) = mstatus0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg sP.(sregs) = mseccfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n sP.(sregs) = pmpcfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions sP.(sregs) = pmar0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base sP.(sregs) = None).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 sP (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 sP (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 sP Lhtifp) as Hwh.
    pose (sX := MState sP.(sregs) (write_bytes sP.(mem) pa 8 vrs2)).
    assert (Hcexec2 :
      exec (execute (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8))) sP
      = Some (RETIRE_SUCCESS, sX)).
    { rewrite (exec_execute_STORE_8_gpr rs2 csp_rs1 imm_l region sP
                ltac:(vm_compute; discriminate) Hrs2 Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hpmm)
                ltac:(rewrite Lspp; exact Halign) ltac:(intro j; rewrite Lpmpcp; exact (Hpmpf j))
                ltac:(rewrite Lpmap Lspp; exact Hmatch) ltac:(rewrite Lspp; exact Hpalign)
                Hwrite ltac:(rewrite Lspp; apply Hwc) ltac:(rewrite Lspp; apply Hws)
                ltac:(rewrite Lspp; apply Hwh)).
      subst sX. do 3 f_equal. rewrite Lspp Lrs2p. reflexivity. }
    assert (Hcexec1 : exec (execute (C_SDSP (uimm, Regidx rs2))) sP
       = Some (ExecuteAs (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8)), sP)).
    { rewrite exec_execute_C_SDSP. change sp with (Regidx csp_rs1). reflexivity. }
    assert (HhartX : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhs. }
    assert (HmiX : register_lookup (R_bool minstret_increment) sX.(sregs) = b1).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; rewrite register_lookup_set; reflexivity. }
    assert (Hnpc_sX : register_lookup nextPC sX.(sregs) = add_vec_int pc 2).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; rewrite register_lookup_set; reflexivity. }
    assert (Hmst_sX : register_lookup minstret sX.(sregs) = (register_lookup minstret s.(sregs))).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; trans_mi; reflexivity. }
    iModIntro.
    iExists (if b1 then set_reg (set_reg sX PC (add_vec_int pc 2)) minstret (add_vec_int (register_lookup minstret s.(sregs)) 1)
                   else set_reg sX PC (add_vec_int pc 2)). iSplitR.
    { iPureIntro.
      apply (forward_exec_rvc_step s pc b1 w16 (C_SDSP (uimm, Regidx rs2))
               (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8)) sX (register_lookup minstret s.(sregs))
               Hfetch_at Hsi_s Hds Hcexec1 Hcexec2 HhartX HmiX Hnpc_sX Hmst_sX Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold sX, sP, s_pcl, sAl, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro.
      unfold sX, sP, s_pcl, sAl, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpCsdspGpr.

(* ===================================================================== *)
(* 4-ALIGNED RVC variants (RVC4 fetch: 32-bit word, low half is the instr) *)
(* ===================================================================== *)
Section WpCliGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cli_gpr_4 (pc : mword 64) (w : mword 32) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_LI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (cli_wval imm6)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val cli_rs1 (sign_extend' 12 imm6) (s_pcl s pc b1) = cli_wval imm6)
      by apply gpr_addi_val_cli.
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcl s pc b1 rd imm6 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc b1 rd imm6 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_cli_gpr s pc b1 (subrange_vec_dec w 15 0) rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
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
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCliGpr4.
Section WpCaddiGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_caddi_gpr_4 (pc : mword 64) (w : mword 32) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_ADDI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
                     regval_into_reg (add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addi_val rd (sign_extend' 12 imm6) (s_pcl s pc b1)
                  = add_vec vd (sign_extend' 64 (sign_extend' 12 imm6)))
      by (apply (gpr_addi_val_caddi_file s pc b1 rd imm6 vd Hrd Lrd)).
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFca s pc b1 rd imm6 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFa_eq s pc b1 rd imm6 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_caddi_gpr s pc b1 (subrange_vec_dec w 15 0) rd imm6 Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
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
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddiGpr4.
Section WpCluiGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_clui_gpr_4 (pc : mword 64) (w : mword 32) (rd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_LUI (imm6, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (luival (sign_extend' 20 imm6))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
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
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rd (luival (sign_extend' 20 imm6)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (luival (sign_extend' 20 imm6)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_LUI (imm6, Regidx rd))
               (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI)) rd (luival (sign_extend' 20 imm6))
               Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival (sign_extend' 20 imm6))) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCluiGpr4.
Section WpCaddGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cadd_gpr_4 (pc : mword 64) (w : mword 32) (rsd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rsd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_ADD (Regidx rsd, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (add_vec vrsd vrs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hrs2 Hmrd Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hrs2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_rd_val rs2 rsd (s_pcl s pc b1) = add_vec vrsd vrs2)
      by (apply (gpr_rd_val_file_l s pc b1 rs2 rsd vrsd vrs2 Hrd Hrs2 Lrd Lrs2)).
    assert (Hcexec1 : exec (execute (C_ADD (Regidx rsd, Regidx rs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)), s_pcl s pc b1))
      by apply exec_execute_C_ADD.
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_rd_val rs2 rsd (s_pcl s pc b1))))).
    { change (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rsd) (Regidx rsd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rsd rsd (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_rd_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_rd_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_ADD (Regidx rsd, Regidx rs2))
               (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD)) rsd
               (gpr_rd_val rs2 rsd (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_rd_val rs2 rsd (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vrsd vrs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddGpr4.

(* ===================================================================== *)
(* ROUND 2: more 4-aligned RVC variants (csrli/caddi16sp/cor/csdsp)        *)
(* ===================================================================== *)
Section WpCsrliGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrli_gpr_4 (pc : mword 64) (w : mword 32) (shamt : mword 6) (crsd : cregidx) (rsd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    creg2reg_idx crsd = Regidx rsd ->
    uint rsd <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vsd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_SRLI (shamt, crsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (csrli_wval shamt vsd)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrsd Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
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
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_srli_val rsd shamt (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_SRLI (shamt, crsd))
               (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)) rsd
               (gpr_srli_val rsd shamt (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_srli_val rsd shamt (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (csrli_wval shamt vsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrliGpr4.
Section WpCaddi16spGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_caddi16sp_gpr_4 (pc : mword 64) (w : mword 32) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vsp misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_ADDI16SP imm6, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint csp_rs1) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hmsp Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb]".
    iDestruct (reg_valid_dq with "Hreg Hspc") as %Lsp.
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
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 csp_rs1 (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_ADDI16SP imm6)
               (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) csp_rs1
               (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc2 Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) _
            (regval_into_reg (gpr_addi_val csp_rs1 (caddi16sp_imm imm6) (s_pcl s pc b1))) with "Hreg Hspc2") as "[Hreg Hspc2]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hspc2".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))) with "Hspc2") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddi16spGpr4.
Section WpCorGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cor_gpr_4 (pc : mword 64) (w : mword 32) (crsd crs2 : cregidx) (rsd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    creg2reg_idx crsd = Regidx rsd -> creg2reg_idx crs2 = Regidx rs2 ->
    uint rsd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_OR (crsd, crs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (or_vec vrsd vrs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrsd Hcrs2 Hrd Hrs2 Hmrd Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hrs2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_or_val rs2 rsd (s_pcl s pc b1) = or_vec vrsd vrs2)
      by (apply (gpr_or_val_file_l s pc b1 rs2 rsd vrsd vrs2 Hrd Hrs2 Lrd Lrs2)).
    assert (Hcexec1 : exec (execute (C_OR (crsd, crs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)), s_pcl s pc b1)).
    { rewrite exec_execute_C_OR. rewrite Hcrsd. rewrite Hcrs2. reflexivity. }
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_or_val rs2 rsd (s_pcl s pc b1))))).
    { change (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)))
        with (execute_RTYPE (Regidx rs2) (Regidx rsd) (Regidx rsd) OR).
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rsd rsd (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_or_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_or_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_OR (crsd, crs2))
               (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR)) rsd
               (gpr_or_val rs2 rsd (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_or_val rs2 rsd (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec vrsd vrs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCorGpr4.
Section WpCsdspGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csdsp_4 (pc : mword 64) (w : mword 32) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vsp vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (vold : bv 64) (npc0 mstatus0 mseccfg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let imm_l := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vsp offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    uint rs2 <> 0 ->
    m !! gpr_of_Z (uint csp_rs1) = Some vsp ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_SDSP (uimm, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN imm_l offset ea a8 pa Hrs2 Hmsp Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HisRVC Hmisa HS Hds Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & _ & Hwrite).
    iIntros "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfile") as "[Hspc Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (sP := s_pcl s pc b1).
    assert (Lspp : register_lookup (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) sP.(sregs) = vsp).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lsp. }
    assert (Lrs2p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) sP.(sregs) = vrs2).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lrs2. }
    assert (Lprivp : register_lookup cur_privilege sP.(sregs) = Machine).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus sP.(sregs) = mstatus0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg sP.(sregs) = mseccfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n sP.(sregs) = pmpcfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions sP.(sregs) = pmar0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base sP.(sregs) = None).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 sP (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 sP (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 sP Lhtifp) as Hwh.
    pose (sX := MState sP.(sregs) (write_bytes sP.(mem) pa 8 vrs2)).
    assert (Hcexec2 :
      exec (execute (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8))) sP
      = Some (RETIRE_SUCCESS, sX)).
    { rewrite (exec_execute_STORE_8_gpr rs2 csp_rs1 imm_l region sP
                ltac:(vm_compute; discriminate) Hrs2 Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hpmm)
                ltac:(rewrite Lspp; exact Halign) ltac:(intro j; rewrite Lpmpcp; exact (Hpmpf j))
                ltac:(rewrite Lpmap Lspp; exact Hmatch) ltac:(rewrite Lspp; exact Hpalign)
                Hwrite ltac:(rewrite Lspp; apply Hwc) ltac:(rewrite Lspp; apply Hws)
                ltac:(rewrite Lspp; apply Hwh)).
      subst sX. do 3 f_equal. rewrite Lspp Lrs2p. reflexivity. }
    assert (Hcexec1 : exec (execute (C_SDSP (uimm, Regidx rs2))) sP
       = Some (ExecuteAs (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8)), sP)).
    { rewrite exec_execute_C_SDSP. change sp with (Regidx csp_rs1). reflexivity. }
    assert (HhartX : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhs. }
    assert (HmiX : register_lookup (R_bool minstret_increment) sX.(sregs) = b1).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; rewrite register_lookup_set; reflexivity. }
    assert (Hnpc_sX : register_lookup nextPC sX.(sregs) = add_vec_int pc 2).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; rewrite register_lookup_set; reflexivity. }
    assert (Hmst_sX : register_lookup minstret sX.(sregs) = (register_lookup minstret s.(sregs))).
    { unfold sX; cbn [sregs]. unfold sP, s_pcl, sAl; trans_mi; trans_mi; reflexivity. }
    iModIntro.
    iExists (if b1 then set_reg (set_reg sX PC (add_vec_int pc 2)) minstret (add_vec_int (register_lookup minstret s.(sregs)) 1)
                   else set_reg sX PC (add_vec_int pc 2)). iSplitR.
    { iPureIntro.
      apply (forward_exec_rvc_step s pc b1 (subrange_vec_dec w 15 0) (C_SDSP (uimm, Regidx rs2))
               (STORE (imm_l, Regidx rs2, Regidx csp_rs1, 8)) sX (register_lookup minstret s.(sregs))
               Hfetch_at Hsi_s Hds Hcexec1 Hcexec2 HhartX HmiX Hnpc_sX Hmst_sX Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold sX, sP, s_pcl, sAl, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro.
      unfold sX, sP, s_pcl, sAl, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpCsdspGpr4.

(* ===================================================================== *)
(* c.and crsd,crs2 = RTYPE AND (rsd:=rsd&rs2). cregidx operands.            *)
(* ===================================================================== *)
Lemma exec_execute_C_AND (rsd rs2 : cregidx) s :
  exec (execute (C_AND (rsd, rs2))) s
  = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, AND)), s).
Proof. unfold execute. cbn match. unfold execute_C_AND. apply exec_returnM. Qed.

Lemma gpr_and_val_file_l (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_and_val rs2 rs1 (s_pcl s pc b) = and_vec va vb.
Proof.
  intros H1 H2 Lva Lvb. rewrite (gpr_and_val_lookup rs2 rs1 (s_pcl s pc b) H1 H2).
  unfold s_pcl, sAl. unfold set_reg; cbn [sregs]. do 4 gpr_trans. rewrite Lva. rewrite Lvb. reflexivity.
Qed.

Section WpCandGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cand_gpr (pc : mword 64) (w16 : mword 16) (crsd crs2 : cregidx) (rsd rs2 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd vrs2 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    creg2reg_idx crsd = Regidx rsd -> creg2reg_idx crs2 = Regidx rs2 ->
    uint rsd <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_AND (crsd, crs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (and_vec vrsd vrs2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hcrsd Hcrs2 Hrd Hrs2 Hmrd Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hrs2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hrs2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hrs2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_and_val rs2 rsd (s_pcl s pc b1) = and_vec vrsd vrs2)
      by (apply (gpr_and_val_file_l s pc b1 rs2 rsd vrsd vrs2 Hrd Hrs2 Lrd Lrs2)).
    assert (Hcexec1 : exec (execute (C_AND (crsd, crs2))) (s_pcl s pc b1)
                    = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, AND)), s_pcl s pc b1)).
    { rewrite exec_execute_C_AND. rewrite Hcrsd. rewrite Hcrs2. reflexivity. }
    assert (Hcexec2 : exec (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, AND))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_and_val rs2 rsd (s_pcl s pc b1))))).
    { change (execute (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, AND)))
        with (execute_RTYPE (Regidx rs2) (Regidx rsd) (Regidx rsd) AND).
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rsd rsd (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_and_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_and_val rs2 rsd (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_AND (crsd, crs2))
               (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, AND)) rsd
               (gpr_and_val rs2 rsd (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_and_val rs2 rsd (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (and_vec vrsd vrs2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCandGpr.


(* ===================================================================== *)
(* c.ldsp rd,uimm(sp) = LOAD 8 (rd := mem[sp+imm]).  base = sp(x2).        *)
(* ===================================================================== *)
Lemma exec_execute_C_LDSP (uimm : mword 6) (rd : regidx) s :
  exec (execute (C_LDSP (uimm, rd))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, rd, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LDSP. cbn zeta. apply exec_returnM. Qed.

Section WpCldspGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cldsp_gpr (pc : mword 64) (w16 : mword 16) (uimm : mword 6)
      (rd : mword 5) (m : gmap register_bitvector_64 (mword 64))
      (vrs1 vd misa0 mdv0 : mword 64) (b1 : bool) (v : bv 64)
      (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let imm_l := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vrs1 offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    uint csp_rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint csp_rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_LDSP (uimm, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN imm_l offset ea a8 pa data2 Hrs1 Hrd Hmrs1 Hmrd Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HisRVC Hmisa HS Hdl Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & Hread & _).
    iIntros "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (sP := s_pcl s pc b1).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) sP.(sregs) = vrs1).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lrs1. }
    assert (Lprivp : register_lookup cur_privilege sP.(sregs) = Machine).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus sP.(sregs) = mstatus0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg sP.(sregs) = mseccfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n sP.(sregs) = pmpcfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions sP.(sregs) = pmar0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base sP.(sregs) = None).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 sP (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 sP (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 sP Lhtifp) as Hwh.
    assert (Hcexec2 :
      exec (execute (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8))) sP
      = Some (RETIRE_SUCCESS, set_reg sP (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8_gpr csp_rs1 rd imm_l v region sP Hrs1 Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hpmm.
      - rewrite Lrs1p. exact Halign.
      - intro j. rewrite Lpmpcp. exact (Hpmpf j).
      - rewrite Lpmap Lrs1p. exact Hmatch.
      - rewrite Lrs1p. exact Hpalign.
      - exact Hread.
      - rewrite Lrs1p. apply Hwc.
      - rewrite Lrs1p. apply Hws.
      - rewrite Lrs1p. apply Hwh.
      - intros j Hj. rewrite Lrs1p. exact (Hbytesf j Hj). }
    assert (Hcexec1 : exec (execute (C_LDSP (uimm, Regidx rd))) sP
       = Some (ExecuteAs (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8)), sP)).
    { rewrite exec_execute_C_LDSP. change sp with (Regidx csp_rs1). reflexivity. }
    iModIntro.
    iExists (sFcg s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_LDSP (uimm, Regidx rd))
               (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8)) rd
               (extend_value false data2) Hfetch_at Hsi_s Hdl Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpCldspGpr.

Section WpCldspGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_cldsp_gpr_4 (pc : mword 64) (w : mword 32) (uimm : mword 6)
      (rd : mword 5) (m : gmap register_bitvector_64 (mword 64))
      (vrs1 vd misa0 mdv0 : mword 64) (b1 : bool) (v : bv 64)
      (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    let imm_l := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vrs1 offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    uint csp_rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint csp_rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_LDSP (uimm, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN imm_l offset ea a8 pa data2 Hrs1 Hrd Hmrs1 Hmrd Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HisRVC Hmisa HS Hdl Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & Hread & _).
    iIntros "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (sP := s_pcl s pc b1).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint csp_rs1))) sP.(sregs) = vrs1).
    { unfold sP, s_pcl, sAl. gpr_trans. trans_mi. exact Lrs1. }
    assert (Lprivp : register_lookup cur_privilege sP.(sregs) = Machine).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus sP.(sregs) = mstatus0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg sP.(sregs) = mseccfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n sP.(sregs) = pmpcfg0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions sP.(sregs) = pmar0).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base sP.(sregs) = None).
    { unfold sP, s_pcl, sAl; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 sP (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 sP (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 sP Lhtifp) as Hwh.
    assert (Hcexec2 :
      exec (execute (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8))) sP
      = Some (RETIRE_SUCCESS, set_reg sP (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8_gpr csp_rs1 rd imm_l v region sP Hrs1 Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hpmm.
      - rewrite Lrs1p. exact Halign.
      - intro j. rewrite Lpmpcp. exact (Hpmpf j).
      - rewrite Lpmap Lrs1p. exact Hmatch.
      - rewrite Lrs1p. exact Hpalign.
      - exact Hread.
      - rewrite Lrs1p. apply Hwc.
      - rewrite Lrs1p. apply Hws.
      - rewrite Lrs1p. apply Hwh.
      - intros j Hj. rewrite Lrs1p. exact (Hbytesf j Hj). }
    assert (Hcexec1 : exec (execute (C_LDSP (uimm, Regidx rd))) sP
       = Some (ExecuteAs (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8)), sP)).
    { rewrite exec_execute_C_LDSP. change sp with (Regidx csp_rs1). reflexivity. }
    iModIntro.
    iExists (sFcg s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd (extend_value false data2) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_LDSP (uimm, Regidx rd))
               (LOAD (imm_l, Regidx csp_rs1, Regidx rd, false, 8)) rd
               (extend_value false data2) Hfetch_at Hsi_s Hdl Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpCldspGpr4.


(* ===================================================================== *)
(* c.addiw rsd,imm = ADDIW (rsd := sext32(rsd+imm)). reads+writes rsd.    *)
(* ===================================================================== *)
Lemma exec_execute_C_ADDIW (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDIW (imm, rsd))) s
  = Some (ExecuteAs (ADDIW (sign_extend' 12 imm, rsd, rsd)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDIW. apply exec_returnM. Qed.

Definition caddiw_wval (imm6 : mword 6) (vrsd : mword 64) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec (add_vec vrsd (sign_extend' 64 (sign_extend' 12 imm6))) 31 0).

Lemma addiw_val_file_l (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (immv : mword 12) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_addiw_val rs1 immv (s_pcl s pc b)
  = sign_extend' 64 (subrange_vec_dec (add_vec va (sign_extend' 64 immv)) 31 0).
Proof.
  intros H1 Lva. unfold gpr_addiw_val, gpr_src, s_pcl, sAl.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  unfold set_reg; cbn [sregs]. do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section WpCaddiwGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_caddiw_gpr (pc : mword 64) (w16 : mword 16) (rsd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rsd <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_ADDIW (imm6, Regidx rsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (caddiw_wval imm6 vrsd)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmrd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1) = caddiw_wval imm6 vrsd)
      by (unfold caddiw_wval; apply (addiw_val_file_l s pc b1 rsd (sign_extend' 12 imm6) vrsd Hrd Lrd)).
    assert (Hcexec1 : exec (execute (C_ADDIW (imm6, Regidx rsd))) (s_pcl s pc b1)
                    = Some (ExecuteAs (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd)), s_pcl s pc b1))
      by apply exec_execute_C_ADDIW.
    assert (Hcexec2 : exec (execute (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1))))).
    { rewrite (exec_execute_ADDIW_gpr rsd rsd (sign_extend' 12 imm6) (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC2 pc w16 region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 w16 (C_ADDIW (imm6, Regidx rsd))
               (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd)) rsd
               (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (caddiw_wval imm6 vrsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddiwGpr.

Section WpCaddiwGpr4.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_caddiw_gpr_4 (pc : mword 64) (w : mword 32) (rsd : mword 5) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vrsd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rsd <> 0 ->
    m !! gpr_of_Z (uint rsd) = Some vrsd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_ADDIW (imm6, Regidx rsd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rsd) := regval_into_reg (caddiw_wval imm6 vrsd)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmrd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC Hmisa HS Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc #Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc1 Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb1" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1) = caddiw_wval imm6 vrsd)
      by (unfold caddiw_wval; apply (addiw_val_file_l s pc b1 rsd (sign_extend' 12 imm6) vrsd Hrd Lrd)).
    assert (Hcexec1 : exec (execute (C_ADDIW (imm6, Regidx rsd))) (s_pcl s pc b1)
                    = Some (ExecuteAs (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd)), s_pcl s pc b1))
      by apply exec_execute_C_ADDIW.
    assert (Hcexec2 : exec (execute (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd))) (s_pcl s pc b1)
      = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1) (R_bitvector_64 (gpr_of_Z (uint rsd)))
                (regval_into_reg (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1))))).
    { rewrite (exec_execute_ADDIW_gpr rsd rsd (sign_extend' 12 imm6) (s_pcl s pc b1)).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd). reflexivity. }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rsd (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rsd (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write s pc b1 (subrange_vec_dec w 15 0) (C_ADDIW (imm6, Regidx rsd))
               (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd)) rsd
               (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1)) Hfetch_at Hsi_s Hdec Hcexec1 Hcexec2 Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg (gpr_addiw_val rsd (sign_extend' 12 imm6) (s_pcl s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (caddiw_wval imm6 vrsd)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCaddiwGpr4.
