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
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* The value LUI writes: imm in bits [31:12], sign-extended to 64. *)
Definition luival (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12)).

(* register-GENERIC LUI execute: writes rd := luival imm (no source register). *)
Lemma exec_execute_UTYPE_LUI_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute_UTYPE imm (Regidx rd) LUI) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (luival imm))).
Proof.
  unfold execute_UTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* exec-level register-generic LUI step (32-bit, F_Base): one lemma, ANY rd. *)
Section ForwardLuiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rd : mword 5) (imm : mword 20).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, LUI), s0).

  Definition sAl : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcl : mstate := set_reg sAl nextPC (add_vec_int pc 4).
  Definition sXl : mstate :=
    set_reg s_pcl (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (luival imm)).
  Definition sTl : mstate := set_reg sXl PC (register_lookup nextPC sXl.(sregs)).
  Definition sFl : mstate :=
    if b then set_reg sTl minstret (add_vec_int (register_lookup minstret sTl.(sregs)) 1)
         else sTl.

  Lemma forward_exec_lui_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFl).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAl.(sregs) = Machine).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAl.(sregs))) ('b"1") = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAl = Some (None, sAl)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAl _ (exec_currentlyEnabled_S sAl) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAl = Some (F_Base w, sAl)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAl
              = Some (UTYPE (imm, Regidx rd, LUI), sAl)) by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (UTYPE (imm, Regidx rd, LUI))) s_pcl
              = Some (RETIRE_SUCCESS, sXl)).
    { change (execute (UTYPE (imm, Regidx rd, LUI)))
        with (execute_UTYPE imm (Regidx rd) LUI).
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pcl).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXl)).
    { exact (exec_hart_active_progress sAl sAl sXl sAl w
               (UTYPE (imm, Regidx rd, LUI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXl w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXl, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXl, s_pcl, sAl; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardLuiGpr.

Ltac reg_ne_l := solve [ vm_compute; reflexivity
                       | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Ltac tmil := rewrite irrelevant_register_set; [ | reg_ne_l ].

Section CleanLuiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm : mword 20) (mst0 : mword 64).
  Definition base_upd_l : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (luival imm)))
      PC (add_vec_int pc 4).
  Definition sFcl : mstate :=
    if b then set_reg base_upd_l minstret (add_vec_int mst0 1) else base_upd_l.

  Lemma sFl_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFl s pc b rd imm = sFcl.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXl s pc b rd imm).(sregs) = add_vec_int pc 4).
    { unfold sXl; cbv zeta. unfold set_reg; cbn [sregs].
      tmil. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTl s pc b rd imm = base_upd_l).
    { unfold sTl. rewrite Enpc. unfold sXl, s_pcl, sAl; cbv zeta.
      unfold base_upd_l, s_pcl, sAl. reflexivity. }
    unfold sFl, sFcl. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_l.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_l, set_reg; cbn [sregs]. do 4 tmil. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanLuiGpr.

(* ====================================================================== *)
(* The register-GENERIC LUI WP: ONE lemma covering `lui rd, imm` for ANY   *)
(* rd, with all GPRs held as the single [gpr_file] resource.               *)
(* ====================================================================== *)
Section WpLuiGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_lui_gpr (pc : mword 64) (w : mword 32) (rd : mword 5) (imm : mword 20)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, LUI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (luival imm)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd HS Hpmaall Hpmpf Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
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
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcl s pc b1 rd imm (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc b1 rd imm (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_lui_gpr s pc b1 w rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival imm)) with "Hrdc") as "Hfile".
    unfold sFcl, base_upd_l. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpLuiGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_lui_gpr] serves many destination regs.     *)
(* ====================================================================== *)
Section WpLuiGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition wp_lui_x5  (pc : mword 64) (w : mword 32) (imm : mword 20) :=
    wp_lui_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 5) imm.
  Definition wp_lui_x28 (pc : mword 64) (w : mword 32) (imm : mword 20) :=
    wp_lui_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 28) imm.
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpLuiGprDemo.
