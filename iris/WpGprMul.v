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
(* Register-GENERIC MUL: ONE WP for 32-bit `mul rd,rs1,rs2`, ANY triple.   *)
(* Structurally identical to the generic ADD (WpGpr.v): reads rs1/rs2,     *)
(* writes rd; only the written value differs (the M-extension product      *)
(* [mult_to_bits_half] instead of [add_vec]).  Reuses [mulop_mul] (the      *)
(* funct3=000 signed/signed/Low op) from WpEntry.v.                         *)
(* ====================================================================== *)

(* The value MUL writes to rd, expressed over the file-generic reads. *)
Definition gpr_mul_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
    (mulop_mul.(mul_op_result_part)).

Lemma exec_execute_MUL_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_mul_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_mul_val.
  change (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)))
    with (execute_MUL (Regidx rs2) (Regidx rs1) (Regidx rd) mulop_mul).
  unfold execute_MUL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Lemma gpr_mul_val_lookup (rs2 rs1 : mword 5) (t : mstate) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  gpr_mul_val rs2 rs1 t
  = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
      (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
      (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) t.(sregs))
      (mulop_mul.(mul_op_result_part)).
Proof.
  intros H1 H2. unfold gpr_mul_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

(* exec-level register-generic MUL step (32-bit, F_Base): ANY rd/rs1/rs2.   *)
Section ForwardMulGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs2 rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul), s0).

  Definition sAmg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcmg : mstate := set_reg sAmg nextPC (add_vec_int pc 4).
  Definition sXmg : mstate :=
    set_reg s_pcmg (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_mul_val rs2 rs1 s_pcmg)).
  Definition sTmg : mstate := set_reg sXmg PC (register_lookup nextPC sXmg.(sregs)).
  Definition sFmg : mstate :=
    if b then set_reg sTmg minstret (add_vec_int (register_lookup minstret sTmg.(sregs)) 1)
         else sTmg.

  Lemma forward_exec_mul_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFmg).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAmg.(sregs) = pc).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAmg.(sregs) = Machine).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAmg.(sregs) = HART_ACTIVE tt).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAmg.(sregs) = zeros' 64).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAmg.(sregs))) ('b"1") = false).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAmg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAmg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAmg = Some (None, sAmg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAmg _ (exec_currentlyEnabled_S sAmg) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAmg = Some (F_Base w, sAmg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAmg
              = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul), sAmg))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))) s_pcmg
              = Some (RETIRE_SUCCESS, sXmg)).
    { unfold sXmg. fold s_pcmg. apply (exec_execute_MUL_gpr rs2 rs1 rd s_pcmg Hrd0). }
    assert (Hha : exec (run_hart_active 0) sAmg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXmg)).
    { exact (exec_hart_active_progress sAmg sAmg sXmg sAmg w
               (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXmg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXmg, s_pcmg, sAmg; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXmg, s_pcmg, sAmg; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardMulGpr.

Lemma gpr_mul_val_file (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_mul_val rs2 rs1 (s_pcmg s pc b)
  = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
      va vb (mulop_mul.(mul_op_result_part)).
Proof.
  intros H1 H2 Lva Lvb.
  rewrite (gpr_mul_val_lookup rs2 rs1 (s_pcmg s pc b) H1 H2).
  unfold s_pcmg, sAmg. unfold set_reg; cbn [sregs].
  do 4 gpr_trans. rewrite Lva. rewrite Lvb. reflexivity.
Qed.

Section CleanMulGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 rd : mword 5) (mst0 : mword 64).
  Definition base_upd_mg : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_mul_val rs2 rs1 (s_pcmg s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcmg : mstate :=
    if b then set_reg base_upd_mg minstret (add_vec_int mst0 1) else base_upd_mg.

  Lemma sFmg_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFmg s pc b rs2 rs1 rd = sFcmg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXmg s pc b rs2 rs1 rd).(sregs) = add_vec_int pc 4).
    { unfold sXmg; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTmg s pc b rs2 rs1 rd = base_upd_mg).
    { unfold sTmg. rewrite Enpc. unfold sXmg, s_pcmg, sAmg; cbv zeta.
      unfold base_upd_mg, s_pcmg, sAmg. reflexivity. }
    unfold sFmg, sFcmg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_mg.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_mg, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanMulGpr.

(* ====================================================================== *)
(* The register-GENERIC MUL WP. *)
(* ====================================================================== *)
Section WpMulGpr.
  Context `{!riscvGS Σ}.

  Lemma wp_mul_gpr (pc : mword 64) (w : mword 32) (rs2 rs1 rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (va vb vd : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rs2 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rs2) = Some vb ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) :=
          regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
            (mulop_mul.(mul_op_signed_rs2)) va vb (mulop_mul.(mul_op_result_part)))]> m) -∗
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
    iIntros (Hr1 Hr2 Hrd Hm1 Hm2 Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
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
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmulv : gpr_mul_val rs2 rs1 (s_pcmg s pc b1)
              = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2)) va vb (mulop_mul.(mul_op_result_part)))
      by (apply (gpr_mul_val_file s pc b1 rs2 rs1 va vb Hr1 Hr2 Lrs1 Lrs2)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcmg s pc b1 rs2 rs1 rd mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFmg_eq s pc b1 rs2 rs1 rd mst0 Lpc Lmst).
      apply (forward_exec_mul_gpr s pc b1 w rs2 rs1 rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_mul_val rs2 rs1 (s_pcmg s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmulv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
            (mulop_mul.(mul_op_signed_rs2)) va vb (mulop_mul.(mul_op_result_part)))) with "Hrdc") as "Hfile".
    unfold sFcmg, base_upd_mg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpMulGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_mul_gpr] serves many register triples.     *)
(* ====================================================================== *)
Section WpMulGprDemo.
  Context `{!riscvGS Σ}.
  (* `mul x5, x6, x7` : rd=x5, rs1=x6, rs2=x7. *)
  Definition wp_mul_x5_x6_x7 (pc : mword 64) (w : mword 32) :=
    wp_mul_gpr pc w (mword_of_int 7) (mword_of_int 6) (mword_of_int 5).
  (* `mul x28, x1, x2` : rd=x28, rs1=x1, rs2=x2.  SAME lemma, different regs. *)
  Definition wp_mul_x28_x1_x2 (pc : mword 64) (w : mword 32) :=
    wp_mul_gpr pc w (mword_of_int 2) (mword_of_int 1) (mword_of_int 28).

  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 7 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpMulGprDemo.
