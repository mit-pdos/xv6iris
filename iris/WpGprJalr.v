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

(* currentlyEnabled Ext_Zicfilp = the mseccfg MLPE bit; false in the boot config.
   Adapted from WpDecode.exec_cE_zicfilp_M, pinning the value. *)
Lemma exec_cE_zicfilp_false s :
  register_lookup cur_privilege (sregs s) = Machine ->
  bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs))) = false ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
Proof.
  intros Hpriv Hmlpe.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). cbn match.
  rewrite Hmlpe. apply exec_returnM.
Qed.

(* register-generic JALR execute: target = (rX rs1 + imm) with bit0 cleared;
   writes rd := link (nextPC), sets nextPC := target.  rs1<>0, rd<>0. *)
Lemma exec_execute_JALR_gpr (imm : mword 12) (rs1 rd : mword 5) s :
  uint rs1 <> 0 -> uint rd <> 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 1) = false ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrs1 Hrd Hzic Halign Hbit1.
  unfold execute_JALR.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
                (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
      2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
      unfold get_next_pc. exact (exec_read_reg nextPC s). }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
                (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Section ForwardJALRg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (imm : mword 12) (rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs10 : uint rs1 <> 0.
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0).
  Hypothesis Hmlpe : bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs))) = false.

  Definition sArg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcrg : mstate := set_reg sArg nextPC (add_vec_int pc 4).
  Definition jrtgt : mword 64 :=
    update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pcrg.(sregs))
                            (sign_extend' 64 imm)) 0 ('b"0").
  Definition sXrg : mstate :=
    set_reg (set_reg s_pcrg nextPC jrtgt)
            (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (register_lookup nextPC s_pcrg.(sregs))).
  Definition sTrg : mstate := set_reg sXrg PC (register_lookup nextPC sXrg.(sregs)).
  Definition sFrg : mstate :=
    if b then set_reg sTrg minstret (add_vec_int (register_lookup minstret sTrg.(sregs)) 1)
         else sTrg.

  Lemma forward_exec_jalr_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (access_vec_dec jrtgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec jrtgt 1) = false ->
    exec riscv_step s = Some (tt, sFrg).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Halign Hbit1.
    assert (LpcA  : register_lookup PC sArg.(sregs) = pc).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sArg.(sregs) = Machine).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sArg.(sregs) = HART_ACTIVE tt).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sArg.(sregs))) ('b"1") = true).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sArg.(sregs))) ('b"1") = false).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sArg.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sArg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sArg = Some (None, sArg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sArg _ (exec_currentlyEnabled_S sArg) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sArg = Some (F_Base w, sArg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sArg = Some (JALR (imm, Regidx rs1, Regidx rd), sArg))
      by (apply Hdec; exact LprivA).
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pcrg = Some (false, s_pcrg)).
    { apply exec_cE_zicfilp_false.
      - unfold s_pcrg, sArg, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity].
      - unfold s_pcrg, sArg, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Hmlpe | vm_compute; reflexivity]. }
    assert (HexecJR : exec (execute (JALR (imm, Regidx rs1, Regidx rd))) s_pcrg
              = Some (RETIRE_SUCCESS, sXrg)).
    { change (execute (JALR (imm, Regidx rs1, Regidx rd)))
        with (execute_JALR imm (Regidx rs1) (Regidx rd)).
      rewrite (exec_execute_JALR_gpr imm rs1 rd s_pcrg Hrs10 Hrd0 Hzic Halign Hbit1).
      unfold sXrg, jrtgt. reflexivity. }
    assert (Hha : exec (run_hart_active 0) sArg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXrg)).
    { exact (exec_hart_active_progress sArg sArg sXrg sArg w
               (JALR (imm, Regidx rs1, Regidx rd)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecJR I). }
    apply (exec_riscv_step_ADD s sXrg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXrg, s_pcrg, sArg; cbn zeta. trans_mi. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXrg, s_pcrg, sArg; cbn zeta. trans_mi. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardJALRg.

(* ret = jalr x0, 0(ra): rd = x0 (uint 0) => NO link write; just PC := target. *)
Lemma exec_execute_JALR_ret (imm : mword 12) (rs1 rdz : mword 5) s :
  uint rs1 <> 0 -> uint rdz = 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 1) = false ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))).
Proof.
  intros Hrs1 Hrdz Hzic Halign Hbit1.
  unfold execute_JALR.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
                (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
      2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
      unfold get_next_pc. exact (exec_read_reg nextPC s). }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
                (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))))).
  rewrite Hrdz. cbn match. apply exec_returnm.
Qed.

Section CleanJALRg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (imm : mword 12) (rs1 rd : mword 5) (mst0 : mword 64).
  Definition base_upd_jr : mstate :=
    set_reg
      (set_reg
         (set_reg
            (set_reg (set_reg s (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
            nextPC (jrtgt s pc b imm rs1))
         (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (add_vec_int pc 4)))
      PC (jrtgt s pc b imm rs1).
  Definition sFcjr : mstate :=
    if b then set_reg base_upd_jr minstret (add_vec_int mst0 1) else base_upd_jr.

  Lemma sFj_eq_jalr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFrg s pc b imm rs1 rd = sFcjr.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXrg s pc b imm rs1 rd).(sregs) = jrtgt s pc b imm rs1).
    { unfold sXrg; cbv zeta. unfold set_reg; cbn [sregs]. tmig.
      rewrite register_lookup_set. reflexivity. }
    assert (Elink : register_lookup nextPC (s_pcrg s pc b).(sregs) = add_vec_int pc 4).
    { unfold s_pcrg; cbv zeta. unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTrg s pc b imm rs1 rd = base_upd_jr).
    { unfold sTrg. rewrite Enpc. unfold sXrg; cbv zeta. rewrite Elink.
      unfold base_upd_jr, s_pcrg, sArg. reflexivity. }
    unfold sFrg, sFcjr. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_jr.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_jr, set_reg; cbn [sregs]. tmig. tmig. tmig. tmig. tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanJALRg.

Lemma jrtgt_eq_jalr (s : mstate) (pc : mword 64) (b : bool) (imm : mword 12) (rs1 : mword 5) (vrs1 : mword 64) :
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = vrs1 ->
  jrtgt s pc b imm rs1 = update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0").
Proof.
  intro Lrs1. unfold jrtgt, s_pcrg, sArg. unfold set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [|apply gpr_of_Z_ne_nextPC].
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  rewrite Lrs1. reflexivity.
Qed.

Section WpJalrGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_jalr_gpr (pc : mword 64) (w : mword 32) (imm : mword 12) (rs1 rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 mseccfg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0)) ->
    eq_vec (access_vec_dec (update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0")) 1) = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto mseccfg dqc mseccfg0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0") -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec_int pc 4)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0") -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto mseccfg dqc mseccfg0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hrd Hmrs1 Hmd HS Hmlpe Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hal0 Hal1 Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hrs1c Hrest]".
    iDestruct (reg_valid_dq with "Hreg Hrs1c") as %Lrs1.
    iDestruct ("Hrest" with "Hrs1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hjt : jrtgt s pc b1 imm rs1 = update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0"))
      by (apply jrtgt_eq_jalr; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcjr s pc b1 imm rs1 rd mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFj_eq_jalr s pc b1 imm rs1 rd mst0 Lpc Lmst).
      apply (forward_exec_jalr_gpr s pc b1 w imm rs1 rd Hfetch_at Hsi_s Hrs1 Hrd Hdec
               ltac:(rewrite Lsec; exact Hmlpe) Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Hjt. exact Hal0.
      - rewrite Hjt. exact Hal1. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (jrtgt s pc b1 imm rs1) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (jrtgt s pc b1 imm rs1) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hjt) in "Hpc". iEval (rewrite Hjt) in "Hnpc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4)) with "Hrdc") as "Hfile".
    unfold sFcjr, base_upd_jr. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpJalrGpr.

(* Demonstration: ONE lemma [wp_jalr_gpr] serves many (rs1,rd) pairs; and the
   exec-level [exec_execute_JALR_ret] covers the ret = jalr x0,0(ra) shape. *)
Section WpJalrGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition wp_jalr_x1_x5 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_jalr_gpr (dqc:=DfracOwn 1) pc w imm (mword_of_int 1) (mword_of_int 5).
  Definition wp_jalr_x6_x28 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_jalr_gpr (dqc:=DfracOwn 1) pc w imm (mword_of_int 6) (mword_of_int 28).
  Goal gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 1 : mword 5) <> 0
    /\ uint (mword_of_int 0 : mword 5) = 0.   (* x0 (ret dest) *)
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpJalrGprDemo.
