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
Import Defs.

(* register-generic base-address read (any rs1, not just x2). *)
Lemma exec_ext_data_get_addr_gpr (rs1 : mword 5) (offset : mword 64) acc w s :
  uint rs1 <> 0 ->
  exec (ext_data_get_addr (Regidx rs1) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset)), s).
Proof.
  intro H. unfold ext_data_get_addr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (proj2 (Z.eqb_neq (uint rs1) 0) H). cbn match.
  apply exec_returnm.
Qed.

(* register-generic 8-byte vmem_read: base address from ANY rs1. *)
Section VRg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrs1 : uint rs1 <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s Hrs1)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8 a8 v region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes).
  reflexivity.
Qed.
End VRg.

(* register-generic LOAD execute: base from rs1, result to rd (rs1 may differ from rd). *)
Section ExecLoadG.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrs1 : uint rs1 <> 0.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr rs1 offset v region s Hrs1 Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadG.

(* exec-level register-generic LOAD step (32-bit, F_Base): ANY rs1/rd. *)
Section ForwardLDg.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 12)
          (rs1 rd : mword 5) (data : mword 64) (b : bool).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hexec_spc :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                    (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data))).

  Definition sAlg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXlg : mstate :=
    set_reg (set_reg sAlg nextPC (add_vec_int pc 4)) (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (extend_value false data)).
  Definition sTlg : mstate := set_reg sXlg PC (register_lookup nextPC sXlg.(sregs)).
  Definition sFlg : mstate :=
    if b then set_reg sTlg minstret (add_vec_int (register_lookup minstret sTlg.(sregs)) 1)
         else sTlg.

  Lemma forward_exec_ld_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFlg).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAlg.(sregs) = pc).
    { unfold sAlg. trans_mi. exact Lpc. }
    assert (LprivA: register_lookup cur_privilege sAlg.(sregs) = Machine).
    { unfold sAlg. trans_mi. exact Lpriv. }
    assert (LhsA  : register_lookup hart_state sAlg.(sregs) = HART_ACTIVE tt).
    { unfold sAlg. trans_mi. exact Lhs. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAlg.(sregs))) ('b"1") = true).
    { unfold sAlg. trans_mi. exact LS. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAlg.(sregs))) ('b"1") = false).
    { unfold sAlg. trans_mi. exact LmIE. }
    assert (LelpA : eq_vec (register_lookup elp sAlg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAlg. trans_mi. exact Lelp. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAlg = Some (None, sAlg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAlg _ (exec_currentlyEnabled_S sAlg) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAlg = Some (F_Base w, sAlg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAlg
              = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), sAlg))
      by (apply Hdec_gen; exact LprivA).
    pose (s_pc := set_reg sAlg nextPC (add_vec_int pc 4)).
    assert (LpcAA : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc. trans_mi. exact LpcA. }
    assert (HexecA : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
              = Some (RETIRE_SUCCESS, sXlg)).
    { unfold sXlg, s_pc, sAlg. exact Hexec_spc. }
    assert (Hha : exec (run_hart_active 0) sAlg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXlg)).
    { exact (exec_hart_active_progress sAlg sAlg sXlg sAlg w
               (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    apply (exec_riscv_step_ADD s sXlg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXlg, sAlg; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXlg, sAlg; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  Variable mst0 : mword 64.
  Hypothesis Lmst_l : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_lg : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data)))
            PC (add_vec_int pc 4).
  Definition sFclg : mstate :=
    if b then set_reg base_upd_lg minstret (add_vec_int mst0 1)
         else base_upd_lg.

  Lemma sFl_eq_gpr : sFlg = sFclg.
  Proof.
    assert (Enpc : register_lookup nextPC sXlg.(sregs) = add_vec_int pc 4).
    { unfold sXlg; unfold set_reg; cbn [sregs]. tmig.
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTlg = base_upd_lg).
    { unfold sTlg. rewrite Enpc. unfold sXlg, sAlg, base_upd_lg. reflexivity. }
    unfold sFlg, sFclg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_lg.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_lg, set_reg; cbn [sregs]. tmig. tmig. tmig. tmig. reflexivity. }
    rewrite Emst Lmst_l. reflexivity.
  Qed.
End ForwardLDg.

(* ====================================================================== *)
(* The register-GENERIC load WP: ONE lemma for `ld rd, imm(rs1)` for ANY   *)
(* rd/rs1, with all GPRs held as the single [gpr_file] resource.           *)
(* ====================================================================== *)
Section WpLoadGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_load_gpr (pc : mword 64) (w_l : mword 32) (imm_l : mword 12)
      (rs1 rd : mword 5) (m : gmap register_bitvector_64 (mword 64))
      (vrs1 vd misa0 mdv0 : mword 64) (b1 : bool) (v : bv 64)
      (npc0a mst0a mstatus0a : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (mi0a : bool) (elp0a : mword 1)
      E {dq : dfrac} (Φ : mval -> iProp Σ) :
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec vrs1 offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w_l 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w_l) s0 = Some (LOAD (imm_l, Regidx rs1, Regidx rd, false, 8), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0a) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0a -∗
    (R_bool minstret_increment) ↦ᵣ mi0a -∗ minstret ↦ᵣ mst0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_l j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0a 1 else mst0a) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_l j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea a8 pa data2 Hrs1 Hrd Hmrs1 Hmrd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HnotRVCf Hdl Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & Hread & _).
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w_l region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
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
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int pc 4)).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs) = vrs1).
    { unfold s_pc. gpr_trans. trans_mi. exact Lrs1. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine).
    { unfold s_pc; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = mstatus0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_pc Lhtifp) as Hwh.
    assert (Hexec_spc :
      exec (execute (LOAD (imm_l, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8_gpr rs1 rd imm_l v region s_pc Hrs1 Hrd Lprivp).
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
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFclg s pc rd data2 b1 mst0a). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq_gpr s w_l pc imm_l rs1 rd data2 b1 Hfetch_at Hsi_s Hexec_spc mst0a Lmst).
      apply (forward_exec_ld_gpr s w_l pc imm_l rs1 rd data2 b1 Hrd Hfetch_at Hdl Hsi_s Hexec_spc
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFclg, base_upd_lg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0a 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpLoadGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_load_gpr] serves many (rd,rs1) pairs.      *)
(* Only the register operands differ between `ld x5, _(x6)` and            *)
(* `ld x28, _(x1)`.                                                        *)
(* ====================================================================== *)
Section WpLoadGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  (* `ld x5, imm(x6)` : rd=x5, rs1=x6.  Same lemma, instantiated. *)
  Definition wp_load_x5_x6 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_load_gpr (dqc:=DfracOwn 1) pc w imm (mword_of_int 6) (mword_of_int 5).
  (* `ld x28, imm(x1)` : rd=x28, rs1=x1.  SAME lemma, different regs. *)
  Definition wp_load_x28_x1 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_load_gpr (dqc:=DfracOwn 1) pc w imm (mword_of_int 1) (mword_of_int 28).

  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ uint (mword_of_int 28 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpLoadGprDemo.
