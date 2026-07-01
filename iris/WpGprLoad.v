From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Import Defs.

(* sign-extending a 64-bit word to 64 bits is the identity (cf. zero_extend'_id). *)
Lemma sign_extend'_id (a : mword 64) : sign_extend' 64 a = a.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed. rewrite bv_sign_extend_signed; [ reflexivity | lia ].
Qed.

(* the bare-mode 64-bit address translation extracts bits [63:0] -- a noop. *)
Lemma subrange_id (a : mword 64) : subrange_vec_dec a (xlen - 0 - 1) 0 = a.
Proof.
  apply bv_eq. unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (xlen - 0 - 1 - 0 + 1)) with 64%N.
  apply bv_wrap_bv_unsigned.
Qed.

(* writing all 64 bits of [v] into a zero word yields [v] -- a noop. *)
Lemma data2_id (v : mword 64) :
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v = v.
Proof.
  apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  erewrite bv_concat_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  rewrite !bv_unsigned_N_0.
  rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  reflexivity.
Qed.

(* register-generic base-address read (any rs1, INCLUDING x0 -> zero_reg). *)
Lemma exec_ext_data_get_addr_gpr (rs1 : mword 5) (offset : mword 64) acc w s :
  exec (ext_data_get_addr (Regidx rs1) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec
      (if Z.eqb (uint rs1) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset)), s).
Proof.
  unfold ext_data_get_addr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  cbn match. apply exec_returnm.
Qed.

(* register-generic 8-byte vmem_read: base address from ANY rs1. *)
Section VRg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
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
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
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
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
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
    (exec_vmem_read_8_gpr rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes)).
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
(* The register-GENERIC load WP on the new [instr] / [mmode_config] /       *)
(* [gpr_file] layer.  Uses a HALF fraction of [mmode_config] handed to      *)
(* [wp_instr] and keeps the other half to reason (reg_valid_dq) about the   *)
(* config the load's address translation / PMP checks read at the execute   *)
(* state; the halves are recombined for the continuation.                   *)
(* ====================================================================== *)
Section WpLdGpr.
  Context `{!riscvGS Σ}.

  (* reg_pointsto Fractional/AsFractional, reg_pointsto_agree, and
     mmode_config_split_half / mmode_config_combine_half now live in InstrBytes.v
     (next to mmode_config) -- shared by every memory / control-flow WP. *)

  (* [instr]/[mmode_config]-formulated register-generic 8-byte LOAD WP.  The
     caller supplies the loaded bytes ([pa..pa+7] ↦ₘ) and alignment facts; the
     config the load's translation / PMP checks read is recovered from the KEPT
     half of [mmode_config] + [hw_config].  [rs1<>0] (base) / [rd<>0] (dest). *)
  Lemma wp_ld_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Hrd Halign.
    iIntros "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr E Φ pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    (* base register at the execute state, uniform over rs1 (x0 -> zero_reg). *)
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    (* [extend_value false] is the identity here (the value is already 64-bit). *)
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    (* [ea]/[pa] the model computes coincide with [ea] once the identity
       zero-extends / +0 are stripped; bridge each PMP/translation goal. *)
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - intro j. rewrite Lpmpcp. exact (Hpmp j).
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpLdGpr.
