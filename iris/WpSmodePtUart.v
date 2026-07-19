(* WpSmodePtUart.v -- the S-mode UART device leaves over the generalized
   page-table invariant [tlb_inv_pt].  The data translate goes through the
   DEVICE-side absorption wrappers [tlb_inv_pt_translateAddr_store_dev]/
   [_load_dev] (the UART vpn is kpt-mapped via the [kpt_dev_vpn] disjunct),
   so the TLB hit/walk split and all the walk-PTE plumbing disappear; the
   [dev_inv] open/close across the step is unchanged from WpUartKpt.v.
   The store towers are the state-generic clones of WpSmodeUart's
   (the translate output memory may carry an A/D write-back). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import InstrBytes.
Require Import KptPt SmodeCore.
Require Import WpLoad WpGpr.
Require Import WpMmodeLeafBase WpSmodeGpr.
Require Import WpUart WpSmodeUart.
Require Import KptTree SmodeCorePt SRegime.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* state-generic width-1 device STORE towers (WpSmodeUart clones with the *)
(* translate output state fully abstract -- no [s'.(mem) = s.(mem)])      *)
(* ===================================================================== *)
  Section SWS1walkDevPt.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable d' : dev_state.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data = Some d'.

  Lemma exec_vmem_write_addr_1_S_walk_dev_pt :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) s'.(mem) d').
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) s'.(mem) d'))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s'
                      = Some (tt, s')) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s' = Some (inr tt, s'))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s'
                             = Some (inr true, MState s'.(sregs) s'.(mem) d'))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_1 (zero_extend' 64 (add_vec_int a (0*1))) s')).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 1 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (1*(0+1)*8-1) with 7. change (1*0*8) with 0. change (1*8) with 8.
               change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold subrange_vec_dec. change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_dev_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data d'
               (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS1walkDevPt.

  Section VWgS1walkDevPt.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable d' : dev_state.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data = Some d'.

  Lemma exec_vmem_write_1_gpr_S_walk_dev_pt :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) s'.(mem) d').
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      rewrite Ha8ea. apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_1_S_walk_dev_pt a8 data d' region s s' Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr).
    reflexivity.
  Qed.
  End VWgS1walkDevPt.

  Section ExecStoreGS1walkDevPt.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable d' : dev_state.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Let data_byte : mword 8 := autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data_byte = Some d'.

  Lemma exec_execute_STORE_1_gpr_S_walk_dev_pt :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) s'.(mem) d').
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 1)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 1).
    unfold execute_STORE.
    replace (1 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_1_gpr_S_walk_dev_pt rs1 offset data_byte d' region s s' Htea Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walkDevPt.

Section WpSmodePtUart.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{!uartGhostG Σ}.
Context `{CID : CpuId}.
Existing Instance riscv_memGS.

Lemma wp_sb_uart_s_r (Rg : s_regime) (γ : gname) (γd : uart_names)
    (off : Z) (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : gmap regidx (mword 64)) (R S : iProp Σ) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) in
  let lppn := kpt_leaf_ppn uart_vpn in
  (0 <= off < uart_size)%Z ->
  (* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
     ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  smode_config γ dq -∗
  sr_inv Rg -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
  dev_inv γd -∗
  R -∗
  (∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
     uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S) -∗
  ( smode_config γ dq -∗
    sr_inv Rg -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗ gpr_file m -∗
    S -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 storebyte lppn Hoff Hcanon Hvpn_def Hident Hpa.
  iIntros "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hdinv HR Hacc Hcont".
  assert (Ha8pa : a8 = uart_pa off).
  { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry. apply zero_extend'_id. }
  assert (Hdevvpn : kpt_dev_vpn (svpn_of a8)).
  { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
    assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia. }
  assert (Hident_pt : zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
            (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
  { unfold svpn_of. rewrite Hvpn_def. rewrite Hident. symmetry. exact Ha8pa. }
  iDestruct (smode_config_unbundle with "Hsm") as
    "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
  iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
  iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
  iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  destruct (Hpma_all (uart_pa off) 1) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  iApply (wp_instr_s_config_regime Rg Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 1)) mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
            with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
  iIntros (σ Hpceq)
    "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1)) by (apply lookup_lookup_total_dom; apply Hdom).
  assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2)) by (apply lookup_lookup_total_dom; apply Hdom).
  iDestruct "Hdev" as "[Hua Hpldev]".
  iInv "Hdinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u p) "(Huf & Hplf & Hg)".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  destruct (uart_write_total u off storebyte Hoff) as [u' Hwrite_u].
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform Rg (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htlbinv") as %Htea.
  iMod (sr_absorb_dev Rg (Store Data) a8 s_pc
          (or_intror eq_refl) Hdevvpn Hcanon Hident_pt
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' with "Hreg Hmem Htlbinv")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)".
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_uart : dev_write s_tr.(mdev) (uart_pa off) 1 storebyte = Some (set_duart σ.(mdev) u')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_write_uart σ.(mdev) off storebyte u' Hoff). rewrite <- Hduart. exact Hwrite_u. }
  assert (Htr_uart : exec (translateAddr (Virtaddr a8) (Store Data)) s_pc
                     = Some (Ok (Physaddr (uart_pa off), PBMT_PMA, init_ext_ptw), s_tr)).
  { replace (uart_pa off) with a8 by exact Ha8pa. exact Htr0. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_1_gpr_S_walk_dev_pt rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva Hpa; change (0 * 1)%Z with 0%Z; rewrite avi0; exact Htr_uart)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva Hpa; exact Hmatch_st)
               Hwrite_st
               ltac:(rewrite !Lva Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
               ltac:(rewrite !Lva Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
               ltac:(rewrite !Lva Hpa; apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva Hpa; apply dev_addr_uart; exact Hoff)
               ltac:(rewrite !Lva !Lv2 Hpa; exact Hwr_uart)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev] Huf") as "[Hdev' Huf']".
  iMod ("Hacc" $! u u' with "[//] Hg HR") as "[Hg' HS]".
  iMod ("Hdclose" with "[Huf' Hplf Hg']") as "_".
  { iNext. iExists u', p. iFrame. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
               HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
               with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
  iApply ("Hcont" with "Hsm Htlbinv [$Hpc' $Hnpc] [Hfmap] HS").
  iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
Qed.

Lemma wp_sb_uart_s_pt (root_ppn : mword 44) (γ : gname) (γd : uart_names)
    (off : Z) (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : gmap regidx (mword 64)) (R S : iProp Σ) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) in
  let lppn := kpt_leaf_ppn uart_vpn in
  (0 <= off < uart_size)%Z ->
  (* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
     ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  smode_config γ dq -∗
  tlb_inv_pt root_ppn -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
  dev_inv γd -∗
  R -∗
  (∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
     uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S) -∗
  ( smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗ gpr_file m -∗
    S -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  exact (wp_sb_uart_s_r (kpt_regime root_ppn) γ γd off Φ pc is_rvc rs2 rs1 imm m R S (dq:=dq)).
Qed.

Lemma wp_lb_uart_s_r (Rg : s_regime) (γ : gname) (γd : uart_names)
    (off : Z) (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) (imm : mword 12)
    (m : gmap regidx (mword 64)) (R : iProp Σ) (S : bv 8 -> iProp Σ) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval := fun (b : bv 8) =>
        (extend_value is_unsigned (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) b) : mword 64) in
  let lppn := kpt_leaf_ppn uart_vpn in
  (0 <= off < uart_size)%Z ->
  uint rd <> 0 ->
  (* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
     ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  smode_config γ dq -∗
  sr_inv Rg -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
  dev_inv γd -∗
  R -∗
  (∀ u b u', ⌜ uart_read u off = Some (b, u') ⌝ -∗
     uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S b) -∗
  ( ∀ b : bv 8,
    smode_config γ dq -∗
    sr_inv Rg -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    gpr_file (<[Regidx rd := regval_into_reg (ldval b)]> m) -∗
    S b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 ldval lppn Hoff Hrd Hcanon Hvpn_def Hident Hpa.
  iIntros "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr #Hdinv HR Hacc Hcont".
  assert (Ha8pa : a8 = uart_pa off).
  { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry. apply zero_extend'_id. }
  assert (Hdevvpn : kpt_dev_vpn (svpn_of a8)).
  { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
    assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia. }
  assert (Hident_pt : zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
            (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
  { unfold svpn_of. rewrite Hvpn_def. rewrite Hident. symmetry. exact Ha8pa. }
  iDestruct (smode_config_unbundle with "Hsm") as
    "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
  iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
  iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
  iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
  destruct (Hpma_all (uart_pa off) 1) as (region_ld & Hmatch_ld & _ & Hread_ld & _ & _).
  iApply (wp_instr_s_config_regime Rg Φ pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
            with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
  iIntros (σ Hpceq)
    "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1)) by (apply lookup_lookup_total_dom; apply Hdom).
  assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd)) by (apply lookup_lookup_total_dom; apply Hdom).
  iDestruct "Hdev" as "[Hua Hpldev]".
  iInv "Hdinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u p) "(Huf & Hplf & Hg)".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  destruct (uart_read_total u off Hoff) as (b & u' & Hread_u).
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform Rg (Load Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htlbinv") as %Htea.
  iMod (sr_absorb_dev Rg (Load Data) a8 s_pc
          (or_introl eq_refl) Hdevvpn Hcanon Hident_pt
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' with "Hreg Hmem Htlbinv")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)".
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hdrd_uart : dev_read s_tr.(mdev) (uart_pa off) 1 = Some (b, set_duart σ.(mdev) u')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_read_uart σ.(mdev) off b u' Hoff). rewrite <- Hduart. exact Hread_u. }
  assert (Htr_uart : exec (translateAddr (Virtaddr a8) (Load Data)) s_pc
                     = Some (Ok (Physaddr (uart_pa off), PBMT_PMA, init_ext_ptw), s_tr)).
  { replace (uart_pa off) with a8 by exact Ha8pa. exact Htr0. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ldval b))).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_1_gpr_S_walk_dev rs1 rd imm is_unsigned b d' region_ld s_pc s_tr
             Hrd Htea
             ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
             ltac:(cbn [bits_of_virtaddr]; rewrite !Lva Hpa; change (0 * 1)%Z with 0%Z; rewrite avi0; exact Htr_uart)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva Hpa; exact Hmatch_ld)
             Hread_ld
             ltac:(rewrite !Lva Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
             ltac:(rewrite !Lva Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
             ltac:(rewrite !Lva Hpa; apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva Hpa; apply dev_addr_uart; exact Hoff)
             ltac:(rewrite !Lva Hpa; exact Hdrd_uart)). }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev] Huf") as "[Hdev' Huf']".
  iMod ("Hacc" $! u b u' with "[//] Hg HR") as "[Hg' HS]".
  iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz rd _ Hrd).
  iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ldval b)) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" $! (regval_into_reg (ldval b)) with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
  iMod ("Hdclose" with "[Huf' Hplf Hg']") as "_".
  { iNext. iExists u', p. iFrame. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x, set_reg; cbn [sregs]. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
               HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
               with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
  iApply ("Hcont" $! b with "Hsm Htlbinv [$Hpc' $Hnpc] [Hfmap] HS").
  iSplitR.
  { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
  iExact "Hfmap".
Qed.

Lemma wp_lb_uart_s_pt (root_ppn : mword 44) (γ : gname) (γd : uart_names)
    (off : Z) (Φ : mval -> iProp Σ)
    (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) (imm : mword 12)
    (m : gmap regidx (mword 64)) (R : iProp Σ) (S : bv 8 -> iProp Σ) {dq : dfrac} :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval := fun (b : bv 8) =>
        (extend_value is_unsigned (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) b) : mword 64) in
  let lppn := kpt_leaf_ppn uart_vpn in
  (0 <= off < uart_size)%Z ->
  uint rd <> 0 ->
  (* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
     ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
  zero_extend' 64 (concat_vec lppn (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = uart_pa off ->
  zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
  smode_config γ dq -∗
  tlb_inv_pt root_ppn -∗
  pc_is pc -∗ gpr_file m -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
  dev_inv γd -∗
  R -∗
  (∀ u b u', ⌜ uart_read u off = Some (b, u') ⌝ -∗
     uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S b) -∗
  ( ∀ b : bv 8,
    smode_config γ dq -∗
    tlb_inv_pt root_ppn -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    gpr_file (<[Regidx rd := regval_into_reg (ldval b)]> m) -∗
    S b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  exact (wp_lb_uart_s_r (kpt_regime root_ppn) γ γd off Φ pc is_rvc is_unsigned rd rs1 imm m R S (dq:=dq)).
Qed.

End WpSmodePtUart.
