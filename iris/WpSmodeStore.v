(* S-mode Store leaf lemmas (smode_config/Supervisor, decode family Store).
   Relocated from function proof files (per-(mode,family) leaf reorg). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpSmodeGpr WpLoad.
Require Import WpMmodeLeafBase.
Import Defs.

(* helper: avi0_mul4 *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
  Proof. change (0 * 4) with 0. apply avi0. Qed.

(* helper: exec_write_ram_plain_4 *)
Local Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
    dev_addr addr = false ->
    exec (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
  Proof.
    intros Hdev.
    unfold write_ram. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
    unfold Defs.sail_mem_write. cbn beta zeta iota match.
    unfold Defs.bind. cbn [Interface.iMon_bind].
    cbn match.
    rewrite exec_MemWrite; last exact Hdev.
    reflexivity.
  Qed.

(* helper: exec_pmaCheck_ram_store_4 *)
Local Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (None, s).
  Proof.
    intros Hmatch Halign Hwrite.
    unfold pmaCheck.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
    rewrite Hmatch.
    destruct region as [rbase rsize rattr rdtree].
    cbn [PMA_Region_attributes] in Hwrite |- *.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
    cbn match beta.
    change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
            (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
      with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
    rewrite Hwrite. cbn match.
    apply exec_returnM.
  Qed.

(* helper: exec_split_misaligned_aligned_4 *)
Local Lemma exec_split_misaligned_aligned_4 (vaddr : virtaddr) s :
    is_aligned_vaddr vaddr 4 = true ->
    exec (split_misaligned vaddr 4) s = Some ((1, 4), s).
  Proof.
    intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
  Qed.

(* helper: exec_mem_write_ea_4 *)
Local Lemma exec_mem_write_ea_4 (addr : mword 64) s :
    exec (mem_write_ea (Physaddr addr) 4 false false false) s = Some (Ok tt, s).
  Proof.
    unfold mem_write_ea. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    apply exec_returnM.
  Qed.

(* helper: exec_checked_mem_write_ram_store_4_S *)
Local Lemma exec_checked_mem_write_ram_store_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 32) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) 4 data (Store Data) pbmt Supervisor tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
    unfold checked_mem_write.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store addr 4 s HA Hord Hrange HW)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
        cbn match. apply exec_returnM. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s))).
    2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_4 addr data s Hdev)).
    apply exec_returnM.
  Qed.

(* helper: exec_mem_write_value_4_S *)
Local Lemma exec_mem_write_value_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 32) (m : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
    dev_addr addr = false ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_write_value (Physaddr addr) 4 data (Store Data) pbmt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. rewrite Hms.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
    unfold mem_write_value_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_4_S pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
    cbn match. unfold mem_write_callback. apply exec_returnm.
  Qed.

(* SEC:section:SWS4 *)
  Section SWS4.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_4_S :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                             = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_4 (zero_extend' 64 (add_vec_int a (0*4))) s)).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (4*(0+1)*8-1) with 31. change (4*0*8) with 0. change (4*8) with 32.
               change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_4_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*4))) region data
               (register_lookup mstatus s.(sregs)) s HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS4.

(* SEC:section:VWgS4 *)
  Section VWgS4.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_4_gpr_S :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_4_S a8 data region s Halign Hcp Hmprv Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS4.

(* SEC:section:ExecStoreGS4 *)
  Section ExecStoreGS4.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_gpr_S :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s.(sregs) (write_bytes s.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)) s.(mdev)).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_4_gpr_S rs1 offset _ region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS4.

(* helper: exec_write_ram_plain_1 *)
Local Lemma exec_write_ram_plain_1 (addr : mword 64) (data : bv 8) s :
    dev_addr addr = false ->
    exec (write_ram rv64d_types.Write_plain (Physaddr addr) 1 data tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
  Proof.
    intros Hdev.
    unfold write_ram. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
    unfold Defs.sail_mem_write. cbn beta zeta iota match.
    unfold Defs.bind. cbn [Interface.iMon_bind].
    cbn match.
    rewrite exec_MemWrite; last exact Hdev.
    reflexivity.
  Qed.

(* helper: exec_pmaCheck_ram_store_1 *)
Local Lemma exec_pmaCheck_ram_store_1 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (pmaCheck (Physaddr addr) 1 (Store Data) pbmt false) s = Some (None, s).
  Proof.
    intros Hmatch Halign Hwrite.
    unfold pmaCheck.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
    rewrite Hmatch.
    destruct region as [rbase rsize rattr rdtree].
    cbn [PMA_Region_attributes] in Hwrite |- *.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
    cbn match beta.
    change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
            (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
      with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
    rewrite Hwrite. cbn match.
    apply exec_returnM.
  Qed.

(* helper: exec_checked_mem_write_ram_store_S_1 *)
Local Lemma exec_checked_mem_write_ram_store_S_1 (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 8) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 1)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 1) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) 1 data (Store Data) pbmt Supervisor tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
    unfold checked_mem_write.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store addr 1 s HA Hord Hrange HW)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_1 addr pbmt region s Hmatch Halign Hwrite)).
        cbn match. apply exec_returnM. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_writable (Physaddr addr) 1) s = Some (false, s))).
    2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_1 addr data s Hdev)).
    apply exec_returnM.
  Qed.

(* SEC:section:SWS4walk *)
  Section SWS4walk.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_4_S_walk :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 4 data) s'.(mdev)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) (write_bytes s.(mem) pa 4 data) s'.(mdev)))
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
                             = Some (inr true, MState s'.(sregs) (write_bytes s.(mem) pa 4 data) s'.(mdev)))
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
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_4 (zero_extend' 64 (add_vec_int a (0*4))) s')).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (4*(0+1)*8-1) with 31. change (4*0*8) with 0. change (4*8) with 32.
               change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          assert (Hmem' : s'.(mem) = s.(mem)) by reflexivity.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_4_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*4))) region data
               (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          rewrite Hmem'.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS4walk.

(* helper: exec_mem_write_value_1_S *)
Local Lemma exec_mem_write_value_1_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 8) (m : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 1)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 1) s = Some (false, s) ->
    dev_addr addr = false ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_write_value (Physaddr addr) 1 data (Store Data) pbmt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. rewrite Hms.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
    unfold mem_write_value_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_S_1 pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
    cbn match. unfold mem_write_callback. apply exec_returnm.
  Qed.

(* helper: exec_split_misaligned_aligned_1 *)
Local Lemma exec_split_misaligned_aligned_1 (vaddr : virtaddr) s :
    is_aligned_vaddr vaddr 1 = true ->
    exec (split_misaligned vaddr 1) s = Some ((1, 1), s).
  Proof.
    intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
  Qed.

(* helper: exec_mem_write_ea_1 *)
Local Lemma exec_mem_write_ea_1 (addr : mword 64) s :
    exec (mem_write_ea (Physaddr addr) 1 false false false) s = Some (Ok tt, s).
  Proof.
    unfold mem_write_ea. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    apply exec_returnM.
  Qed.

(* helper: is_aligned_vaddr_1 *)
Local Lemma is_aligned_vaddr_1 (vaddr : virtaddr) : is_aligned_vaddr vaddr 1 = true.
  Proof. destruct vaddr as [addr]. unfold is_aligned_vaddr. rewrite Z.rem_1_r. reflexivity. Qed.

(* helper: is_aligned_paddr_1 *)
Local Lemma is_aligned_paddr_1 (paddr : physaddr) : is_aligned_paddr paddr 1 = true.
  Proof. destruct paddr as [addr]. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

(* SEC:section:SWS1 *)
  Section SWS1.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_1_S :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 1 data) s.(mdev)).
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
                   = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 1 data) s.(mdev)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                             = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 1 data) s.(mdev)))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_1 (zero_extend' 64 (add_vec_int a (0*1))) s)).
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
            (exec_mem_write_value_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data
               (register_lookup mstatus s.(sregs)) s HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS1.

(* SEC:section:VWgS4walk *)
  Section VWgS4walk.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_4_gpr_S_walk :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 4 data) s'.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_4_S_walk a8 data region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS4walk.

(* SEC:section:ExecStoreGS4walk *)
  Section ExecStoreGS4walk.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_gpr_S_walk :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)) s'.(mdev)).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_4_gpr_S_walk rs1 offset _ region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS4walk.

(* SEC:section:VWgS1 *)
  Section VWgS1.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_1_gpr_S :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 1 data) s.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_1_S a8 data region s Halign Hcp Hmprv Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS1.

(* SEC:section:ExecStoreGS1 *)
  Section ExecStoreGS1.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_1_gpr_S :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s.(sregs) (write_bytes s.(mem) pa 1
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0) : mword 8)) s.(mdev)).
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
      (exec_vmem_write_1_gpr_S rs1 offset _ region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1.

(* SEC:section:SWS1walk *)
  Section SWS1walk.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_1_S_walk :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data) s'.(mdev)).
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
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) (write_bytes s.(mem) pa 1 data) s'.(mdev)))
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
                             = Some (inr true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data) s'.(mdev)))
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
          assert (Hmem' : s'.(mem) = s.(mem)) by reflexivity.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data
               (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          rewrite Hmem'.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS1walk.

(* SEC:section:VWgS1walk *)
  Section VWgS1walk.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_1_gpr_S_walk :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data) s'.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_1_S_walk a8 data region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS1walk.

(* SEC:section:ExecStoreGS1walk *)
  Section ExecStoreGS1walk.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_1_gpr_S_walk :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s.(mem) pa 1
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0) : mword 8)) s'.(mdev)).
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
      (exec_vmem_write_1_gpr_S_walk rs1 offset _ region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walk.

(* helper: write_bytes_1 *)
Local Lemma write_bytes_1 (mm : _) (pa : Arch.pa) (v : bv 8) :
    write_bytes mm pa 1 v = <[pa := nth_byte v 0]> mm.
  Proof. unfold write_bytes. change (N.to_nat 1) with 1%nat. cbn [seq foldr]. rewrite pa_add_0. reflexivity. Qed.

Section WpSmodeStore.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

(* helper (ctx): ram_bounds_of_bytes *)
  Local Lemma ram_bounds_of_bytes (pa : mword 64) (dqm : dfrac) (v : bv 64) :
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dqm} nth_byte v j) -∗
    ⌜ addr_is_ram pa /\ addr_is_ram (pa_add pa 7)
      /\ (ram_base <= uint pa)%Z /\ (uint pa + 8 <= ram_base + ram_size)%Z ⌝.
  Proof.
    iIntros "Hbytes".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    iPureIntro.
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hr0 as [H _]; exact H).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hr0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hr7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    split; [exact Hr0 | split; [exact Hr7 | split; [exact Hlo | exact Hfit]]].
  Qed.

(* helper (ctx): mem_update_1 *)
  Local Lemma mem_update_1 (mm : _) (pa : Arch.pa) (vold vnew : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ pa ↦ₘ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 1 vnew) ∗ pa ↦ₘ (nth_byte vnew 0).
  Proof. rewrite write_bytes_1. apply mem_update. Qed.

(* helper (ctx): upd_window_bw *)
  Local Lemma upd_window_bw {k : N} (mm : _) (pa : Arch.pa) (vnew vold : bv k)
      (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add pa j := nth_byte vnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof.
    iInduction l as [|x xs IH] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (mem_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x) with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

(* helper (ctx): upd_window_4 *)
  Local Lemma upd_window_4 (mm : _) (pa : Arch.pa) (vnew vold : bv 32) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 4 vnew)
      ∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof. unfold write_bytes. change (N.to_nat 4) with 4%nat. apply upd_window_bw. Qed.

  Lemma wp_csd_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: X-bit + RAM coverage (geometry derived from instr_bytes) *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_csd_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iApply (wp_csd_s root_ppn E Φ pc rs2 rs1 imm (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_csd_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csd_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_gpr_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csw_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_csw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (ea ↦₄ vold)%I with "[Hbytes]" as "Hbw4".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpal4. }
    iApply (wp_csw_s root_ppn E Φ pc rs2 rs1 imm (svpn_of ea) m vold
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbw4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile Hbw").
  Qed.

  Lemma wp_csw_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₄ (RiscvExtras.trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csw_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sb_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 8)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)) in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) in
    ↑minstretN ⊆ E ->
    (* the superpage-identity geometry facts below (svpn := svpn_of a8) are
       derived internally at this leaf from [addr_is_ram a8]; no caller obligation. *)
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    (pa ↦ₘ vold) -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      (pa ↦ₘ (nth_byte storeval 0)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN.
    set (svpn := svpn_of a8).
    iIntros "Hsm Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbyte Hcont".
    (* [push to leaf] derive the svpn geometry facts here from [addr_is_ram a8]. *)
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa0.
    { iDestruct (mem_ram with "Hbyte") as %Hr0. iPureIntro. exact Hr0. }
    assert (Hpa_a8 : pa = a8)
      by (unfold pa; rewrite Z.mul_0_l avi0; apply zero_extend'_id).
    assert (Hrama8 : addr_is_ram a8) by (rewrite <- Hpa_a8; exact Hrampa0).
    pose proof (RiscvExtras.ram_canonical a8 Hrama8) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (WpSmodeGpr.ram_ident root_ppn a8 Hrama8) as Hident.
    pose proof (RiscvExtras.ram_mask a8 Hrama8) as Hmask.
    pose proof (RiscvExtras.ram_svpn2 a8 Hrama8) as Hvpn2.
    pose proof (RiscvExtras.ram_mvpn a8 Hrama8) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn a8 Hrama8) as Hmppn.
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 1) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 1))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hms1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (mem_ram with "Hbyte") as %Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 1 <= ram_base + ram_size)%Z)
      by (destruct Hrampa as [_ Hh]; unfold ram_base, ram_size in *; lia).
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 1
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    (* the walk's PTE bytes + their RAM-ness (used by the data-miss branch) *)
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrama8
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrama8 Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 1 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 1 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)
                   ltac:(rewrite Lva; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                   with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
      iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 1 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 1 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)
                   ltac:(rewrite Lva; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                   with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
      iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrama8 Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sd_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: X-bit + RAM coverage (geometry derived from instr_bytes) *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    pose proof Hrange_ld as Hrange_st.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sd_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iDestruct (ram_bounds_of_bytes pa (DfracOwn 1) vold with "Hbytes") as %(Hr0 & _ & Hlo & Hfit).
    iApply (wp_sd_s root_ppn E Φ pc rs2 rs1 imm (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_sd_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sd_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 storeval) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (ea ↦₄ vold)%I with "[Hbytes]" as "Hbw4".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpal4. }
    iApply (wp_sw_s root_ppn E Φ pc rs2 rs1 imm (svpn_of ea) m vold
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbw4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sw_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

End WpSmodeStore.
