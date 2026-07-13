(* S-mode Load leaf lemmas (smode_config/Supervisor, decode family Load).
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

(* helper: exec_pmaCheck_ram_load_4 *)
Local Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (None, s).
  Proof.
    intros Hmatch Halign Hread.
    unfold pmaCheck.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
    rewrite Hmatch.
    destruct region as [rbase rsize rattr rdtree].
    cbn [PMA_Region_attributes] in Hread |- *.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
    cbn match beta.
    change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
            (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
      with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
    rewrite Hread. cbn match.
    apply exec_returnM.
  Qed.

(* helper: exec_split_misaligned_aligned_4 *)
Local Lemma exec_split_misaligned_aligned_4 (vaddr : virtaddr) s :
    is_aligned_vaddr vaddr 4 = true ->
    exec (split_misaligned vaddr 4) s = Some ((1, 4), s).
  Proof.
    intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
  Qed.

(* helper: exec_checked_mem_read_ram_load_4_S *)
Local Lemma exec_checked_mem_read_ram_load_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 32) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 4)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Load Data) pbmt Supervisor (Physaddr addr) 4 false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
    unfold checked_mem_read.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_load_data addr 4 s HA Hord Hrange HR)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load_4 addr pbmt region s Hmatch Halign Hread)).
        cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
    2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
    2:{ unfold read_kind_of_flags. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
    apply exec_returnM.
  Qed.

(* helper: exec_mem_read_load_4_S *)
Local Lemma exec_mem_read_load_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 32) (m : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 4)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_read (Load Data) pbmt (Physaddr addr) 4 false false false)
         s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    rewrite Hms.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_S m s Hmprv)).
    unfold mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_load_4_S with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

(* SEC:section:RWS4 *)
  Section RWS4.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_4_S :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Ok data2, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (4 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?mrm ?post) s = _ =>
          assert (Hmrm : execR mrm s = Some (inr data2, s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_load_4_S PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
               HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hcp)).
          cbn match.
          rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite autocast_id. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
        cbn. apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. rewrite autocast_id. reflexivity.
  Qed.
  End RWS4.

(* SEC:section:RWgS4 *)
  Section RWgS4.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_4_gpr_S :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok data2, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_4_S a8 v region s Halign Hcp Hmprv Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.
  End RWgS4.

(* SEC:section:ExecLoadGS4 *)
  Section ExecLoadGS4.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_gpr_S :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 4).
    unfold execute_LOAD.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_read_4_gpr_S rs1 offset v region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
                 = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.
  End ExecLoadGS4.

(* SEC:section:RWS4walk *)
  Section RWS4walk.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_4_S_walk :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Ok data2, s').
  Proof.
    assert (Hbytes' : forall j : nat, (N.of_nat j < 4)%N ->
              s'.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytes.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (4 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s'))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?mrm ?post) s' = _ =>
          assert (Hmrm : execR mrm s' = Some (inr data2, s'))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_load_4_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
               HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes' eq_refl Hmprv' Hcp')).
          cbn match.
          rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s')).
          rewrite autocast_id. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
        cbn. apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. rewrite autocast_id. reflexivity.
  Qed.
  End RWS4walk.

(* SEC:section:RWgS4walk *)
  Section RWgS4walk.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_4_gpr_S_walk :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok data2, s').
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_4_S_walk a8 v region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.
  End RWgS4walk.

(* SEC:section:ExecLoadGS4walk *)
  Section ExecLoadGS4walk.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_gpr_S_walk :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 4).
    unfold execute_LOAD.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_read_4_gpr_S_walk rs1 offset v region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s'
                 = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s').
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.
  End ExecLoadGS4walk.

(* helper: data2_id_4 *)
Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
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

Section WpSmodeLoad.
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

  Lemma wp_cld_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    (* load PMP: TOR entry 0 covers pa with R *)
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
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
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
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
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
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 8)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    (* the data-address translate through the kernel PT (KptPt.v): packaged
       three-way -- a HIT at [a8]'s own 4KB leaf entry, or (empty slot /
       foreign resident entry) a 3-level WALK that fills the slot with
       [kpt_tlb_ent root_ppn (svpn_of a8)]. *)
    destruct (exec_translateAddr_kpt_ram (Load Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_load s_pc)
                kpt_ram_check_load
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
      pose proof (within_htif_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 2).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
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
      pose proof (within_htif_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S_walk rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 2).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  Lemma wp_cld_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iApply (wp_cld_s root_ppn E Φ pc rd rs1 imm (svpn_of a8) m v
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_cld_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cld_s_ram root_ppn E Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_cldsp_gpr_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ pc uimm rd m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_clw_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (v : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    (* load PMP: TOR entry 0 covers pa with R *)
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
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    pa ↦₄{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
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
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
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
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
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
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 4)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v) = sign_extend' 64 v).
    { unfold extend_value. rewrite data2_id_4. reflexivity. }
    (* the data-address translate through the kernel PT (KptPt.v): packaged
       three-way -- a HIT at [a8]'s own 4KB leaf entry, or (empty slot /
       foreign resident entry) a 3-level WALK that fills the slot with
       [kpt_tlb_ent root_ppn (svpn_of a8)]. *)
    destruct (exec_translateAddr_kpt_ram (Load Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_load s_pc)
                kpt_ram_check_load
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
      pose proof (within_htif_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
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
      pose proof (within_htif_false pa 4 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sign_extend' 64 v)))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_4_gpr_S_walk rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64 v)) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
               = add_vec_int pc 2).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  Lemma wp_clw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (ea ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw4".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpal4. }
    iApply (wp_clw_s root_ppn E Φ pc rd rs1 imm (svpn_of ea) m v
              mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbw4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile Hbw").
  Qed.

  Lemma wp_clw_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ea ↦₄{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      ea ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_clw_s_ram root_ppn E Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_ld_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    (* load PMP: TOR entry 0 covers pa with R *)
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
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
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
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
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
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 8)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    (* the data-address translate through the kernel PT (KptPt.v): packaged
       three-way -- a HIT at [a8]'s own 4KB leaf entry, or (empty slot /
       foreign resident entry) a 3-level WALK that fills the slot with
       [kpt_tlb_ent root_ppn (svpn_of a8)]. *)
    destruct (exec_translateAddr_kpt_ram (Load Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_load s_pc)
                kpt_ram_check_load
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
      pose proof (within_htif_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 4).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
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
      pose proof (within_htif_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S_walk rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hbytesf_pc)). }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 4).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  Lemma wp_ld_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
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
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iDestruct (ram_bounds_of_bytes pa dqm v with "Hbytes") as %(Hr0 & _ & Hlo & Hfit).
    iApply (wp_ld_s root_ppn E Φ pc rd rs1 imm (svpn_of a8) m v
              mstatus0 mie_v mdv0 menvcfg0
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_ld_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_ld_s_ram root_ppn E Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

End WpSmodeLoad.
