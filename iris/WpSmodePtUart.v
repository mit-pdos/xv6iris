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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RiscvExtras.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import WpUart WpSmodeUart.
Require Import MemAccessGen.
Require Import WpSmodeGpr.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* state-generic width-1 device STORE towers (WpSmodeUart clones with the *)
(* translate output state fully abstract -- no [s'.(mem) = s.(mem)])      *)
(* ===================================================================== *)
  Section SWS1walkDevPt.
  Variable a : mword 64.
  Variable data : mword (8*1).
  Variable d' : dev_state.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Store Data)) s
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
    assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
    { rewrite Hcps. apply exec_effectivePrivilege_store_S. exact Hmprvs. }
    assert (Hea : exec (mem_write_ea (Physaddr pa) 1 (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok tt, s')).
    { apply (exec_mem_write_ea_g 1 pa (Store Data) PBMT_PMA Supervisor s').
      - rewrite Hcp. apply exec_effectivePrivilege_store_S. exact Hmprv.
      - unfold check_pma_with_pmp_priority.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmaCheck_dev_store_1 pa PBMT_PMA region s' Hmatch Hwrite)).
        cbn match. apply exec_returnM.
      - exact (exec_pmpCheck_supervisor_grant_store pa 1 s' HA Hord Hrange HW). }
    assert (Hwv : exec (mem_write_value (Physaddr pa) 1
                          (autocast (T := mword) (subrange_vec_dec data (8*1-1) 0))
                          (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok true, MState s'.(sregs) s'.(mem) d')).
    { rewrite (subrange_full_gen_cast (8 * 1) data ltac:(lia)).
      exact (exec_mem_write_value_dev_1_S PBMT_PMA pa region data d'
               (register_lookup mstatus s'.(sregs)) s'
               HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr eq_refl Hmprv Hcp). }
    exact (exec_vmem_write_addr_aligned_store 1 a pa data Supervisor md s s'
             (MState s'.(sregs) s'.(mem) d')
             ltac:(left; reflexivity) Halign Heff Htm Htr Hea Hwv).
  Qed.
  End SWS1walkDevPt.

  Section VWgS1walkDevPt.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : mword (8*1).
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
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
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
    rewrite (exec_vmem_write_addr_1_S_walk_dev_pt a8 data d' region s s' Halign Hcp' Hmprv'
               md Hcps Hmprvs Htm Htr HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr).
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
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Store Data)) s
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
      (exec_vmem_write_1_gpr_S_walk_dev_pt rs1 offset data_byte d' region s s' Htea Halign
         md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walkDevPt.

Section WpSmodePtUart.
Context `{!riscvGS Σ, !xv6G Σ}.
Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
Existing Instance riscv_memGS.



End WpSmodePtUart.
