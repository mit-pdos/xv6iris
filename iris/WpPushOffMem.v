(* WpPushOffMem.v -- 4-byte data load/store S-mode instruction lemmas
   (c.lw / c.sw through a general base register), for push_off's per-cpu
   [noff]/[intena] accesses.  Built by cloning wp_cldsp_gpr_s / wp_csdsp_gpr_s
   (WpSmodeGpr.v, 8-byte, sp-relative) with the base register generalized and
   the access width changed 8 -> 4. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpLoad.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import WpSmodeGpr.
Local Open Scope Z_scope.
Import Defs.

Section WpPushOffMem.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ===================================================================== *)
  (* Width-4 model-level exec facts, cloned from the width-8 stack in       *)
  (* WpSmodeGpr.v and the width-1 stack in WpMemsetS.v with the width        *)
  (* literal changed to 4 (store value: low 32 bits of rs2; load value:      *)
  (* 32 bits sign-extended to 64).                                           *)
  (* ===================================================================== *)


  (* ---- width-4 store primitives ---- *)
  Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
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

  Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
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

  Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
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





  (* ---- width-4 vmem_write_addr (HIT: state-preserving) ---- *)
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

  End SWS4.

  (* ---- width-4 register-generic vmem_write (HIT) ---- *)
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

  End VWgS4.

  (* ---- width-4 register-generic STORE execute (HIT) ---- *)
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

  End ExecStoreGS4.

  (* ---- width-4 vmem_write_addr WALK (fills the TLB) ---- *)
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

  End SWS4walk.

  (* ---- width-4 register-generic vmem_write WALK ---- *)
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

  End VWgS4walk.

  (* ---- width-4 register-generic STORE execute WALK ---- *)
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

  End ExecStoreGS4walk.

  (* ---- width-4 load building blocks ---- *)


  (* ---- width-4 vmem_read_addr (HIT) ---- *)
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

  End RWS4.

  (* ---- width-4 register-generic vmem_read (HIT) ---- *)
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

  End RWgS4.

  (* ---- width-4 register-generic LOAD execute (HIT) ---- *)
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

  End ExecLoadGS4.

  (* ---- width-4 vmem_read_addr WALK ---- *)
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

  End RWS4walk.

  (* ---- width-4 register-generic vmem_read WALK ---- *)
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

  End RWgS4walk.

  (* ---- width-4 register-generic LOAD execute WALK ---- *)
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

  End ExecLoadGS4walk.

  (* ---- width-4 helper facts for the WP lemmas ---- *)



  (* ------------------------------------------------------------------- *)
  (* c.sw rs2, imm(rs1) -- 4-byte store through a GENERAL base register,   *)
  (* superpage-identity data address (a8 = ea = rs1 + sext imm).  Cloned    *)
  (* from wp_csdsp_gpr_s with base generalized and width 8 -> 4.            *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* c.lw rd, imm(rs1) -- 4-byte signed load (sign-extend 32 -> 64)        *)
  (* through a GENERAL base register.  Cloned from wp_cldsp_gpr_s.          *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------ *)
  (* [_ram] variants: the whole Sv39 super-page-identity geometry is     *)
  (* DERIVED internally from the owning [ea ↦₄ v] (which carries          *)
  (* [addr_is_ram] + 4-byte alignment) via the [ram_*] family, so the    *)
  (* caller supplies NO geometry -- it just hands over the points-to.    *)
  (* This lets [wp_push_off] and the VCgen keep their per-instruction    *)
  (* obligations to a single memory fact.                                *)
  (* ------------------------------------------------------------------ *)

  (* [wp_csw_s], same treatment.  The stored word is [trunc32 rs2]. *)

  (* ---- base (non-compressed) SW: sw rs2, imm(rs1) -- 4-byte word store.
     Mechanical [false]/[+4] clone of wp_csw_s / wp_csw_s_ram (used by wakeup's
     [sw s5,24(s1)] state write). ---- *)


End WpPushOffMem.
