(* WpSmodeUart.v -- S-mode, instruction-level UART load/store WPs.

   WpUart.v proved the device MMIO transaction leaves at the M-mode
   PHYSICAL level (checked_mem_{read,write}_dev_1, Machine privilege).
   This file lifts them to the S-MODE INSTRUCTION level: an S-mode LOAD
   or STORE to a UART register runs through the full Sv39 translation of
   the kernel's UART mapping (a 4KB identity page, root[0] -> l1[128] ->
   l0[0] leaf, R|W|A|D -- the mapping kvmmake installs), whose translated
   physical address lands in the device window and is serviced by the
   device fabric.

   The walk itself reuses CommonWalk's privilege/access-generic 3-level
   walk (instantiated at Supervisor + Load/Store Data); only the leaf
   permission check and the device-routed checked_mem differ from the
   RAM path.  The device checked_mem leaves below are WpUart's M-mode
   ones with the PMP check swapped for the S-mode TOR grant. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodeCore CommonWalk.
Require Import WpGpr.
Require Import WpLoad WpMmodeLeafBase.
Require Import WpSmodeGpr.
Require Import WpUart.
Require Import TrampPt TrampTlb.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  S-mode, width-1 device checked_mem leaves.                          *)
(*     = WpUart's M-mode dev leaves, PMP check swapped to the S-mode       *)
(*     TOR grant (R bit for loads, W bit for stores).                      *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_dev_1_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (b : bv 8) (d' : dev_state) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_read s.(mdev) pa 1 = Some (b, d') ->
  exec (checked_mem_read (Load Data) pbmt Supervisor (Physaddr pa) 1 false false false false)
       s = Some (Ok (b, default_meta), MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hrd.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_load_data pa 1 s HA Hord Hrange HR)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_dev_load_1 pa pbmt region s Hmatch Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr pa) 1) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_dev_1 pa b d' s Hdev Hrd)).
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_dev_1_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (data : bv 8) (d' : dev_state) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_write s.(mdev) pa 1 data = Some d' ->
  exec (checked_mem_write (Physaddr pa) 1 data (Store Data) pbmt Supervisor tt false false false)
       s = Some (Ok true, MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store pa 1 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_dev_store_1 pa pbmt region s Hmatch Hwrite)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr pa) 1) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags _ _ _) s = Some (Write_plain, s))).
  2:{ unfold write_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_dev_1 pa data d' s Hdev Hwr)).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §2  The mem_read / mem_write_value wrappers around the device leaves    *)
(*     (Supervisor, MPRV=0), width 1.  A device read ADVANCES the device   *)
(*     (RHR pops the rx FIFO), so the post-state carries [d'].             *)
(* ===================================================================== *)

Lemma exec_mem_read_dev_1_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (b : bv 8) (d' : dev_state) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_read s.(mdev) pa 1 = Some (b, d') ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (Load Data) pbmt (Physaddr pa) 1 false false false)
       s = Some (Ok b, MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hrd Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_S m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 1 _ _ _ _) s
                   = Some (Ok (b, default_meta), MState s.(sregs) s.(mem) d'))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 1 _ _ _ _) s
                       = Some (Ok (b, default_meta), MState s.(sregs) s.(mem) d'))).
      2:{ cbn match. apply exec_checked_mem_read_dev_1_S with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_mem_write_value_dev_1_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (data : bv 8) (d' : dev_state) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_write s.(mdev) pa 1 data = Some d' ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_write_value (Physaddr pa) 1 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_dev_1_S pbmt pa region data d' s HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §3  The UART data-address translation: the full 3-level Sv39 walk over  *)
(*     the kernel's UART 4KB identity mapping (root[0] -> l1[128] ->        *)
(*     l0[0] leaf, R|W|A|D).  Reuses CommonWalk's privilege/access-generic  *)
(*     [exec_translate_walk_user] at (Store/Load Data, Supervisor); the      *)
(*     translateAddr wrapper is the Supervisor-data mirror of UmodeWalk's    *)
(*     [exec_translateAddr_fetch_walk_u].  The three PTE reads are taken as  *)
(*     [read_pte] exec facts (dischargeable from owned PT-page bytes via     *)
(*     [exec_read_pte_S]); the walk FILLS the TLB (state change).           *)
(* ===================================================================== *)

Lemma exec_translateAddr_store_walk_u_S
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (va satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
  (forall (mxr do_sum : bool) s0, exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Store Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Store Data)) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va),
                PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL Hmprv Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store_S (register_lookup mstatus s.(sregs)) s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_store s)).
  unfold Defs.bind0.
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
  rewrite execR_bind. rewrite execR_returnR. cbn match.
  assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
    by (cbn; apply exec_returnm).
  rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
  assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
  { unfold get_satp.
    assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    change (Z.eqb 39 32) with false. cbn match.
    unfold autocast_m.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
  assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                        "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
  { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
  rewrite Hcanon. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  match goal with |- context[translate 39 _ _ _ _ _ ?mxrx ?dsx _] =>
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (Store Data) Supervisor mxrx dsx
                  H2i H2nl H1i H1nl H0i H0nl (Hchk0 mxrx dsx) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

Lemma exec_translateAddr_load_walk_u_S
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (va satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
  (forall (mxr do_sum : bool) s0, exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Load Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Load Data)) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va),
                PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL Hmprv Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load_S (register_lookup mstatus s.(sregs)) s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_load s)).
  unfold Defs.bind0.
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
  rewrite execR_bind. rewrite execR_returnR. cbn match.
  assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
    by (cbn; apply exec_returnm).
  rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
  assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
  { unfold get_satp.
    assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    change (Z.eqb 39 32) with false. cbn match.
    unfold autocast_m.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
  assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                        "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
  { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
  rewrite Hcanon. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  match goal with |- context[translate 39 _ _ _ _ _ ?mxrx ?dsx _] =>
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (Load Data) Supervisor mxrx dsx
                  H2i H2nl H1i H1nl H0i H0nl (Hchk0 mxrx dsx) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


(* ===================================================================== *)
(* §3b  P_uart and the fetch/data DISCRIMINATION.  The generalized fetch    *)
(*     engine ([wp_instr_s_config_tlbinv_gen]) admits the UART leaf in the   *)
(*     TLB via [P_uart] and, for every RAM address, needs the UART entry to  *)
(*     FAIL [match_TLB_Entry] (so a RAM fetch/data access at a colliding     *)
(*     hash re-walks rather than mis-hitting the UART leaf).  This holds     *)
(*     because the UART entry's vpn tag is [sign_extend' 45 0x10000] whereas *)
(*     every RAM svpn sits in the 0x80000 gigapage.  This is the concrete    *)
(*     proof the [tlb_consistent] generalization admits the UART entry.      *)
(*     (The four bitvector/TLB helpers are local copies of UptInv's; they    *)
(*     are generic and should eventually move to CommonWalk.)                *)
(* ===================================================================== *)

Lemma u_eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply bool_decide_eq_true_2. reflexivity. Qed.

Lemma u_and_ones45 (x : mword 45) :
  and_vec x (not_vec (zero_extend' (57 - 12) (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  change (Z.sub 57 12) with 45.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 45) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

Lemma u_and_ones27 (x : mword 27) :
  and_vec x (not_vec (zero_extend' 27 (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 27) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

Lemma u_sext45_inj (x y : mword 27) :
  sign_extend' (57 - 12) x = sign_extend' (57 - 12) y -> x = y.
Proof.
  intros H.
  apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H; [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

(* the level-0 walk entry matches exactly its own vpn (asid 0, empty mask) *)
Lemma u_walk_entry_match (vpn vpn' : mword 27) (pte2 pte1 pte0 : mword 64) :
  match_TLB_Entry (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0)) (mword_of_int 0)
    (sign_extend' (57 - 12) vpn')
  = eq_vec (sign_extend' (57 - 12) vpn) (sign_extend' (57 - 12) vpn').
Proof.
  unfold match_TLB_Entry, u_walk_entry.
  cbn [TLB_Entry_global TLB_Entry_asid TLB_Entry_vpn TLB_Entry_levelMask].
  rewrite u_and_ones45. rewrite u_and_ones27. rewrite u_eq_vec_refl.
  rewrite orb_true_r. reflexivity.
Qed.

Definition uart_vpn : mword 27 := mword_of_int 0x10000.

Definition P_uart (root : mword 44) (pte2 pte1 pte0 : mword 64) : TLB_Entry -> Prop :=
  fun e => e = pw_tlb_entry root (mword_of_int 0) \/
           e = u_walk_entry uart_vpn pte2 pte1 pte0 (mword_of_int 0).

(* the UART entry never matches a RAM address's svpn *)
Lemma uart_entry_nomatch_ram (pte2 pte1 pte0 : mword 64) (a : mword 64) :
  addr_is_ram a ->
  match_TLB_Entry (u_walk_entry uart_vpn pte2 pte1 pte0 (mword_of_int 0)) (mword_of_int 0)
    (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros Hram.
  rewrite u_walk_entry_match.
  destruct (eq_vec _ _) eqn:He; [exfalso | reflexivity].
  apply eq_vec_true_iff in He. apply u_sext45_inj in He.
  pose proof (ram_mask a Hram) as Hm.
  rewrite <- He in Hm.
  apply (f_equal bv_unsigned) in Hm.
  vm_compute in Hm. discriminate.
Qed.

(* the two obligations the generic engine takes: superpage is legal, and    *)
(* every legal entry is either the superpage (a hit) or fails to match a     *)
(* RAM fetch/data vpn (a re-walk).                                           *)
Lemma P_uart_super (root : mword 44) (pte2 pte1 pte0 : mword 64) :
  P_uart root pte2 pte1 pte0 (pw_tlb_entry root (mword_of_int 0)).
Proof. left; reflexivity. Qed.

Lemma P_uart_disc (root : mword 44) (pte2 pte1 pte0 : mword 64) :
  forall a e, addr_is_ram a -> P_uart root pte2 pte1 pte0 e ->
    e = pw_tlb_entry root (mword_of_int 0) \/
    match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros a e Hram [-> | ->].
  - left; reflexivity.
  - right; apply uart_entry_nomatch_ram; exact Hram.
Qed.

(* ===================================================================== *)
(* §3c  tlb4k-entry variant of P_uart.  The UART data translate is built   *)
(*     by INSTANTIATING TrampTlb's generic 4KB three-way translate         *)
(*     ([exec_translateAddr_tramp], hit/nonmatch/walk, generic in the      *)
(*     access), which installs a [tlb4k_entry] rather than CommonWalk's    *)
(*     [u_walk_entry].  So the invariant's legal-entry set [P_uart4k] is    *)
(*     phrased on [tlb4k_entry], and its discrimination re-uses TrampTlb's  *)
(*     match facts.  (The §3b u_walk_entry copy is retained but superseded  *)
(*     by this path for the actual WP.)                                     *)
(* ===================================================================== *)

Definition uart_tlb_ent (lppn : mword 44) (pte ptea : mword 64) : TLB_Entry :=
  tlb4k_entry (mword_of_int 0) uart_vpn lppn pte ptea.

Definition P_uart4k (root lppn : mword 44) (pte ptea : mword 64) : TLB_Entry -> Prop :=
  fun e => e = pw_tlb_entry root (mword_of_int 0) \/ e = uart_tlb_ent lppn pte ptea.

Lemma tlb4k_nomatch_ram (lppn : mword 44) (pte ptea : mword 64) (a : mword 64) :
  addr_is_ram a ->
  match_TLB_Entry (uart_tlb_ent lppn pte ptea) (mword_of_int 0)
    (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros Hram.
  unfold uart_tlb_ent, match_TLB_Entry, tlb4k_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  apply andb_false_intro2.
  match goal with |- context[and_vec ?x ?m] =>
    rewrite (and45_ones x m ltac:(vm_compute; reflexivity)) end.
  destruct (eq_vec _ _) eqn:He; [exfalso | reflexivity].
  apply eq_vec_true_iff in He. apply u_sext45_inj in He.
  pose proof (ram_mask a Hram) as Hm. rewrite <- He in Hm.
  apply (f_equal bv_unsigned) in Hm. vm_compute in Hm. discriminate.
Qed.

Lemma P_uart4k_super (root lppn : mword 44) (pte ptea : mword 64) :
  P_uart4k root lppn pte ptea (pw_tlb_entry root (mword_of_int 0)).
Proof. left; reflexivity. Qed.

Lemma P_uart4k_disc (root lppn : mword 44) (pte ptea : mword 64) :
  forall a e, addr_is_ram a -> P_uart4k root lppn pte ptea e ->
    e = pw_tlb_entry root (mword_of_int 0) \/
    match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros a e Hram [-> | ->].
  - left; reflexivity.
  - right; apply tlb4k_nomatch_ram; exact Hram.
Qed.

(* the RAM superpage entry never matches the UART vpn (0x80000 tag vs the   *)
(* 0x10000 vpn, whose bit is masked out by the gigapage levelMask 0x3FFFF): *)
(* so a superpage resident at the UART's hash slot triggers a re-walk.      *)
Lemma pw_super_nomatch_uart (root : mword 44) :
  match_TLB_Entry (pw_tlb_entry root (mword_of_int 0)) (mword_of_int 0 : mword 16)
    (sign_extend' (57 - 12) uart_vpn) = false.
Proof.
  unfold match_TLB_Entry, pw_tlb_entry, uart_vpn.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  vm_compute. reflexivity.
Qed.

(* convert the invariant's [tlb_consistent (P_uart4k ...)] at the UART hash  *)
(* slot into exactly the trichotomy [exec_translateAddr_tramp] consumes:     *)
(* empty | resident-but-nonmatching (superpage collision → re-walk) |        *)
(* resident UART leaf (hit).  [pte]/[ptea] of the UART leaf are pinned to     *)
(* what TrampTlb's walk installs ([mk_pte lppn lflags] at [a0]).             *)
Lemma uart_slot_disj (root lppn : mword 44) (lflags : Z) (a0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_consistent (P_uart4k root lppn (mk_pte lppn lflags) a0) tlbvec ->
  (vec_access_dec tlbvec (tlb_hash (__id 39) uart_vpn) = None \/
   (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) uart_vpn) = Some ent /\
                match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) uart_vpn) = false) \/
   (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) uart_vpn)
                 = Some (tlb4k_entry (mword_of_int 0) uart_vpn lppn (mk_pte lppn lflags) ptea))).
Proof.
  intros Hcons.
  destruct (Hcons (tlb_hash (__id 39) uart_vpn) (tlb_hash_range uart_vpn)) as [Hn | (e & He & HPe)].
  - left; exact Hn.
  - destruct HPe as [-> | ->].
    + right; left. exists (pw_tlb_entry root (mword_of_int 0)).
      split; [ exact He | apply pw_super_nomatch_uart ].
    + right; right. exists a0. unfold uart_tlb_ent in He. exact He.
Qed.

(* ===================================================================== *)
(* §4  S-mode, width-1 device STORE towers (translation WALKS, filling     *)
(*     the TLB, then the device write ADVANCES the device).  Clones of      *)
(*     WpMemsetS's width-1 RAM store walk towers with the RAM leaf swapped  *)
(*     for the device leaf; the untilMT loop machinery is reused verbatim.  *)
(* ===================================================================== *)

(* two tiny width-1 helpers (local copies of WpMemsetS's, which live inside
   an Iris section) *)
Lemma exec_split_misaligned_aligned_1 (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 1 = true ->
  exec (split_misaligned vaddr 1) s = Some ((1, 1), s).
Proof. intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm. Qed.

Lemma exec_mem_write_ea_1 (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) 1 false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

  Section SWS1walkDev.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable d' : dev_state.
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
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data = Some d'.

  Lemma exec_vmem_write_addr_1_S_walk_dev :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) s.(mem) d').
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
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) s.(mem) d'))
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
                             = Some (inr true, MState s'.(sregs) s.(mem) d'))
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
            (exec_mem_write_value_dev_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data d'
               (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr eq_refl Hmprv Hcp)).
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
  End SWS1walkDev.

  Section VWgS1walkDev.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable d' : dev_state.
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
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data = Some d'.

  Lemma exec_vmem_write_1_gpr_S_walk_dev :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) s.(mem) d').
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
    rewrite (exec_vmem_write_addr_1_S_walk_dev a8 data d' region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr).
    reflexivity.
  Qed.
  End VWgS1walkDev.

  Section ExecStoreGS1walkDev.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Variable d' : dev_state.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Let data_byte : mword 8 := autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0).
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
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = true.
  Hypothesis Hwr : dev_write s'.(mdev) pa 1 data_byte = Some d'.

  Lemma exec_execute_STORE_1_gpr_S_walk_dev :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) s.(mem) d').
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
      (exec_vmem_write_1_gpr_S_walk_dev rs1 offset data_byte d' region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev Hwr)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walkDev.

(* ===================================================================== *)
(* §5  S-mode, width-1 device LOAD towers (translation WALKS + device      *)
(*     read ADVANCES the device).  Width-1 device adaptation of            *)
(*     WpSmodeGpr's width-8 RWSwalk / RWgSwalk / ExecLoadGSwalk (the RAM    *)
(*     8-byte load walk towers); the untilMT read loop is width-1 and the  *)
(*     RAM leaf is swapped for the device leaf.  LB (sign-extended); an     *)
(*     LBU (unsigned) twin is `extend_value true`.                          *)
(* ===================================================================== *)
Section RWS1walkDev.
Variable a : mword 64.
Variable v : bv 8.
Variable d' : dev_state.
Variable region : PMA_Region.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
Let data2 : mword (1*1*8) :=
  update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) v.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hdrd : dev_read s'.(mdev) pa 1 = Some (v, d').

Lemma exec_vmem_read_addr_1_S_walk_dev :
  exec (vmem_read_addr (Virtaddr a) 1 (Load Data) false false false) s
    = Some (Ok data2, MState s'.(sregs) s'.(mem) d').
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (1 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), MState s'.(sregs) s'.(mem) d'))
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
        assert (Hmrm : execR mrm s' = Some (inr data2, MState s'.(sregs) s'.(mem) d'))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_dev_1_S PBMT_PMA pa region v d' (register_lookup mstatus s'.(sregs)) s'
             HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hdrd eq_refl Hmprv' Hcp')).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt (MState s'.(sregs) s'.(mem) d'))).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End RWS1walkDev.

Section RWgS1walkDev.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 8.
Variable d' : dev_state.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
Let data2 : mword (1*1*8) :=
  update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hdrd : dev_read s'.(mdev) pa 1 = Some (v, d').

Lemma exec_vmem_read_1_gpr_S_walk_dev :
  exec (vmem_read (Regidx rs1) offset 1 (Load Data) false false false) s = Some (Ok data2, MState s'.(sregs) s'.(mem) d').
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 1) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 1 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_1_S_walk_dev a8 v d' region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hdrd).
  reflexivity.
Qed.
End RWgS1walkDev.

Section ExecLoadGS1walkDev.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 8.
Variable d' : dev_state.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
Let data2 : mword (1*1*8) :=
  update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 1)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 1) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hdrd : dev_read s'.(mdev) pa 1 = Some (v, d').

Lemma exec_execute_LOAD_1_gpr_S_walk_dev :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 1))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) s'.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 1)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 1).
  unfold execute_LOAD.
  replace (1 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_1_gpr_S_walk_dev rs1 offset v d' region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hdrd)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) (MState s'.(sregs) s'.(mem) d')
               = Some (tt, set_reg (MState s'.(sregs) s'.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) (MState s'.(sregs) s'.(mem) d')).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGS1walkDev.

Section UartWpBytes.
Context `{!riscvGS Σ}.
Existing Instance riscv_memGS.

Definition uart_map (root p1 p0 lppn : mword 44) (lflags : Z) (dq : dfrac) : iProp Σ :=
  (pte_addr_at root (subrange_vec_dec uart_vpn 26 18) ↦₈{ dq } mk_pte p1 PTE_PTR ∗
   pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9) ↦₈{ dq } mk_pte p0 PTE_PTR ∗
   pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0) ↦₈{ dq } mk_pte lppn lflags)%I.

Lemma uart_map_bytes (root p1 p0 lppn : mword 44) (lflags : Z) dq (σ : mstate) :
  gen_heap_interp σ.(mem) -∗ uart_map root p1 p0 lppn lflags dq -∗
  ⌜ (forall j:nat, (N.of_nat j < 8)%N ->
       σ.(mem) !! (pa_add (pte_addr_at root (subrange_vec_dec uart_vpn 26 18)) j) = Some (nth_byte (mk_pte p1 PTE_PTR) j))
  /\ (forall j:nat, (N.of_nat j < 8)%N ->
       σ.(mem) !! (pa_add (pte_addr_at p1 (subrange_vec_dec uart_vpn 17 9)) j) = Some (nth_byte (mk_pte p0 PTE_PTR) j))
  /\ (forall j:nat, (N.of_nat j < 8)%N ->
       σ.(mem) !! (pa_add (pte_addr_at p0 (subrange_vec_dec uart_vpn 8 0)) j) = Some (nth_byte (mk_pte lppn lflags) j)) ⌝.
Proof.
  iIntros "Hm (H2 & H1 & H0)".
  iDestruct (word_pointsto_bytes with "H2") as "H2".
  iDestruct (word_pointsto_bytes with "H1") as "H1".
  iDestruct (word_pointsto_bytes with "H0") as "H0".
  iSplit; [| iSplit].
  - iIntros (j Hj). iDestruct (big_sepL_lookup _ _ j j with "H2") as "Hbj".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iApply (mem_valid with "Hm Hbj").
  - iIntros (j Hj). iDestruct (big_sepL_lookup _ _ j j with "H1") as "Hbj".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iApply (mem_valid with "Hm Hbj").
  - iIntros (j Hj). iDestruct (big_sepL_lookup _ _ j j with "H0") as "Hbj".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iApply (mem_valid with "Hm Hbj").
Qed.

End UartWpBytes.
