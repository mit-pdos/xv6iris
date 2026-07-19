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
Require Import DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr.
Require Import WpLoad WpMmodeLeafBase.
Require Import WpSmodeGpr.
Require Import WpUart.
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
(* §3  UART TLB tagging: the UART page's Sv39 vpn.  The tag injectivity    *)
(*     lemma [u_sext45_inj] used by the discrimination below now lives in  *)
(*     CommonWalk.v.                                                        *)
(* ===================================================================== *)

Definition uart_vpn : mword 27 := mword_of_int 0x10000.

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
Variable s s' : mstate.
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
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
Let data2 : mword (1*1*8) :=
  update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) v.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
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
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 1) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 1 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_1_S_walk_dev a8 v d' region s s' Halign Hcp' Hmprv' Htr HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hdrd).
  reflexivity.
Qed.
End RWgS1walkDev.

Section ExecLoadGS1walkDev.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable is_unsigned : bool.
Variable v : bv 8.
Variable d' : dev_state.
Variable region : PMA_Region.
Variable s s' : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
Let data2 : mword (1*1*8) :=
  update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                  = Some (Virtaddr ea, s).
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
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) s'.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value is_unsigned data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 1).
  unfold execute_LOAD.
  replace (1 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_1_gpr_S_walk_dev rs1 offset v d' region s s' Htea Halign Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hread Hc Hsig Hh Hdev Hdrd)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value is_unsigned data2)) (MState s'.(sregs) s'.(mem) d')
               = Some (tt, set_reg (MState s'.(sregs) s'.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value is_unsigned data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned data2) (MState s'.(sregs) s'.(mem) d')).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGS1walkDev.

(* the 1-byte UART access matches the kernel's TOR entry 0 (the UART window
   [0x10000000,0x10000008) sits well inside [0, pmpaddr0*4)) *)
Lemma uart_pmp_match1 (pmpaddr0 : mword 64) (off : Z) :
  (0 <= off < uart_size)%Z ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint (uart_pa off)) (uint (to_bits 64 1)) = PMP_Match.
Proof.
  intros Hoff Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (Hw1 : uint (to_bits 64 1 : mword 64) = 1) by (vm_compute; reflexivity).
  rewrite Hz Hw1. rewrite Z.mul_0_l. rewrite (uint_uart_pa off Hoff).
  apply pmpRangeMatch_full; unfold ram_base, ram_size, uart_base, uart_size in *; lia.
Qed.
