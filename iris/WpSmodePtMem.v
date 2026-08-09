(* WpSmodePtMem.v -- remaining S-mode load/store leaves over [tlb_inv_pt]:
   the width-4 (clw/lw/csw/sw) and width-1 (sb) data leaves plus the
   4-byte-encoded width-8 forms (ld/sd).  State-generic width-4/1 towers
   cloned from WpSmodeLoad.v / WpSmodeStore.v; leaves follow the
   wp_cld_s_pt / wp_csd_s_pt recipe (see WpSmodePtLeaves.v). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import RegFile.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte.
Require Import SmodeCore WpSmodeGpr.
Require Import UserBits.
Require Import SmodeCorePt SRegime WpSmodePtLeaves.
Require Import MemAccessGen.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ---- Local width-4/1 helpers copied from WpSmodeLoad.v / WpSmodeStore.v ---- *)

Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
  Proof. change (0 * 4) with 0. apply avi0. Qed.

Local Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    intros Hmatch Halign Hread.
    destruct region as [rbase rsize rattr rdtree].
    pma_ok_peel Hmatch Hread (exec_is_mag_applicable_load_data 4 s) Halign.
  Qed.


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
    assert (Hcp : exec (check_pma_with_pmp_priority (Load Data) pbmt Supervisor
                          (Physaddr addr) 4 false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_load_4 addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s)).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite avi0_mul4.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant_load_data addr 4 s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrdr). cbn beta zeta.
      rewrite autocast_id.
      change (8 * 1 * 4) with 32. change (8 * (0 + 1) * 4 - 1) with 31. change (8 * 0 * 4) with 0.
      rewrite usvd_zeros32.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite autocast_id. rewrite execR_returnR. reflexivity.
  Qed.

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

Local Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    intros Hmatch Halign Hwrite.
    destruct region as [rbase rsize rattr rdtree].
    pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_data 4 s) Halign.
  Qed.


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
    assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt Supervisor
                          (Physaddr addr) 4 false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 4) = addr)
        by (change (0 * 4)%Z with 0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant_store addr 4 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      rewrite autocast_id.
      change (8 * (0 + 1) * 4 - 1) with 31. change (8 * 0 * 4) with 0.
      rewrite subrange_full_32.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_write_ram_plain_4 addr data s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

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

Local Lemma exec_pmaCheck_ram_store_1 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (pmaCheck (Physaddr addr) 1 (Store Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    intros Hmatch Halign Hwrite.
    destruct region as [rbase rsize rattr rdtree].
    pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_data 1 s) Halign.
  Qed.

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
    assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt Supervisor
                          (Physaddr addr) 1 false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_1 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr addr) 1) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 1 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 1) = addr)
        by (change (0 * 1)%Z with 0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant_store addr 1 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      rewrite autocast_id.
      change (8 * (0 + 1) * 1 - 1) with 7. change (8 * 0 * 1) with 0.
      rewrite subrange_full_8.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_write_ram_plain_1 addr data s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

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







(* ---- state-generic width-4/1 towers ---- *)

  Section RWS4walkPt.
  Variable a : mword 64.
  Variable v : mword (8*4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Load Data)) s
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
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_4_S_walk_pt :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Ok v, s').
  Proof.
    assert (Heff : exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
    { rewrite Hcps. apply exec_effectivePrivilege_load_S. exact Hmprvs. }
    apply (exec_vmem_read_addr_aligned_load 4 a pa v Supervisor md s s'
             ltac:(right; right; left; reflexivity) Halign Heff Htm).
    apply (exec_translate_and_read_value_g 4 a pa PBMT_PMA v s s' s' Htr).
    exact (exec_mem_read_load_4_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
             HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv' Hcp').
  Qed.
  End RWS4walkPt.

  Section RWgS4walkPt.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable v : mword (8*4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
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
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_4_gpr_S_walk_pt :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok v, s').
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      rewrite Ha8ea. apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_4_S_walk_pt a8 v region s s' pa Halign Hcp' Hmprv'
               md Hcps Hmprvs Htm Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.
  End RWgS4walkPt.

  Section ExecLoadGS4walkPt.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable v : mword (8*4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Variable md : SATPMode.
  Hypothesis Hcps : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprvs : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htm : exec (translationMode Supervisor) s = Some (md, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Load Data)) s
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
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_gpr_S_walk_pt :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false v))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 4).
    unfold execute_LOAD.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_read_4_gpr_S_walk_pt rs1 offset v region s s' pa Htea Halign
         md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value false v)) s'
                 = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false v)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value false v) s').
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.
  End ExecLoadGS4walkPt.

  Section SWS4walkPt.
  Variable a : mword 64.
  Variable data : mword (8*4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
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
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_4_S_walk_pt :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)).
  Proof.
    assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
    { rewrite Hcps. apply exec_effectivePrivilege_store_S. exact Hmprvs. }
    assert (Hea : exec (mem_write_ea (Physaddr pa) 4 (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok tt, s')).
    { apply (exec_mem_write_ea_g 4 pa (Store Data) PBMT_PMA Supervisor s').
      - rewrite Hcp. apply exec_effectivePrivilege_store_S. exact Hmprv.
      - unfold check_pma_with_pmp_priority.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmaCheck_ram_store_4 pa PBMT_PMA region s' Hmatch Hpalign Hwrite)).
        cbn match. apply exec_returnM.
      - exact (exec_pmpCheck_supervisor_grant_store pa 4 s' HA Hord Hrange HW). }
    assert (Hwv : exec (mem_write_value (Physaddr pa) 4
                          (autocast (T := mword) (subrange_vec_dec data (8*4-1) 0))
                          (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev))).
    { rewrite (subrange_full_gen_cast (8 * 4) data ltac:(lia)).
      exact (exec_mem_write_value_4_S PBMT_PMA pa region data
               (register_lookup mstatus s'.(sregs)) s'
               HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp). }
    exact (exec_vmem_write_addr_aligned_store 4 a pa data Supervisor md s s'
             (MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev))
             ltac:(right; right; left; reflexivity) Halign Heff Htm Htr Hea Hwv).
  Qed.
  End SWS4walkPt.

  Section VWgS4walkPt.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : mword (8*4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
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
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_4_gpr_S_walk_pt :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      rewrite Ha8ea. apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_4_S_walk_pt a8 data region s s' pa Halign Hcp' Hmprv'
               md Hcps Hmprvs Htm Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS4walkPt.

  Section ExecStoreGS4walkPt.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
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
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_gpr_S_walk_pt :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s'.(mem) pa 4
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
      (exec_vmem_write_4_gpr_S_walk_pt rs1 offset _ region s s' pa Htea Halign
         md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS4walkPt.

  Section SWS1walkPt.
  Variable a : mword 64.
  Variable data : mword (8*1).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_1_S_walk_pt :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 1 data) s'.(mdev)).
  Proof.
    assert (Heff : exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (Supervisor, s)).
    { rewrite Hcps. apply exec_effectivePrivilege_store_S. exact Hmprvs. }
    assert (Hpalign1 : is_aligned_paddr (Physaddr pa) 1 = true)
      by (unfold is_aligned_paddr; rewrite Z.rem_1_r; reflexivity).
    assert (Hea : exec (mem_write_ea (Physaddr pa) 1 (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok tt, s')).
    { apply (exec_mem_write_ea_g 1 pa (Store Data) PBMT_PMA Supervisor s').
      - rewrite Hcp. apply exec_effectivePrivilege_store_S. exact Hmprv.
      - unfold check_pma_with_pmp_priority.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmaCheck_ram_store_1 pa PBMT_PMA region s' Hmatch Hpalign1 Hwrite)).
        cbn match. apply exec_returnM.
      - exact (exec_pmpCheck_supervisor_grant_store pa 1 s' HA Hord Hrange HW). }
    assert (Hwv : exec (mem_write_value (Physaddr pa) 1
                          (autocast (T := mword) (subrange_vec_dec data (8*1-1) 0))
                          (Store Data) PBMT_PMA false false false) s'
                  = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 1 data) s'.(mdev))).
    { rewrite (subrange_full_gen_cast (8 * 1) data ltac:(lia)).
      exact (exec_mem_write_value_1_S PBMT_PMA pa region data
               (register_lookup mstatus s'.(sregs)) s'
               HA Hord Hrange HW Hmatch Hpalign1 Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp). }
    exact (exec_vmem_write_addr_aligned_store 1 a pa data Supervisor md s s'
             (MState s'.(sregs) (write_bytes s'.(mem) pa 1 data) s'.(mdev))
             ltac:(left; reflexivity) Halign Heff Htm Htr Hea Hwv).
  Qed.
  End SWS1walkPt.

  Section VWgS1walkPt.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : mword (8*1).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_1_gpr_S_walk_pt :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 1 data) s'.(mdev)).
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
    rewrite (exec_vmem_write_addr_1_S_walk_pt a8 data region s s' pa Halign Hcp' Hmprv'
               md Hcps Hmprvs Htm Htr HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
  End VWgS1walkPt.

  Section ExecStoreGS1walkPt.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
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
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_1_gpr_S_walk_pt :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s'.(mem) pa 1
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
      (exec_vmem_write_1_gpr_S_walk_pt rs1 offset _ region s s' pa Htea Halign
         md Hcps Hmprvs Htm Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walkPt.


Section WpSmodePtMemLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma wp_clw_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (v : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
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
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] Hfmap Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_s_config_regime R Φ pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0
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
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div a8 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iDestruct (sr_transform R (Load Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htlbinv") as %Htea.
    iDestruct (sr_tmode R s_pc LSXL_pc with "Hreg Htlbinv") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb R (Load Data) a8 (pa_of ppn a8) ppn KP_rw s_pc _
            (or_intror (or_introl eq_refl)) I
            (lo_canonical a8 Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' (sr_adm_id R a8 ppn Hid) _ with "Hk Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)"; [solve_ndisj |].
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
    iDestruct (s_mem_chunk s_tr pa a8 0 4 4 (nth_byte v) ppn dqm
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram3 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn a8) 4
               (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl)) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn a8))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn a8) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn a8) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn a8) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn a8) (4 - 1)) with (pa_add (pa_of ppn a8) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w (pa_of ppn a8) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov1) as Hrange_ld.
    pose proof (within_clint_false (pa_of ppn a8) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn a8) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn a8) 4 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value (n := 8 * 4) false v = sign_extend' 64 v).
    { unfold extend_value. reflexivity. }
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr a8))) (Load Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn a8), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr a8)) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 v)))).
    { rewrite <- Hev.
      apply (exec_execute_LOAD_4_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr (pa_of ppn a8) Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               Hrange_ld HR1
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               (pa_aligned_div ppn a8 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hread_ld Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)
               Hbytesf_tr). }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (sign_extend' 64 v)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (sign_extend' 64 v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sign_extend' 64 v))).(sregs)
             = add_vec_int pc 2).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] Hfmap Hbw").
  Qed.



  Lemma wp_ld_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (v : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
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
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] Hfmap Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_s_config_regime R Φ pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0
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
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div a8 8 ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    (* the data-side translation through the absorption theorem: identity
       pa, state moved to some absorbable s_tr (hit / fill / write-back) *)
    iDestruct (sr_transform R (Load Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htlbinv") as %Htea.
    iDestruct (sr_tmode R s_pc LSXL_pc with "Hreg Htlbinv") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb R (Load Data) a8 (pa_of ppn a8) ppn KP_rw s_pc _
            (or_intror (or_introl eq_refl)) I
            (lo_canonical a8 Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' (sr_adm_id R a8 ppn Hid) _ with "Hk Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)"; [solve_ndisj |].
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
    iDestruct (s_mem_chunk s_tr pa a8 0 8 8 (nth_byte v) ppn dqm
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram7 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn a8) 8
               (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn a8))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn a8) + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn a8) + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add (pa_of ppn a8) 7 Hnw) as Heq.
      change (pa_add (pa_of ppn a8) (8 - 1)) with (pa_add (pa_of ppn a8) 7) in Hram7.
      destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w (pa_of ppn a8) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 8
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov1) as Hrange_ld.
    pose proof (within_clint_false (pa_of ppn a8) 8 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn a8) 8 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn a8) 8 s_tr Lhtif_tr) as Hwh.
    assert (Hev : extend_value (n := 8 * 8) false v = v).
    { unfold extend_value. apply sign_extend'_id. }
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr a8))) (Load Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn a8), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr a8)) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg v))).
    { rewrite <- Hev.
      apply (exec_execute_LOAD_8_gpr_S_walk_pt rs1 rd imm v region_ld s_pc s_tr (pa_of ppn a8) Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               Hrange_ld HR1
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               (pa_aligned_div ppn a8 8 ltac:(lia) ltac:(exists 512; lia) Halign4)
               Hread_ld Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)
               Hbytesf_tr). }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg v) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] Hfmap Hbw").
  Qed.


  Lemma wp_csw_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := trunc32 (m !!! Regidx rs2) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
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
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa storeval HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] Hfmap Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_s_config_regime R Φ pc true (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
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
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div a8 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform R (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htlbinv") as %Htea.
    iDestruct (sr_tmode R s_pc LSXL_pc with "Hreg Htlbinv") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb R (Store Data) a8 (pa_of ppn a8) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical a8 Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' (sr_adm_id R a8 ppn Hid) _ with "Hk Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)"; [solve_ndisj |].
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
    iDestruct (s_mem_chunk s_tr pa a8 0 4 4 (nth_byte vold) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(_ & Hram0 & Hram3 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn a8) 4
               (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl)) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn a8))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn a8) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn a8) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn a8) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn a8) (4 - 1)) with (pa_add (pa_of ppn a8) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w (pa_of ppn a8) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov1) as Hrange_st.
    pose proof (within_clint_false (pa_of ppn a8) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn a8) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn a8) 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr a8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn a8), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr a8)) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn a8) 4 storeval)
                              s_tr.(mdev))).
    { pose proof (exec_execute_STORE_4_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr (pa_of ppn a8)
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               Hrange_st HW1
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn a8 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite Lv2 in H0.
      exact H0. }
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) vold Hpalign4 with "Hbytes") as "Hbytes".
    iMod (word4_pointsto_write_c s_tr.(mem) pa ppn vold storeval Hcan Hoff with "Hk Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn a8) 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn a8) 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 2).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] Hfmap Hbytes").
  Qed.




  Lemma wp_sd_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (vold : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
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
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] Hfmap Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr_s_config_regime R Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
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
    (* the word's OWN base claim + canonicality (peek byte 0 of its bytes) *)
    iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hb".
    pose proof (off_bound_div a8 8 ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform R (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htlbinv") as %Htea.
    iDestruct (sr_tmode R s_pc LSXL_pc with "Hreg Htlbinv") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb R (Store Data) a8 (pa_of ppn a8) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical a8 Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' (sr_adm_id R a8 ppn Hid) _ with "Hk Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htlbinv)"; [solve_ndisj |].
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
    iDestruct (s_mem_chunk s_tr pa a8 0 8 8 (nth_byte vold) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hb") as %(_ & Hram0 & Hram7 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn a8) 8
               (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn a8))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn a8) + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn a8) + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add (pa_of ppn a8) 7 Hnw) as Heq.
      change (pa_add (pa_of ppn a8) (8 - 1)) with (pa_add (pa_of ppn a8) 7) in Hram7.
      destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w (pa_of ppn a8) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 8
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov1) as Hrange_st.
    pose proof (within_clint_false (pa_of ppn a8) 8 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn a8) 8 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn a8) 8 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr a8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn a8), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace (bits_of_virtaddr (Virtaddr a8)) with a8
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn a8) 8 (m !!! Regidx rs2))
                              s_tr.(mdev))).
    { pose proof (exec_execute_STORE_8_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr (pa_of ppn a8)
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva; rewrite subrange_id; rewrite sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               Hrange_st HW1
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn a8 8 ltac:(lia) ltac:(exists 512; lia) Halign4)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite Lv2 in H0.
      exact H0. }
    iDestruct (word_pointsto_intro pa (DfracOwn 1) vold Hpalign4 with "Hb") as "Hbytes".
    iMod (word_pointsto_write_c s_tr.(mem) pa ppn vold (m !!! Regidx rs2) Hcan Hoff with "Hk Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn a8) 8 (m !!! Regidx rs2)) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn a8) 8 (m !!! Regidx rs2)) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] Hfmap Hbytes").
  Qed.


  (* width-1 store leaf: sb rs2, imm(rs1) to a RAM byte, γ-form.  Same
     absorption recipe; the byte window is a single [↦ₘ] cell. *)


End WpSmodePtMemLeaves.
