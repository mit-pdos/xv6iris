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
Require Import SmodeCorePt SRegime WpSmodePtLeaves WpSmodePtFetch.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame HartSMem WpSmodePtEngine KptGoodb KptShare Ktier.
Require Import MemAccessGen.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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


(* the STORE engine's data premise at width 4: [RiscvExtras.trunc32] IS that
   truncation, so this is [reflexivity] -- but as a standalone equation, so
   the application it feeds carries no evars (an [eq_refl] in that position
   makes the neighbouring [rewrite]s fail with "matches but type classes
   inference fails"). *)
Lemma store_data4 (w : SailStdpp.Values.mword 64) :
  autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 4 8) 1) 0)
  = trunc32 w.
Proof. reflexivity. Qed.

Section WpSmodePtMemLeaves.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ==================================================================== *)
  (* THE TIER-INDEXED FORM (sp-migration phase D, design §4).  [kt'] is the *)
  (* DATUM's tier, [kt] the accessing hart's; [KtierLe kt' kt] is the whole *)
  (* access condition and [sr_ktier_wit R kt] (persistent, [emp] at KT0) is *)
  (* what the hart shows for it -- at KT0 the datum's own pin discharges    *)
  (* admissibility ([sr_adm_id]); at KT1 the regime's all-claims witness    *)
  (* does ([sr_absorb_wit]).  Both go through [SRegime.sr_absorb_ktier], so *)
  (* the body below is the pre-phase-D proof with ONE call respelled.       *)
  (* TIER-PRESERVING: the datum comes back at [kt'].  The [KT0/KT0]         *)
  (* corollary after [Qed] is the pre-phase-D statement, character for      *)
  (* character, so no consumer sees the generalization.                     *)
  (* ==================================================================== *)
  Lemma wp_clw_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
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
    sr_ktier_wit R kt -∗
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
    pa ↦₄[kt']{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      pa ↦₄[kt']{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    (* the three [let]s collapse: the engine spells the address as the term,
       and a local definition is not syntactically it *)
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 4
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 4
                  ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* THE WORD'S OWN CLAIM: byte 0 carries the ppn, the canonicality, the
       RAM-ness of the translated base and the tier pin -- everything the
       engine needs BEFORE it runs, and none of it needs the heap. *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    assert (Hev : extend_value (n := 8 * 4) false v = sign_extend' 64 v)
      by (unfold extend_value; reflexivity).
    iApply (wp_instr_s_config_folded R pc true
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 2⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                 gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₄[kt']{ dqm } v)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hbytes] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some (sr_swp_mode R satp0))
        by (rewrite sda_rs_satp; exact (sr_swp_mode_ok R satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor
              = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 4)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 4).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_LOAD_ram_S4 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs1 rd false m (pa_of ppn (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) pmar0 pcfg paddr v
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₄[kt']{ dqm } v)%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr
                    Lpmm
                    Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Load Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr
                       Lpmm
                       Lsxl
                       Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       Lsxl
                       Lmd)
                    Lep
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 4
                       ltac:(lia) ltac:(exists 1024; lia) Halign4)
                    Hrd
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hbytes]").
          - (* THE DATA TRANSLATION, the regime's own *)
            iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Load Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_introl eq_refl)) I Hmenvval0 HSXL HMPRV
                      Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Load Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_introl eq_refl)))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* THE RAM OBLIGATION, off the word the leaf owns *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct (s_mem_chunk (KTR := kt') sigma
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         0 4 4 (nth_byte v)
                         ppn dqm ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff
                         Hcan with "Hmem Hk Hbytes") as %(Hbf & _ & _ & _).
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iSplitR.
            { iPureIntro. intros j Hj. apply Hbf. exact Hj. }
            iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev".
            rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & Hword)".
      (* the landing file back onto the tower, at ITS OWN tlb value *)
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hany"; [| iExact "Hany"].
      iExists mstatus0, mdv0, (add_vec_int pc 2).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Hev. iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY: the pre-phase-D statement verbatim (the ambient
     tier IS the KT0 default), with the [emp] witness discharged here. *)
  Lemma wp_clw_s_r (R : s_regime)
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
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_clw_s_r_t R KT0 KT0 pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0
              (dq := dq) (dqm := dqm)
              Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.



  (* ==================================================================== *)
  (* THE TIER-INDEXED FORM (sp-migration phase D, design §4).  [kt'] is the *)
  (* DATUM's tier, [kt] the accessing hart's; [KtierLe kt' kt] is the whole *)
  (* access condition and [sr_ktier_wit R kt] (persistent, [emp] at KT0) is *)
  (* what the hart shows for it -- at KT0 the datum's own pin discharges    *)
  (* admissibility ([sr_adm_id]); at KT1 the regime's all-claims witness    *)
  (* does ([sr_absorb_wit]).  Both go through [SRegime.sr_absorb_ktier], so *)
  (* the body below is the pre-phase-D proof with ONE call respelled.       *)
  (* TIER-PRESERVING: the datum comes back at [kt'].  The [KT0/KT0]         *)
  (* corollary after [Qed] is the pre-phase-D statement, character for      *)
  (* character, so no consumer sees the generalization.                     *)
  (* ==================================================================== *)
  Lemma wp_ld_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
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
    sr_ktier_wit R kt -∗
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
    pa ↦₈[kt']{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈[kt']{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    (* the three [let]s collapse: the engine spells the address as the term,
       and a local definition is not syntactically it *)
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 8
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                  ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* THE WORD'S OWN CLAIM: byte 0 carries the ppn, the canonicality, the
       RAM-ness of the translated base and the tier pin -- everything the
       engine needs BEFORE it runs, and none of it needs the heap. *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    assert (Hev : extend_value (n := 8 * 8) false v = v)
      by (unfold extend_value; apply sign_extend'_id).
    iApply (wp_instr_s_config_folded R pc false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                 gpr_file (<[Regidx rd := regval_into_reg v]> m) ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₈[kt']{ dqm } v)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hbytes] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some (sr_swp_mode R satp0))
        by (rewrite sda_rs_satp; exact (sr_swp_mode_ok R satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor
              = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_LOAD_ram_S8 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs1 rd false m (pa_of ppn (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) pmar0 pcfg paddr v
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₈[kt']{ dqm } v)%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr
                    Lpmm
                    Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Load Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr
                       Lpmm
                       Lsxl
                       Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       Lsxl
                       Lmd)
                    Lep
                    HA Hord HR Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                       ltac:(lia) ltac:(exists 512; lia) Halign4)
                    Hrd
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hbytes]").
          - (* THE DATA TRANSLATION, the regime's own *)
            iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Load Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_introl eq_refl)) I Hmenvval0 HSXL HMPRV
                      Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Load Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_introl eq_refl)))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - (* THE RAM OBLIGATION, off the word the leaf owns *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct (s_mem_chunk (KTR := kt') sigma
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                         0 8 8 (nth_byte v)
                         ppn dqm ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff
                         Hcan with "Hmem Hk Hbytes") as %(Hbf & _ & _ & _).
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iSplitR.
            { iPureIntro. intros j Hj. apply Hbf. exact Hj. }
            iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev".
            rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & Hword)".
      (* the landing file back onto the tower, at ITS OWN tlb value *)
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hany"; [| iExact "Hany"].
      iExists mstatus0, mdv0, (add_vec_int pc 4).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      rewrite Hev. iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY: the pre-phase-D statement verbatim (the ambient
     tier IS the KT0 default), with the [emp] witness discharged here. *)
  Lemma wp_ld_s_r (R : s_regime)
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
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_ld_s_r_t R KT0 KT0 pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0
              (dq := dq) (dqm := dqm)
              Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.


  (* ==================================================================== *)
  (* THE TIER-INDEXED FORM (sp-migration phase D, design §4).  [kt'] is the *)
  (* DATUM's tier, [kt] the accessing hart's; [KtierLe kt' kt] is the whole *)
  (* access condition and [sr_ktier_wit R kt] (persistent, [emp] at KT0) is *)
  (* what the hart shows for it -- at KT0 the datum's own pin discharges    *)
  (* admissibility ([sr_adm_id]); at KT1 the regime's all-claims witness    *)
  (* does ([sr_absorb_wit]).  Both go through [SRegime.sr_absorb_ktier], so *)
  (* the body below is the pre-phase-D proof with ONE call respelled.       *)
  (* TIER-PRESERVING: the datum comes back at [kt'].  The [KT0/KT0]         *)
  (* corollary after [Qed] is the pre-phase-D statement, character for      *)
  (* character, so no consumer sees the generalization.                     *)
  (* ==================================================================== *)
  Lemma wp_csw_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
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
    sr_ktier_wit R kt -∗
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
    pa ↦₄[kt'] vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₄[kt'] storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa storeval HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea, storeval in *. clear pa a8 ea storeval.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (word4_pointsto_aligned_p (KTR := kt') with "Hbytes")
      as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 4
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 4
                  ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* the window's own claim, off byte 0, then the word refolded *)
    iDestruct (word4_pointsto_bytes (KTR := kt') with "Hbytes") as "Hbytes".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    iDestruct (word4_pointsto_intro (KTR := kt') _ _ _ Hpalign4 with "Hbytes")
      as "Hword".
    iApply (wp_instr_s_config_folded R pc true
              (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 2⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₄[kt'] (trunc32 (m !!! Regidx rs2)))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hword] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some (sr_swp_mode R satp0))
        by (rewrite sda_rs_satp; exact (sr_swp_mode_ok R satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor
              = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_STORE_ram_S4 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs2 rs1 m
                    (pa_of ppn (add_vec (m !!! Regidx rs1)
                                  (sign_extend' 64 imm)))
                    (trunc32 (m !!! Regidx rs2)) pmar0 pcfg paddr
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₄[kt'] (trunc32 (m !!! Regidx rs2)))%I
                    (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    (store_data4 (m !!! Regidx rs2))
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr
                    Lpmm
                    Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Store Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr
                       Lpmm
                       Lsxl
                       Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       Lsxl
                       Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 4
                       ltac:(lia) ltac:(exists 1024; lia) Halign4)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hword]").
          - iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Store Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_intror (or_introl eq_refl))) eq_refl
                      Hmenvval0
                      HSXL HMPRV Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Store Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_intror (or_introl eq_refl))))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (word4_pointsto_write_c (KTR := kt') sigma.(mem)
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                    vold (trunc32 (m !!! Regidx rs2)) Hcan Hoff
                    with "Hk Hmem Hword") as "[Hmem Hword]".
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev Hword". }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hword & Hfrag)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hfrag"; [| by iApply resv_any_intro].
      iExists mstatus0, mdv0, (add_vec_int pc 2).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY: the pre-phase-D statement verbatim (the ambient
     tier IS the KT0 default), with the [emp] witness discharged here. *)
  Lemma wp_csw_s_r (R : s_regime)
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
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_csw_s_r_t R KT0 KT0 pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0
              (dq := dq)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.




  (* ==================================================================== *)
  (* THE TIER-INDEXED FORM (sp-migration phase D, design §4).  [kt'] is the *)
  (* DATUM's tier, [kt] the accessing hart's; [KtierLe kt' kt] is the whole *)
  (* access condition and [sr_ktier_wit R kt] (persistent, [emp] at KT0) is *)
  (* what the hart shows for it -- at KT0 the datum's own pin discharges    *)
  (* admissibility ([sr_adm_id]); at KT1 the regime's all-claims witness    *)
  (* does ([sr_absorb_wit]).  Both go through [SRegime.sr_absorb_ktier], so *)
  (* the body below is the pre-phase-D proof with ONE call respelled.       *)
  (* TIER-PRESERVING: the datum comes back at [kt'].  The [KT0/KT0]         *)
  (* corollary after [Qed] is the pre-phase-D statement, character for      *)
  (* character, so no consumer sees the generalization.                     *)
  (* ==================================================================== *)
  Lemma wp_sd_s_r_t (R : s_regime) (kt kt' : ktier) `{!KtierLe kt' kt}
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
    sr_ktier_wit R kt -∗
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
    pa ↦₈[kt'] vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈[kt'] (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ea a8 pa HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    unfold pa, a8, ea in *. clear pa a8 ea.
    iIntros "#Hwit #Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (word_pointsto_aligned_p (KTR := kt') with "Hbytes")
      as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr
              (Virtaddr (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))) 8
              = true) by exact Hpalign4.
    pose proof (off_bound_div
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                  ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* the window's own claim, off byte 0, then the word refolded *)
    iDestruct (word_pointsto_bytes (KTR := kt') with "Hbytes") as "Hbytes".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes")
      as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc (KTR := kt') with "Hb0")
      as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0
             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    iDestruct (word_pointsto_intro (KTR := kt') _ _ _ Hpalign4 with "Hbytes")
      as "Hword".
    iApply (wp_instr_s_config_folded R pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 => (⌜npc = add_vec_int pc 4⌝ ∗
                 ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗ gpr_file m ∗
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                   ↦₈[kt'] (m !!! Regidx rs2))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr
                    [Hfile Hword] [Hcont]").
    - iIntros "Hpriv Hms Hmie Hmdl Hmenv Hslot Hclk HPC HnPC Hresv".
      (* THE SLOT STAYS FOLDED.  [sda_slot_acc_R] is the one place the two
         translation arms are told apart: it hands out an ABSTRACT write set
         with its frames, the residue, and the arm's translation SIDE
         CONDITION already discharged -- the one thing a regime-generic leaf
         cannot produce for itself ([sr_swp_side_ok] demands [tlb ∈ Drw], and
         the Bare arm's write set is empty). *)
      iDestruct (sda_slot_acc_R R dq mstatus0 menvcfg0 pmar0
                   Hmenvval0 HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hslot")
        as (SD satp0 pcfg paddr tv')
           "(%Hdisj & %Hsub & %Hsok & %Hpok & %Hside & Hrw & Hro & HRes &
             Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR & Hcov).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) ('b"0") = true)
        by (rewrite sda_rs_mst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM
                (register_lookup menvcfg (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))) = PMM_Disabled)
        by (rewrite sda_rs_menv; exact Hpmm).
      assert (Lsxl : _get_Mstatus_SXL
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) = 'b"10")
        by (rewrite sda_rs_mst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))) = Some (sr_swp_mode R satp0))
        by (rewrite sda_rs_satp; exact (sr_swp_mode_ok R satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data)
                (register_lookup mstatus (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')) Supervisor
              = returnM Supervisor)
        by (rewrite sda_rs_mst;
            exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Hclose] [-]").
      2:{ iApply (swp_execute_STORE_ram_S8 SD sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    imm rs2 rs1 m
                    (pa_of ppn (add_vec (m !!! Regidx rs1)
                                  (sign_extend' 64 imm)))
                    (m !!! Regidx rs2) pmar0 pcfg paddr
                    ((add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       ↦₈[kt'] (m !!! Regidx rs2))%I (sr_swp_res R) rr
                    (sr_swp_mode R satp0)
                    (store_data8 (m !!! Regidx rs2))
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr
                    Lpmm
                    Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
                       (Store Data) (sr_swp_mode R satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep
                       eq_refl eq_refl eq_refl
                       Lmxr
                       Lpmm
                       Lsxl
                       Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                       (sr_swp_mode R satp0) (sda_in_mst_D SD) (sda_in_satp_D SD)
                       Lsxl
                       Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_ram Hpma_all) Hkd0
                    Halign4
                    (pa_aligned_div ppn
                       (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 8
                       ltac:(lia) ltac:(exists 512; lia) Halign4)
                    with "Hcert Hfrag HRes Hfile Hrw Hro [] [Hword]").
          - iIntros "Hfrag HRes Hrw Hro".
            iApply (sda_translate_D R SD kt kt' dq (Store Data) KP_rw mstatus0
                      menvcfg0 satp0 pmar0 pcfg paddr tv'
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn rr
                      (or_intror (or_intror (or_introl eq_refl))) eq_refl
                      Hmenvval0
                      HSXL HMPRV Hsok
                      ltac:(unfold pmp_ent0_ok; split_and!; assumption)
                      (pma_all_ram Hpma_all) Hcan Hid Hdisj
                      (Hside (Store Data) KP_rw
                         (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                         tv' (or_intror (or_intror (or_introl eq_refl))))
                      with "Hwit Hk Hcert Hfrag HRes Hrw Hro").
          - iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iMod (word_pointsto_write_c (KTR := kt') sigma.(mem)
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ppn
                    vold (m !!! Regidx rs2) Hcan Hoff
                    with "Hk Hmem Hword") as "[Hmem Hword]".
            iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
            iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev Hword". }
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hword & Hfrag)".
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)
                   SD ∗
                 hreg_frame_ro (sda_Df dq)
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 sr_swp_res_at R satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tv'. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0
                       pcfg paddr tv' tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree R
                   (register_set tlb tvx
                      (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      iAssert (sr_swp_res R
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree R
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv2)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes")
        as "(Hms & Hpriv & Hmenv & _ & _ & _ & Hslot)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hslot Hclk".
      iSplitR "Hfrag"; [| by iApply resv_any_intro].
      iExists mstatus0, mdv0, (add_vec_int pc 4).
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfile Hword".
    - iNext. iIntros (npc ms1 mdv1)
        "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc
         (-> & -> & -> & Hfile & Hword)".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                            Hword").
  Qed.

  (* THE KT0/KT0 COROLLARY: the pre-phase-D statement verbatim (the ambient
     tier IS the KT0 default), with the [emp] witness discharged here. *)
  Lemma wp_sd_s_r (R : s_regime)
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
    iPoseProof (sr_ktier_wit_KT0 R) as "#Hwit".
    iApply (wp_sd_s_r_t R KT0 KT0 pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0
              (dq := dq)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 with "Hwit").
  Qed.


  (* width-1 store leaf: sb rs2, imm(rs1) to a RAM byte, γ-form.  Same
     absorption recipe; the byte window is a single [↦ₘ] cell. *)


End WpSmodePtMemLeaves.
