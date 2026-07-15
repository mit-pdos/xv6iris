(* MemAmo4.v -- mode-neutral width-4 ATOMIC (AMOSWAP.W) memory leaf lemmas.

   The width-4 atomic read-modify-write core, factored out of the S-mode
   AMOSWAP tower (WpAmo.v).  Everything is privilege-GENERIC: the access
   privilege enters ONLY through the pmpCheck grant, supplied by the caller
   as a hypothesis [Hpmp] (S the supervisor grant, U the user grant).  The
   effective-address transform [Htea] and address translation [Htr] are
   likewise hypotheses, and [pa] is an ABSTRACT Variable (identity for the
   kernel, real Sv39 [u_pa] for U-mode).  The AMO read kind is
   Read_RISCV_reserved_acquire and the write kind Write_RISCV_conditional. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* pmaCheck for an aligned RAM AMO with atomic support (res_or_con = true). *)
Lemma exec_pmaCheck_ram_amo_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (pmaCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) pbmt true) s = Some (None, s).
Proof.
  intros Hmatch Halign Hread Hwrite Hamo.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread, Hwrite, Hamo |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  match goal with |- exec (?m >>= ?k) s = _ =>
    assert (Hass : exec m s
            = Some (andb (PMA_readable (override_PMA rattr pbmt))
                      (andb (PMA_writable (override_PMA rattr pbmt))
                         (pma_allows_atomic_op (PMA_atomic_support (override_PMA rattr pbmt))
                            AMOSWAP 4)), s))
      by (rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl s)); apply exec_returnM);
    rewrite (exec_bind_Some _ _ _ _ _ Hass)
  end.
  cbn beta.
  rewrite Hread Hwrite Hamo. cbn [andb]. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_effectivePrivilege_amo_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Atomic (AMOSWAP, Data, Data)) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma run_read_ram_resacq_4_pin (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram rv64d_types.Read_RISCV_reserved_acquire (Physaddr addr) 4 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_resacq_4 (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rv64d_types.Read_RISCV_reserved_acquire (Physaddr addr) 4 false) s
  = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_resacq_4_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

Lemma exec_write_ram_cond_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_RISCV_conditional (Physaddr addr) 4 data tt) s
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

Lemma exec_mem_write_ea_amo_4 (addr : mword 64) s :
  is_aligned_paddr (Physaddr addr) 4 = true ->
  exec (mem_write_ea (Physaddr addr) 4 false false true) s = Some (Ok tt, s).
Proof.
  intro Halign. unfold mem_write_ea.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false true) s
                 = Some (rv64d_types.Write_RISCV_conditional, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_ram_amo_4 (p : Privilege) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Atomic (AMOSWAP, Data, Data)) pbmt p (Physaddr addr) 4 true false true false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_RISCV_reserved_acquire, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resacq_4 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_amo_4 (p : Privilege) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = p ->
  exec (mem_read (Atomic (AMOSWAP, Data, Data)) pbmt (Physaddr addr) 4 true false true)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm m p s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta.
      rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_amo_4 with (p := p) (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_ram_amo_4 (p : Privilege) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt p tt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
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
            (_ : exec (write_kind_of_flags false false true) s
                 = Some (rv64d_types.Write_RISCV_conditional, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_4 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_amo_4 (p : Privilege) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = p ->
  exec (mem_write_value (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm m p s Hmprv)).
  unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_amo_4 p pbmt addr region data s Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section ExecAmoGS4.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable w : mword 32.
  Variable s : mstate.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable pa : mword 64.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr a, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval) s.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_AMO. cbn zeta.
    rewrite exec_catch_early_return.
    assert (Hae : exec (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2)) "extensions/A/zaamo_insts.sail:73.32-73.33") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s)).
    cbn beta match.
    replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
    cbv iota.
    (* rs2_val: (liftR (rX_bits rs2) >>= returnR (trunc ..)) >>= k *)
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn beta. rewrite execR_returnR. cbn match.
    (* mem_write_ea *)
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_amo_4 pa s Hpalign)).
    cbn match.
    (* mem_read: (liftR (mem_read ..) >>= match) >>= fun loaded => .. *)
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_read_amo_4 p PBMT_PMA pa region w (register_lookup mstatus s.(sregs)) s
                 Hpmp Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev Hbytes eq_refl Hmprv Hcp)).
    cbn match. rewrite execR_returnR. cbn match.
    cbn zeta. cbn match.
    (* AMOCAS test is false: and_boolM short-circuits *)
    replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
    rewrite execR_returnR. cbn match.
    (* the conditional write of rs2's low 32 bits *)
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_value_amo_4 p PBMT_PMA pa region _ (register_lookup mstatus s.(sregs)) s
                 Hpmp Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv Hcp)).
    cbn match.
    (* rd := sext64(loaded) on the post-write state *)
    match goal with |- context[execR _ ?st] =>
      set (s_m := st)
    end.
    assert (HwX : execR (Defs.liftR (wX_bits (Regidx rd)
                     (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))
                   : Defs.monadR ExecutionResult exception unit) s_m
                  = Some (inr tt,
                          set_reg s_m (R_bitvector_64 (gpr_of_Z (uint rd)))
                            (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))))).
    { rewrite execR_liftR.
      rewrite (exec_wX_bits_gpr rd _ s_m).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    rewrite (execR_bind0_Some _ _ _ _ HwX).
    rewrite execR_returnR.
    cbn.
    reflexivity.
  Qed.
End ExecAmoGS4.

(* ===================================================================== *)
(* AMOSWAP.W gpr-walk core: translate MISSES at s and FILLS -> s'; the AMO *)
(* read+write body runs at s'.  State-threading twin of ExecAmoGS4.        *)
(* ===================================================================== *)
Section ExecAmoGS4Walk.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable w : mword 32.
  Variable s s' : mstate.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable pa : mword 64.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr a, s).
  Hypothesis Htr : exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr_walk :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s'.(mem) pa 4 storeval) s'.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_AMO. cbn zeta.
    rewrite exec_catch_early_return.
    assert (Hae : exec (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2)) "extensions/A/zaamo_insts.sail:73.32-73.33") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s')).
    cbn beta match.
    replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
    cbv iota.
    (* rs2_val: (liftR (rX_bits rs2) >>= returnR (trunc ..)) >>= k *)
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')).
    cbn beta. rewrite execR_returnR. cbn match.
    (* mem_write_ea *)
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_amo_4 pa s' Hpalign)).
    cbn match.
    (* mem_read: (liftR (mem_read ..) >>= match) >>= fun loaded => .. *)
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_read_amo_4 p PBMT_PMA pa region w (register_lookup mstatus s'.(sregs)) s'
                 Hpmp Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev Hbytes eq_refl Hmprv Hcp)).
    cbn match. rewrite execR_returnR. cbn match.
    cbn zeta. cbn match.
    (* AMOCAS test is false: and_boolM short-circuits *)
    replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
    rewrite execR_returnR. cbn match.
    (* the conditional write of rs2's low 32 bits *)
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_value_amo_4 p PBMT_PMA pa region _ (register_lookup mstatus s'.(sregs)) s'
                 Hpmp Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv Hcp)).
    cbn match.
    (* rd := sext64(loaded) on the post-write state *)
    match goal with |- context[execR _ ?st] =>
      set (s_m := st)
    end.
    assert (HwX : execR (Defs.liftR (wX_bits (Regidx rd)
                     (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))
                   : Defs.monadR ExecutionResult exception unit) s_m
                  = Some (inr tt,
                          set_reg s_m (R_bitvector_64 (gpr_of_Z (uint rd)))
                            (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))))).
    { rewrite execR_liftR.
      rewrite (exec_wX_bits_gpr rd _ s_m).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    rewrite (execR_bind0_Some _ _ _ _ HwX).
    rewrite execR_returnR.
    cbn.
    reflexivity.
  Qed.
End ExecAmoGS4Walk.
