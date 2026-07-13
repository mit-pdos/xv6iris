(* UmodeLrsc.v -- U-mode LR/SC fault-execute tower (LR/SC PROHIBITED).

   On this platform LR/SC are assumed prohibited: the RAM region has
   PMA_reservability = RsrvNone, so a LoadReserved / StoreConditional
   fails the PMA check with an access fault BEFORE the model's
   uninterpreted reservation axiom (load_reservation) is reached.  This
   file proves the faulting execute of LR.W (and SC.W): translate the
   data address (TLB hit), then the PMA check returns the access fault,
   which memory_exception turns into a trap ExecutionResult. *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGpr WpLoad MemData4 SmodeCore UmodeFetch UmodeData.
Local Open Scope Z_scope.
Import Defs.

(* pmaCheck for an aligned RAM LoadReserved with reservability RsrvNone:
   the region does not support reservations -> access fault. *)
Lemma exec_pmaCheck_ram_loadres_fail (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) = RsrvNone ->
  exec (pmaCheck (Physaddr addr) 4 (LoadReserved Data) pbmt true) s
    = Some (Some (E_Load_Access_Fault tt), s).
Proof.
  intros Hmatch Halign Hresv.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hresv |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:111.56-111.57" >>=
          (fun _ : true = true =>
             returnM (andb (PMA_readable (override_PMA rattr pbmt))
                        (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone))))
    with (returnM (andb (PMA_readable (override_PMA rattr pbmt))
                    (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hresv.
  replace (generic_neq RsrvNone RsrvNone) with false by (vm_compute; reflexivity).
  rewrite andb_false_r.
  replace (get_config_print_pma tt) with false by (vm_compute; reflexivity).
  cbn match.
  apply exec_returnM.
Qed.

(* pmpCheck user grant for a LoadReserved: pmpCheckRWX checks R, exactly
   like Load Data -- clone of exec_pmpCheck_user_grant_load. *)
Lemma exec_pmpCheck_user_grant_loadres (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (LoadReserved Data) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (LoadReserved Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* checked_mem_read for a prohibited LoadReserved: pmp grant passes, PMA
   fails on reservability -> Err (access fault).  aq/rl/meta are free. *)
Lemma exec_checked_mem_read_ram_loadres_fail (p : Privilege) (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (aq rl meta : bool) s :
  exec (pmpCheck (Physaddr addr) 4 (LoadReserved Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) = RsrvNone ->
  exec (checked_mem_read (LoadReserved Data) pbmt p (Physaddr addr) 4 aq rl true meta) s
    = Some (Err (E_Load_Access_Fault tt), s).
Proof.
  intros Hpmp Hmatch Halign Hresv.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (Some (E_Load_Access_Fault tt), s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_loadres_fail addr pbmt region s Hmatch Halign Hresv)).
      cbn match. apply exec_returnM. }
  cbn match. apply exec_returnM.
Qed.

(* effectivePrivilege for LoadReserved below Machine (MPRV clear): identity. *)
Lemma exec_effectivePrivilege_loadres_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (LoadReserved Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* untilMT with a body that early-returns (inl) on the first iteration:
   the early-return propagates out of the loop unchanged. *)
Lemma execR_untilMT_1_early {R Vars} (vars : Vars) (measure : Vars -> Z)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars)
   (r : R) s s' :
  measure vars = 1 ->
  execR (body vars) s = Some (inl r, s') ->
  execR (Defs.untilMT vars measure cond body) s = Some (inl r, s').
Proof.
  intros Hm Hb. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge]; [| exfalso; rewrite Hm in Hge; lia ].
  rewrite execR_bind. rewrite Hb. reflexivity.
Qed.

(* mem_read for a prohibited LoadReserved faults with the access fault. *)
Lemma exec_mem_read_loadres_fail (p : Privilege) (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (m : mword 64) (aq rl : bool) s :
  exec (pmpCheck (Physaddr addr) 4 (LoadReserved Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) = RsrvNone ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = p ->
  exec (mem_read (LoadReserved Data) pbmt (Physaddr addr) 4 aq (andb aq rl) true) s
    = Some (Err (E_Load_Access_Fault tt), s).
Proof.
  intros Hpmp Hmatch Halign Hresv Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_loadres_nm m p s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Err (E_Load_Access_Fault tt), s))).
  2:{ unfold mem_read_priv_meta.
      rewrite Halign. rewrite andb_false_r. cbn match.
      destruct aq; cbn [andb] in *;
        rewrite (exec_bind_Some _ _ _ _ _
                  (exec_checked_mem_read_ram_loadres_fail p pbmt addr region _ _ false s
                     Hpmp Hmatch Halign Hresv));
        cbn match; apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* memory_exception delivers a Trap ExecutionResult carrying the current
   privilege, the sync exception (cause + xtval), and the current PC. *)
Lemma exec_memory_exception (vaddr : virtaddr) (e : ExceptionType) s :
  exec (memory_exception vaddr e) s
    = Some (Trap (register_lookup cur_privilege s.(sregs),
                  make_sync_exception e (bits_of_virtaddr vaddr),
                  register_lookup PC s.(sregs)), s).
Proof.
  unfold memory_exception, trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* Fault-execute tower for a prohibited LR.W (reservability = RsrvNone).  *)
(* Mirrors MemData4's SUCCESS vmem_read chain, but on the Err branch:     *)
(* translate hits, PMA fails, memory_exception -> early_return the Trap.  *)
(* ===================================================================== *)

Section GenVMemReadLoadresFail4.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Access_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (LoadReserved Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (LoadReserved Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.

  Lemma exec_vmem_read_addr_loadres_fail :
    exec (vmem_read_addr (Virtaddr a) 4 (LoadReserved Data) aq (andb aq rl) true) s
      = Some (Err W, s).
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
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_loadres_fail p PBMT_PMA pa region
               (register_lookup mstatus s.(sregs)) aq rl s
               Hpmp Hmatch Hpalign Hresv eq_refl Hmprv Hcp)).
          cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_Load_Access_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.
End GenVMemReadLoadresFail4.

Section GenExecLoadresFail4.
  Variable p : Privilege.
  Variable rs1 rd : mword 5.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Access_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (LoadReserved Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (LoadReserved Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (LoadReserved Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.

  Lemma exec_vmem_read_loadres_fail :
    exec (vmem_read (Regidx rs1) (zeros' 64) 4 (LoadReserved Data) aq (andb aq rl) true) s
      = Some (Err W, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (LoadReserved Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (LoadReserved Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_loadres_fail p a region s pa aq rl
               Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hresv).
    reflexivity.
  Qed.

  (* Faulting execute of LR.W: vmem_read returns Err, execute returns the Trap. *)
  Lemma exec_execute_LOADRES_fault :
    exec (execute (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd))) s = Some (W, s).
  Proof.
    change (execute (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd)))
      with (execute_LOADRES aq rl (Regidx rs1) 4 (Regidx rd)).
    unfold execute_LOADRES.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_read_loadres_fail)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecLoadresFail4.

(* ===================================================================== *)
(* SC.W fault-execute tower (StoreConditional prohibited).                *)
(*                                                                         *)
(* With LR/SC prohibited, no reservation is ever established, so           *)
(* match_reservation is always false.  Then SC.W takes the no-matching-    *)
(* reservation branch of vmem_write_addr, which runs phys_access_check      *)
(* directly; the store-conditional PMA check (writable and reservability    *)
(* not RsrvNone) fails on RsrvNone, giving E_SAMO_Access_Fault, then trap.  *)
(* ===================================================================== *)

(* pmaCheck for an aligned RAM StoreConditional with reservability RsrvNone. *)
Lemma exec_pmaCheck_ram_storecon_fail (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) = RsrvNone ->
  exec (pmaCheck (Physaddr addr) 4 (StoreConditional Data) pbmt true) s
    = Some (Some (E_SAMO_Access_Fault tt), s).
Proof.
  intros Hmatch Halign Hresv.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hresv |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:112.56-112.57" >>=
          (fun _ : true = true =>
             returnM (andb (PMA_writable (override_PMA rattr pbmt))
                        (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone))))
    with (returnM (andb (PMA_writable (override_PMA rattr pbmt))
                    (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hresv.
  replace (generic_neq RsrvNone RsrvNone) with false by (vm_compute; reflexivity).
  rewrite andb_false_r.
  replace (get_config_print_pma tt) with false by (vm_compute; reflexivity).
  cbn match.
  apply exec_returnM.
Qed.

(* pmpCheck user grant for a StoreConditional: pmpCheckRWX checks W, exactly
   like Store Data -- clone of exec_pmpCheck_user_grant_store. *)
Lemma exec_pmpCheck_user_grant_storecon (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (StoreConditional Data) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HW.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (StoreConditional Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* effectivePrivilege for StoreConditional below Machine (MPRV clear): identity. *)
Lemma exec_effectivePrivilege_storecon_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (StoreConditional Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* phys_access_check for a prohibited StoreConditional: pmp grants, PMA
   fails on reservability -> Some (E_SAMO_Access_Fault). *)
Lemma exec_phys_access_check_storecon_fail (p : Privilege) (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) s :
  exec (pmpCheck (Physaddr addr) 4 (StoreConditional Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) = RsrvNone ->
  exec (phys_access_check (StoreConditional Data) pbmt p (Physaddr addr) 4 true) s
    = Some (Some (E_SAMO_Access_Fault tt), s).
Proof.
  intros Hpmp Hmatch Halign Hresv.
  unfold phys_access_check.
  rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_pmaCheck_ram_storecon_fail addr pbmt region s Hmatch Halign Hresv)).
  cbn match. apply exec_returnM.
Qed.

Section GenVMemWriteStoreconFail4.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable dw : mword (8 * 4).
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let W' : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Access_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (StoreConditional Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (StoreConditional Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.
  Hypothesis Hmatchrsv : match_reservation (bits_of_physaddr (Physaddr pa)) = false.

  Lemma exec_vmem_write_addr_storecon_fail :
    exec (vmem_write_addr (Virtaddr a) 4 dw (StoreConditional Data) (andb aq rl) rl true) s
      = Some (Err W', s).
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
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W'), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        (* the SC assert (Bool.eqb res is_store_conditional) *)
        assert (Hsc : exec (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W'), s))
        end.
        { match goal with
          | |- execR (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) s = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          rewrite Hmatchrsv. cbn [negb andb].
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
          rewrite Hcp.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_storecon_nm (register_lookup mstatus s.(sregs)) p s Hmprv)). cbn beta.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_phys_access_check_storecon_fail p PBMT_PMA pa region s Hpmp Hmatch Hpalign Hresv)). cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_SAMO_Access_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.
End GenVMemWriteStoreconFail4.

Section GenExecStoreconFail4.
  Variable p : Privilege.
  Variable rs1 rs2 rd : mword 5.
  Variable a : mword 64.
  Variable dw : mword (8 * 4).
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  (* The rs2 source value is irrelevant to the fault; abstract it. *)
  Variable dw_src : mword 64.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let W' : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Access_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (StoreConditional Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (StoreConditional Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (StoreConditional Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.
  Hypothesis Hmatchrsv : match_reservation (bits_of_physaddr (Physaddr pa)) = false.
  Hypothesis Hrs2 : exec (rX_bits (Regidx rs2)) s = Some (dw_src, s).

  Lemma exec_vmem_write_storecon_fail :
    exec (vmem_write (Regidx rs1) (zeros' 64) 4
            (autocast (T := mword) (subrange_vec_dec dw_src (Z.sub (Z.mul 4 8) 1) 0))
            (StoreConditional Data) (andb aq rl) rl true) s
      = Some (Err W', s).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (StoreConditional Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (StoreConditional Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_storecon_fail p a
               (autocast (T := mword) (subrange_vec_dec dw_src (Z.sub (Z.mul 4 8) 1) 0))
               region s pa aq rl Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hresv Hmatchrsv).
    reflexivity.
  Qed.

  Lemma exec_execute_STORECON_fault :
    exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd))) s = Some (W', s).
  Proof.
    change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_STORECON.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ Hrs2).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_storecon_fail)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreconFail4.

(* ===================================================================== *)
(* translateAddr TLB-hit wrappers for LoadReserved / StoreConditional.     *)
(* Clones of UmodeData's load/store wrappers with the access swapped; the  *)
(* only differences are effectivePrivilege, is_shadow_stack, and the       *)
(* translate access argument.                                              *)
(* ===================================================================== *)

Lemma exec_is_shadow_stack_loadres s :
  exec (is_shadow_stack_access (LoadReserved Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

Lemma exec_is_shadow_stack_storecon s :
  exec (is_shadow_stack_access (StoreConditional Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

Section UTranslateLrscWrappers.
  Context (ent : TLB_Entry) (vpn : mword 27).

  Lemma exec_translateAddr_loadres_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    (forall (mxr do_sum : bool) s0,
       exec (check_PTE_permission (LoadReserved Data) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
         = Some (PTE_Check_Success tt, s0)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (LoadReserved Data) = (None : option (mword 64)) ->
    (forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0)) ->
    match_TLB_Entry ent (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = true ->
    register_lookup cur_privilege s.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    exec (translateAddr (Virtaddr va) (LoadReserved Data)) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hchk Hupd Hpbmt Hmatch Hcp HSXL HMPRV Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_effectivePrivilege_loadres_nm _ _ s HMPRV)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_loadres s)).
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
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_hit_u_acc (LoadReserved Data) ent vpn Hchk Hupd Hpbmt Hmatch
                  _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

  Lemma exec_translateAddr_storecon_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    (forall (mxr do_sum : bool) s0,
       exec (check_PTE_permission (StoreConditional Data) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
         = Some (PTE_Check_Success tt, s0)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (StoreConditional Data) = (None : option (mword 64)) ->
    (forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0)) ->
    match_TLB_Entry ent (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = true ->
    register_lookup cur_privilege s.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    exec (translateAddr (Virtaddr va) (StoreConditional Data)) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hchk Hupd Hpbmt Hmatch Hcp HSXL HMPRV Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_effectivePrivilege_storecon_nm _ _ s HMPRV)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_storecon s)).
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
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_hit_u_acc (StoreConditional Data) ent vpn Hchk Hupd Hpbmt Hmatch
                  _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.
End UTranslateLrscWrappers.

(* ===================================================================== *)
(* transform_effective_address (identity) for LoadReserved/StoreConditional. *)
(* Clones of UmodeData's load/store EA-transform leaf stack.                *)
(* ===================================================================== *)

Lemma exec_is_pmm_applicable_loadres_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (LoadReserved Data) User) s = Some (true, s).
Proof.
  intro Hmxr.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (LoadReserved Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (LoadReserved Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (LoadReserved Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_returnM _ s). rewrite Hmxr. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_is_pmm_applicable_storecon_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (StoreConditional Data) User) s = Some (true, s).
Proof.
  intro Hmxr.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (StoreConditional Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (StoreConditional Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (StoreConditional Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_returnM _ s). rewrite Hmxr. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_loadres_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmlen (LoadReserved Data) User) s = Some (0, s).
Proof.
  intros Hmxr HES Hsenv Hmenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_loadres_u s Hmxr)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_user s HES Hsenv Hmenv)).
  apply exec_returnM.
Qed.

Lemma exec_get_pmlen_storecon_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmlen (StoreConditional Data) User) s = Some (0, s).
Proof.
  intros Hmxr HES Hsenv Hmenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_storecon_u s Hmxr)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_user s HES Hsenv Hmenv)).
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_loadres_u (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4) ->
  exec (transform_effective_address (Virtaddr ea) (LoadReserved Data)) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hmode.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_loadres_nm _ _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_loadres_u s Hmxr HES Hsenv Hmenv)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_translationMode_U_sv39 (register_lookup satp s.(sregs)) s
                HSXL eq_refl Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  rewrite <- (pm_transform_VA_0 ea) at 2.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_storecon_u (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4) ->
  exec (transform_effective_address (Virtaddr ea) (StoreConditional Data)) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hmode.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_storecon_nm _ _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_storecon_u s Hmxr HES Hsenv Hmenv)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_translationMode_U_sv39 (register_lookup satp s.(sregs)) s
                HSXL eq_refl Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  rewrite <- (pm_transform_VA_0 ea) at 2.
  apply exec_returnM.
Qed.
