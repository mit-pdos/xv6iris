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
Require Import WpGpr WpLoad MemData4 SmodeCore UmodeData.
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
