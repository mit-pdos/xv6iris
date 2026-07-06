(* WpAmo.v -- S-mode support for xv6's amoswap.w.aq (acquire()'s atomic
   test-and-set).  Three layers:
     1. decode: the A-extension gate [currentlyEnabled Ext_Zaamo] reduces via
        a misa.A hypothesis; [amodec] decodes acquire's 0x0cf4a7af.
     2. exec: Atomic-access clones of the width-4 (Store Data)/(Load Data)
        translation + PMP/PMA + read/write stacks of WpPushOffMem/WpSmodeGpr
        ((Atomic (AMOSWAP, Data, Data)) checks R&&W everywhere, the read is
        Read_RISCV_reserved_acquire, the write Write_RISCV_conditional), and
        the whole-instruction [exec_execute_AMOSWAP_4_gpr_S] (+ _walk).
     3. the stored/loaded value shims ([amoswap_stored]/[amoswap_loaded])
        atop the whole-instruction exec fact, consumed by WpLockLeaves.v's
        CSL-lock-invariant amoswap step (whose decode field now also
        provides misa.A, threaded from hw_config); that step mirrors
        wp_csw_s (TLB hit and walk data paths) plus wp_gpr_write_s_config's
        rd update. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpPushOffMem.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Part 1 -- the A-extension enable gate.                                 *)
(* ===================================================================== *)





(* ===================================================================== *)
(* Part 2 -- decode of acquire()'s [amoswap.w.aq a5,a5,(s1)] (0x0cf4a7af). *)
(* ===================================================================== *)

Definition amoswap_acq_ast : instruction :=
  AMO (AMOSWAP, true, false, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4,
       Regidx (mword_of_int 15)).

Lemma amodec s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  eq_vec (_get_Misa_A (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode (mword_of_int 0x0cf4a7af : mword 32)) s
  = Some (amoswap_acq_ast, s).
Proof.
  intros Hpriv HmisaA.
  decode_pause_prefix s Hpriv.
  (* refold the exec_bind expansion, then vm-normalize the (read-free up to
     the single misa RegRead) remaining decoder into its free-monad tree *)
  rewrite <- exec_bind.
  match goal with |- exec ?d ?st = _ =>
    let r := eval vm_compute in d in change_no_check (exec d st) with (exec r st) end.
  cbn [exec].
  (* the A-extension gate: the stuck test IS (convertibly) misa.A = 1 *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (symmetry; exact HmisaA) end.
  cbn [exec].
  repeat f_equal;
    first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(* Part 3 -- Atomic-access ((Atomic (AMOSWAP, Data, Data))) exec layer:   *)
(* clones of the width-4 (Store Data)/(Load Data) stacks with the AMO     *)
(* access type (PMP checks R&&W, PMA additionally checks atomic support,  *)
(* the read kind is Read_RISCV_reserved_acquire, the write kind           *)
(* Write_RISCV_conditional).                                              *)
(* ===================================================================== *)

(* Supervisor PMP grant for an AMO (R && W bits). *)
Lemma exec_pmpCheck_supervisor_grant_amo (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Atomic (AMOSWAP, Data, Data)) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR HW.
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
                            (Atomic (AMOSWAP, Data, Data))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

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

Lemma exec_effectivePrivilege_amo_S (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Atomic (AMOSWAP, Data, Data)) m Supervisor) s = Some (Supervisor, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_is_shadow_stack_amo s :
  exec (is_shadow_stack_access (Atomic (AMOSWAP, Data, Data))) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma exec_is_pmm_applicable_amo_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Atomic (AMOSWAP, Data, Data)) Supervisor) s = Some (true, s).
Proof.
  intro Hmxr. unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite Hmxr. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_amo_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Atomic (AMOSWAP, Data, Data)) Supervisor) s = Some (0, s).
Proof.
  intros Hmxr Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_amo_S s Hmxr)).
  cbn match.
  assert (Hgp : exec (get_pmm Supervisor) s
          = Some (pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_amo_S (ea : mword 64) (satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
    = Some (pm_transform_VA (Virtaddr ea) 0, s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_S _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_amo_S s Hmxr Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* Part 4 -- Sv39 translation of the AMO data address in the 1GB identity *)
(* superpage: TLB HIT (state-preserving) and one-PTE WALK (fills the TLB), *)
(* cloned from the (Store Data) chain in WpSmodeGpr.v.                     *)
(* ===================================================================== *)

Section AmoTranslate.
  Context (root_ppn : mword 44).

  Lemma exec_pt_walk_amo_super (vpn : mword 27) (mxr do_sum : bool)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 vpn (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (sdata_ppn_out vpn) (autocast (T := mword) pte_super)
                    (Physaddr (pte_paddr root_ppn)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold pt_walk, Zwf_guarded.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (pte_paddr root_ppn : mword 64) by
        (unfold pte_paddr; rewrite Hvpn2; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S (pte_paddr root_ppn) region pte_super s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0))
                           (ext_bits_of_PTE pte_super)) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    match goal with |- context[pte_is_non_leaf ?f] =>
      replace (pte_is_non_leaf f) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    match goal with |- context[neq_vec ?a ?b] =>
      replace (neq_vec a b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    assert (Hchk : exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0)) (ext_bits_of_PTE pte_super) tt) s
                   = Some (PTE_Check_Success tt, s))
      by (destruct mxr, do_sum; vm_compute; reflexivity).
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hchk. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (2 >? 0) with true. cbv iota beta.
    match goal with |- context[eq_vec (_get_PTE_Ext_N ?e) ?b] =>
      replace (eq_vec (_get_PTE_Ext_N e) b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    unfold sdata_ppn_out.
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  Lemma exec_translate_TLB_miss_amo (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid root_ppn vpn
            (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_amo_super vpn mxr do_sum region menvcfg0 s
                  Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_store_super root_ppn vpn asid s Hmvpn Hmppn)).
    apply exec_returnm.
  Qed.

  Lemma exec_translate_amo_walk (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid root_ppn vpn
            (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss_data vpn asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_amo vpn mxr do_sum asid region menvcfg0 s
             Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
  Qed.

  Lemma exec_translateAddr_amo_walk (a : mword 64) (vpn : mword 27)
        (region : PMA_Region) (menvcfg0 satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (sdata_ppn_out vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))))).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hppn Hasid Hcanon Hvpn_def Hident
           Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_amo_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_amo s)).
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
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_amo_walk vpn _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  Lemma exec_translate_TLB_hit_amo_super (vpn : mword 27) (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
            tt (tlb_hash (__id 39) vpn) (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[check_PTE_permission ?ac ?pr ?mx ?ds ?fl ?ex ?ep] =>
      assert (Hchk : exec (check_PTE_permission ac pr mx ds fl ex ep) s = Some (PTE_Check_Success tt, s))
        by (destruct mxr, do_sum; vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    assert (Hpbmt : exec (tlb_get_pbmt (pw_tlb_entry root_ppn (mword_of_int 0))) s = Some (PBMT_PMA, s))
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hpbmt). apply exec_returnm.
  Qed.

  Lemma exec_translate_amo_hit (vpn : mword 27) (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_data root_ppn vpn tlbvec s Htlb Hvec Hmask)).
    cbn match.
    apply exec_translate_TLB_hit_amo_super.
  Qed.

  Lemma exec_translateAddr_amo_hit (a : mword 64) (vpn : mword 27)
        (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hasid Hcanon Hvpn_def Hident Htlb Hvec Hmask.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_amo_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_amo s)).
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
               (exec_translate_amo_hit vpn _ _ _ tlbvec s Htlb Hvec Hmask)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

End AmoTranslate.

(* ===================================================================== *)
(* Part 5 -- the AMO's physical memory operations: an acquire-kind read   *)
(* and a conditional-kind write (both to RAM, PMP/PMA-checked with the    *)
(* Atomic access type), and the whole-instruction execute lemmas.         *)
(* ===================================================================== *)

Lemma run_read_ram_resacq_4_pin (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram rv64d_types.Read_RISCV_reserved_acquire (Physaddr addr) 4 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_resacq_4 (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rv64d_types.Read_RISCV_reserved_acquire (Physaddr addr) 4 false) s
  = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_resacq_4_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
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

Lemma exec_checked_mem_read_ram_amo_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Atomic (AMOSWAP, Data, Data)) pbmt Supervisor (Physaddr addr) 4 true false true false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_amo addr 4 s HA Hord Hrange HR HW)).
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resacq_4 addr w s Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_amo_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (Atomic (AMOSWAP, Data, Data)) pbmt (Physaddr addr) 4 true false true)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_S m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta.
      rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_amo_4_S with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_write_ram_cond_4 (addr : mword 64) (data : bv 32) s :
  exec (write_ram rv64d_types.Write_RISCV_conditional (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data)).
Proof.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind]. cbn match. reflexivity.
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

Lemma exec_checked_mem_write_ram_amo_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  exec (checked_mem_write (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt Supervisor tt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data)).
Proof.
  intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_amo addr 4 s HA Hord Hrange HR HW)).
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_4 addr data s)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_amo_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_write_value (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data)).
Proof.
  intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_S m s Hmprv)).
  unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_amo_4_S pbmt addr region data s HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* Part 6 -- whole-instruction execute of [amoswap.w.aq rd, rs2, (rs1)]:  *)
(* translate once (TLB hit / walk), read the old 32-bit value w, write    *)
(* the truncated rs2, set rd := sext64 w.                                 *)
(* ===================================================================== *)

Section ExecAmoGS4.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable w : mword 32.
  Variable s : mstate.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := a8.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Atomic (AMOSWAP, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr_S :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval))
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
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_amo_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
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
              (exec_mem_read_amo_4_S PBMT_PMA pa region w (register_lookup mstatus s.(sregs)) s
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hbytes eq_refl Hmprv Hcp)).
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
              (exec_mem_write_value_amo_4_S PBMT_PMA pa region _ (register_lookup mstatus s.(sregs)) s
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw eq_refl Hmprv Hcp)).
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

(* The WALK variant: translateAddr fills the TLB (state change s -> s');
   the register read, memory read and write all happen at s' (whose gprs,
   CSRs and memory coincide with s's -- only [tlb] differs). *)
Section ExecAmoGS4walk.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable w : mword 32.
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := a8.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Atomic (AMOSWAP, Data, Data))) s
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
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr_S_walk :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s.(mem) pa 4 storeval))
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
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_amo_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s')).
    cbn beta match.
    replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
    cbv iota.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')).
    cbn beta. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_amo_4 pa s' Hpalign)).
    cbn match.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_read_amo_4_S PBMT_PMA pa region w (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr
                 (fun j Hj => Hbytes j Hj) eq_refl Hmprv' Hcp')).
    cbn match. rewrite execR_returnR. cbn match.
    cbn zeta. cbn match.
    replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
    rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_value_amo_4_S PBMT_PMA pa region _ (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw eq_refl Hmprv' Hcp')).
    cbn match.
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
End ExecAmoGS4walk.

(* ===================================================================== *)
(* Part 7 -- the stored/loaded value shims for [amoswap.w.aq rd, rs2,     *)
(* (rs1)] on a 4-byte RAM cell: the on-the-wire 32-bit store value and    *)
(* the sign-extended 64-bit load value. The whole-step WP built from      *)
(* these (mirroring wp_csw_s's data TLB hit + walk, plus a rd write       *)
(* mirroring wp_gpr_write_s_config's) now lives in WpLockLeaves.v as the  *)
(* CSL-lock-invariant leaves (wp_amoswap_lockinv and twin).                *)
(* ===================================================================== *)

Definition amoswap_stored (v : mword 64) : mword 32 :=
  sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) v).

Definition amoswap_loaded (w : mword 32) : mword 64 :=
  sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)).

