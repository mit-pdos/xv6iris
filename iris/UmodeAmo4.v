(* UmodeAmo4.v -- U-mode width-4 ATOMIC (AMOSWAP.W) execute lemma.

   Thin U-mode instantiation of the mode-neutral AMO tower in MemAmo4: we
   supply the User-privilege pmpCheck grant (R && W), the Sv39 TLB-hit
   translation at the Atomic access type (pa = u_pa ent ea vpn, no A/D
   write-back), and the identity effective-address transform (pmlen 0),
   then discharge the generic exec_execute_AMOSWAP_4_gpr.  Its hypothesis
   set is the union of the U-mode LOAD read-side and STORE write-side
   facts, plus pma_allows_atomic_op. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import WpGpr.
Require Import UmodeFetch MemAmo4 UmodeData.
Require Import CommonWalk.
Require Import RiscvPtsto.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_pmpCheck_user_grant_amo (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Atomic (AMOSWAP, Data, Data)) User) s = Some (None, s).
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

Lemma exec_is_shadow_stack_amo s :
  exec (is_shadow_stack_access (Atomic (AMOSWAP, Data, Data))) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma exec_is_pmm_applicable_amo_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Atomic (AMOSWAP, Data, Data)) User) s = Some (true, s).
Proof.
  intro Hmxr.
  unfold is_pmm_applicable.
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
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_returnM _ s). rewrite Hmxr. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_amo_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmlen (Atomic (AMOSWAP, Data, Data)) User) s = Some (0, s).
Proof.
  intros Hmxr HES Hsenv Hmenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_amo_u s Hmxr)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_user s HES Hsenv Hmenv)).
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_amo_u (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4) ->
  exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hmode.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm _ _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_amo_u s Hmxr HES Hsenv Hmenv)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_translationMode_U_sv39 (register_lookup satp s.(sregs)) s
                HSXL eq_refl Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  rewrite <- (pm_transform_VA_0 ea) at 2.
  apply exec_returnM.
Qed.

Section AmoWrap.
  Context (ent : TLB_Entry) (vpn : mword 27).

  Lemma exec_translateAddr_amo_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    (forall (mxr do_sum : bool) s0,
       exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
         = Some (PTE_Check_Success tt, s0)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (Atomic (AMOSWAP, Data, Data)) = (None : option (mword 64)) ->
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
    exec (translateAddr (Virtaddr va) (Atomic (AMOSWAP, Data, Data))) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hchk Hupd Hpbmt Hmatch Hcp HSXL HMPRV Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_effectivePrivilege_amo_nm _ _ s HMPRV)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
               (exec_translate_hit_u_acc (Atomic (AMOSWAP, Data, Data)) ent vpn Hchk Hupd Hpbmt Hmatch
                  _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

End AmoWrap.

(* ===================================================================== *)
(* U-mode AMO data-EA WALK-FILL translateAddr wrapper (cold data TLB).     *)
(* AMO twin of exec_translateAddr_load_walk_u; acc = Atomic(AMOSWAP,..).   *)
(* ===================================================================== *)
Lemma exec_translateAddr_amo_walk_u
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
  (forall (mxr' do_sum' : bool) s0,
     exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr' do_sum'
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Atomic (AMOSWAP, Data, Data)) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Atomic (AMOSWAP, Data, Data))) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va), PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_amo_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (Atomic (AMOSWAP, Data, Data)) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


Lemma exec_translateAddr_amo_walk_u_nomatch
    (ent' : TLB_Entry)
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
  (forall (mxr' do_sum' : bool) s0,
     exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr' do_sum'
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = false ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Atomic (AMOSWAP, Data, Data)) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Atomic (AMOSWAP, Data, Data))) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va), PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_amo_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user_nomatch vpn root pte2 pte1 pte0 (Atomic (AMOSWAP, Data, Data)) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 ent' tlbvec s
                  Hmisa Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


(* ===================================================================== *)
(* U-mode width-4 register-generic AMOSWAP.W (rd <> x0).                 *)
(* Hypotheses = the LOAD read-side (Hread/Hc/Hsig/Hhr/Hbytes/HpmpR)      *)
(* unioned with the STORE write-side (Hwrite/Hhw/HpmpW) plus Hamo.       *)
(* ===================================================================== *)
Section VAU4.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable rs2 rs1 rd : mword 5.
  Variable w : mword 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let pa := u_pa ent ea vpn.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).

  (* stored-entry leaf facts at the Atomic access type *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Atomic (AMOSWAP, Data, Data))
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch_tlb : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.
  (* machine-state pins *)
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis HES : exec (currentlyEnabled Ext_S) s = Some (true, s).
  Hypothesis Hsenv : register_lookup senvcfg s.(sregs) = mword_of_int 0.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = MENVCFG_S.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) (register_lookup satp s.(sregs)) : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = Some ent.
  (* va geometry at the effective address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side pmp facts at the translated pa (both R and W) *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  (* physical-side pma / memory facts *)
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
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
  Hypothesis Hrd : uint rd <> 0.

  Lemma exec_execute_AMOSWAP_4_U :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval) s.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    assert (Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr ea, s)).
    { apply exec_transform_effective_address_amo_u; assumption. }
    assert (Htr : exec (translateAddr (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
                  = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s)).
    { exact (exec_translateAddr_amo_hit_u ent vpn ea
               (register_lookup satp s.(sregs)) (register_lookup tlb s.(sregs)) s
               Hchk Hupd Hpbmt Hmatch_tlb Hcp HSXL Hmprv eq_refl Hsatpmode Hasid
               eq_refl Hvec Hcanon Hvpn_def). }
    assert (Hpmp : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) User) s = Some (None, s)).
    { exact (exec_pmpCheck_user_grant_amo pa 4 s HpmpA Hpmp_ord Hrange HpmpR HpmpW). }
    exact (exec_execute_AMOSWAP_4_gpr rs2 rs1 rd region w s User ea pa
             Hrd Hcp Hmprv Halign Htea Htr Hpmp Hpmam Hpalign Hread Hwrite Hamo
             Hc Hsig Hhr Hhw Hdev Hbytes).
  Qed.
End VAU4.

(* ===================================================================== *)
(* U-mode AMOSWAP.W with a COLD data TLB: the EA translate walks the page  *)
(* table and fills the TLB (s -> s'), then the atomic read+write runs at   *)
(* s'.  Walk twin of exec_execute_AMOSWAP_4_U.                             *)
(* ===================================================================== *)
Section VAU4Walk.
  Context (vpn : mword 27) (root : mword 44).
  Variable rs2 rs1 rd : mword 5.
  Variable w : mword 32.
  Variable region : PMA_Region.
  Variable pte2 pte1 pte0 : mword 64.
  Variable s : mstate.
  Variable satp0 : mword 64.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let tlbvecF := vec_update_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn)
                   (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))).
  Let s' := set_reg s tlb tlbvecF.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let pa := u_walk_pa pte0 ea.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).

  (* walk PTE structure *)
  Hypothesis H2i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0).
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0).
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  Hypothesis H0i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0).
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false.
  Hypothesis Hchk : forall (mxr' do_sum' : bool) s0,
     exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr' do_sum'
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0).
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false.
  Hypothesis Hupd : update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Atomic (AMOSWAP, Data, Data)) = None.
  Hypothesis Hrd2 : exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s).
  Hypothesis Hrd1 : exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s).
  Hypothesis Hrd0 : exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s).
  (* machine-state pins at s *)
  Hypothesis Hmisa : register_lookup misa s.(sregs) = MISA_C.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis HES : exec (currentlyEnabled Ext_S) s = Some (true, s).
  Hypothesis Hsenv : register_lookup senvcfg s.(sregs) = mword_of_int 0.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = MENVCFG_S.
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hroot : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = None.
  (* va geometry at the effective address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side pmp facts at s (transported to s') *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  (* physical-side pma / memory facts *)
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hram : addr_is_ram pa.
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).
  Hypothesis Hrd : uint rd <> 0.

  Lemma exec_execute_AMOSWAP_4_U_walk :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s'.(mem) pa 4 storeval) s'.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    assert (Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr ea, s)).
    { apply exec_transform_effective_address_amo_u;
        [ exact Hcp | exact Hmprv | exact Hmxr | exact HSXL | exact HES | exact Hsenv | exact Hmenv
        | rewrite Hsatp; exact Hsatpmode ]. }
    assert (Htr : exec (translateAddr (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
                  = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s')).
    { exact (exec_translateAddr_amo_walk_u vpn root pte2 pte1 pte0 ea satp0 MENVCFG_S
               (register_lookup tlb s.(sregs)) s
               H2i H2nl H1i H1nl H0i H0nl Hchk H0N Hmisa Hcp HSXL Hmprv Hsatp Hsatpmode
               Hasid Hroot eq_refl Hvec Hupd Hrd2 Hrd1 Hrd0 Hmenv
               ltac:(vm_compute; reflexivity) Hcanon Hvpn_def). }
    assert (Hcp' : register_lookup cur_privilege s'.(sregs) = User)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hcp | vm_compute; reflexivity ]).
    assert (Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1" : mword 1) = false)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hmprv | vm_compute; reflexivity ]).
    assert (HpmpA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpA | vm_compute; reflexivity ]).
    assert (Hpmp_ord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hpmp_ord | vm_compute; reflexivity ]).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hrange | vm_compute; reflexivity ]).
    assert (HpmpR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpR | vm_compute; reflexivity ]).
    assert (HpmpW' : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpW | vm_compute; reflexivity ]).
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hpmam | vm_compute; reflexivity ]).
    assert (Hbytes' : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j))
      by (unfold s', set_reg; cbn [mem]; exact Hbytes).
    assert (Hcp'p : register_lookup cur_privilege s'.(sregs) = User) by exact Hcp'.
    assert (Hpmp' : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) User) s' = Some (None, s'))
      by exact (exec_pmpCheck_user_grant_amo pa 4 s' HpmpA' Hpmp_ord' Hrange' HpmpR' HpmpW').
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    assert (Lhtif' : register_lookup htif_tohost_base s'.(sregs) = None)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hhtif | vm_compute; reflexivity ]).
    exact (exec_execute_AMOSWAP_4_gpr_walk rs2 rs1 rd region w s s' User ea pa
             Hrd Hcp' Hmprv' Halign Htea Htr Hpmp' Hpmam' Hpalign Hread Hwrite Hamo
             (within_clint_false pa 4 s' Hnc ltac:(lia))
             (within_sig_false pa 4 s' Hns ltac:(lia))
             (within_htif_false pa 4 s' Lhtif')
             (within_htif_false pa 4 s' Lhtif' : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s'))
             (addr_is_ram_not_dev _ Hram) Hbytes').
  Qed.
End VAU4Walk.


Section VAU4WalkNomatch.
  Context (vpn : mword 27) (root : mword 44).
  Variable rs2 rs1 rd : mword 5.
  Variable w : mword 32.
  Variable region : PMA_Region.
  Variable pte2 pte1 pte0 : mword 64.
  Variable s : mstate.
  Variable satp0 : mword 64.
  Variable ent' : TLB_Entry.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let tlbvecF := vec_update_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn)
                   (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))).
  Let s' := set_reg s tlb tlbvecF.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let pa := u_walk_pa pte0 ea.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).

  (* walk PTE structure *)
  Hypothesis H2i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0).
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0).
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  Hypothesis H0i : forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0).
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false.
  Hypothesis Hchk : forall (mxr' do_sum' : bool) s0,
     exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) User mxr' do_sum'
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0).
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false.
  Hypothesis Hupd : update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (Atomic (AMOSWAP, Data, Data)) = None.
  Hypothesis Hrd2 : exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s).
  Hypothesis Hrd1 : exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s).
  Hypothesis Hrd0 : exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s).
  (* machine-state pins at s *)
  Hypothesis Hmisa : register_lookup misa s.(sregs) = MISA_C.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis HES : exec (currentlyEnabled Ext_S) s = Some (true, s).
  Hypothesis Hsenv : register_lookup senvcfg s.(sregs) = mword_of_int 0.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = MENVCFG_S.
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hroot : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = Some ent'.
  Hypothesis Hnm : match_TLB_Entry ent' (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = false.
  (* va geometry at the effective address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side pmp facts at s (transported to s') *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  (* physical-side pma / memory facts *)
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hram : addr_is_ram pa.
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte w j).
  Hypothesis Hrd : uint rd <> 0.

  Lemma exec_execute_AMOSWAP_4_U_walk_nomatch :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s'.(mem) pa 4 storeval) s'.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    assert (Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s = Some (Virtaddr ea, s)).
    { apply exec_transform_effective_address_amo_u;
        [ exact Hcp | exact Hmprv | exact Hmxr | exact HSXL | exact HES | exact Hsenv | exact Hmenv
        | rewrite Hsatp; exact Hsatpmode ]. }
    assert (Htr : exec (translateAddr (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
                  = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s')).
    { exact (exec_translateAddr_amo_walk_u_nomatch ent' vpn root pte2 pte1 pte0 ea satp0 MENVCFG_S
               (register_lookup tlb s.(sregs)) s
               H2i H2nl H1i H1nl H0i H0nl Hchk H0N Hmisa Hcp HSXL Hmprv Hsatp Hsatpmode
               Hasid Hroot eq_refl Hvec Hnm Hupd Hrd2 Hrd1 Hrd0 Hmenv
               ltac:(vm_compute; reflexivity) Hcanon Hvpn_def). }
    assert (Hcp' : register_lookup cur_privilege s'.(sregs) = User)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hcp | vm_compute; reflexivity ]).
    assert (Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1" : mword 1) = false)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hmprv | vm_compute; reflexivity ]).
    assert (HpmpA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpA | vm_compute; reflexivity ]).
    assert (Hpmp_ord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hpmp_ord | vm_compute; reflexivity ]).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hrange | vm_compute; reflexivity ]).
    assert (HpmpR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpR | vm_compute; reflexivity ]).
    assert (HpmpW' : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact HpmpW | vm_compute; reflexivity ]).
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hpmam | vm_compute; reflexivity ]).
    assert (Hbytes' : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j))
      by (unfold s', set_reg; cbn [mem]; exact Hbytes).
    assert (Hcp'p : register_lookup cur_privilege s'.(sregs) = User) by exact Hcp'.
    assert (Hpmp' : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) User) s' = Some (None, s'))
      by exact (exec_pmpCheck_user_grant_amo pa 4 s' HpmpA' Hpmp_ord' Hrange' HpmpR' HpmpW').
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    assert (Lhtif' : register_lookup htif_tohost_base s'.(sregs) = None)
      by (unfold s', set_reg; cbn [sregs]; rewrite irrelevant_register_set; [ exact Hhtif | vm_compute; reflexivity ]).
    exact (exec_execute_AMOSWAP_4_gpr_walk rs2 rs1 rd region w s s' User ea pa
             Hrd Hcp' Hmprv' Halign Htea Htr Hpmp' Hpmam' Hpalign Hread Hwrite Hamo
             (within_clint_false pa 4 s' Hnc ltac:(lia))
             (within_sig_false pa 4 s' Hns ltac:(lia))
             (within_htif_false pa 4 s' Lhtif')
             (within_htif_false pa 4 s' Lhtif' : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s'))
             (addr_is_ram_not_dev _ Hram) Hbytes').
  Qed.
End VAU4WalkNomatch.

