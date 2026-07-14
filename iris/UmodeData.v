(* UmodeData.v -- U-mode DATA access primitives: the PMP TOR-entry-0
   grants for loads and stores at User privilege, and the 8-byte physical
   data read.  (The store write path and narrower widths follow as the
   execute-family lemmas need them.)  Straight clones of the S-mode /
   M-mode versions: below Machine the per-entry PMP logic is identical,
   only the RWX bit consulted differs per access.                        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import CommonWalk.
Require Import WpLoad WpGpr WpGprStore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 PMP grants at User for data accesses (TOR entry 0 covering RAM).    *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant_load (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load Data) User) s = Some (None, s).
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
                            (Load Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_pmpCheck_user_grant_store (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Store Data) User) s = Some (None, s).
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
                            (Store Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 effectivePrivilege for data accesses below Machine: MPRV clear.     *)
(* ===================================================================== *)

Lemma exec_effectivePrivilege_load_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Load Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_effectivePrivilege_store_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Store Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §3 The 8-byte physical data read at User.                              *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_ram_8_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr 8 s HA Hord Hrange HR)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (pmaCheck (Physaddr addr) 8 (Load Data) pbmt false) s
                     = Some (None, s))).
      2:{ unfold pmaCheck.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
          rewrite Hmatch.
          destruct region as [rbase rsize rattr rdtree].
          cbn [PMA_Region_attributes] in Hread |- *.
          rewrite Halign. cbn [Riscv.rv64d.not negb].
          rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
          cbn match beta.
          change (assert_exp' true "sys/mem.sail:105.61-105.62" >>=
                  (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
            with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
          rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
          rewrite Hread. cbn match.
          apply exec_returnM. }
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §4 Data-side translation: the acc-GENERIC TLB-hit chain (clone of      *)
(*    UmodeFetch's UTranslateHit at an arbitrary access type) and the     *)
(*    translateAddr wrappers for user loads and stores.                   *)
(* ===================================================================== *)
Require Import UmodeFetch.

Lemma exec_is_shadow_stack_load s :
  exec (is_shadow_stack_access (Load Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

Lemma exec_is_shadow_stack_store s :
  exec (is_shadow_stack_access (Store Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

Section UTranslateHitAcc.
  Context (acc : MemoryAccessType mem_payload).
  Context (ent : TLB_Entry) (vpn : mword 27).

  (* the acc-permission check succeeds on this entry's PTE *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s,
    exec (check_PTE_permission acc User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
      = Some (PTE_Check_Success tt, s).
  (* A (and D as needed for the acc) preset: no PTE write-back on the hit *)
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) acc
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s, exec (tlb_get_pbmt ent) s = Some (PBMT_PMA, s).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.

  Lemma exec_translate_TLB_hit_u_acc (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn acc User mxr do_sum
            tt (tlb_hash (__id 39) vpn) ent) s
      = Some (Ok (tlb_get_ppn 39 ent vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk mxr do_sum s)). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd' : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (symmetry; exact Hupd) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd'). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (Hpbmt s)). apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_hit_u_acc (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) vpn) s
      = Some (Some (tlb_hash (__id 39) vpn, ent), s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    rewrite Hmatch.
    apply exec_returnm.
  Qed.

  Lemma exec_translate_hit_u_acc (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn acc User mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 ent vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_u_acc tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_u_acc.
  Qed.

End UTranslateHitAcc.

Section UTranslateDataWrappers.
  Context (ent : TLB_Entry) (vpn : mword 27).

  (* the translateAddr wrapper for a user LOAD through the hit *)
  Lemma exec_translateAddr_load_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    (forall (mxr do_sum : bool) s0,
       exec (check_PTE_permission (Load Data) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
         = Some (PTE_Check_Success tt, s0)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (Load Data) = (None : option (mword 64)) ->
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
    exec (translateAddr (Virtaddr va) (Load Data)) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hchk Hupd Hpbmt Hmatch Hcp HSXL HMPRV Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_effectivePrivilege_load_nm _ _ s HMPRV)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_hit_u_acc (Load Data) ent vpn Hchk Hupd Hpbmt Hmatch
                  _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

  (* the translateAddr wrapper for a user STORE through the hit *)
  Lemma exec_translateAddr_store_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    (forall (mxr do_sum : bool) s0,
       exec (check_PTE_permission (Store Data) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
         = Some (PTE_Check_Success tt, s0)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (Store Data) = (None : option (mword 64)) ->
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
    exec (translateAddr (Virtaddr va) (Store Data)) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hchk Hupd Hpbmt Hmatch Hcp HSXL HMPRV Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_effectivePrivilege_store_nm _ _ s HMPRV)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_hit_u_acc (Store Data) ent vpn Hchk Hupd Hpbmt Hmatch
                  _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

End UTranslateDataWrappers.

(* ===================================================================== *)
(* §4c Data-side WALK-FILL translateAddr wrappers (load / store, in the    *)
(* match and colliding-slot forms).  Each is the acc-generic wrapper over   *)
(* the shared, acc-generic walk core [exec_translate_walk_user].  These are *)
(* the data-EA twins of [exec_translateAddr_fetch_walk_u].                  *)
(* ===================================================================== *)
Lemma exec_translateAddr_load_walk_u
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
     exec (check_PTE_permission (Load Data) User mxr' do_sum'
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (Load Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

Lemma exec_translateAddr_store_walk_u
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
     exec (check_PTE_permission (Store Data) User mxr' do_sum'
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (Store Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §5 The pointer-masking transform at User: PMM disabled (senvcfg = 0),  *)
(*    so the effective address passes through unchanged.                  *)
(* ===================================================================== *)

Lemma exec_is_pmm_applicable_load_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Load Data) User) s = Some (true, s).
Proof.
  intro Hmxr.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
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

Lemma exec_get_pmm_user s :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmm User) s = Some (PMM_Disabled, s).
Proof.
  intros HES Hsenv Hmenv.
  unfold get_pmm.
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  assert (Hrs : exec (read_senvcfg tt) s
                = Some (_update_SEnvcfg_SSE (mword_of_int 0)
                          (and_vec (_get_MEnvcfg_SSE MENVCFG_S)
                                   (_get_SEnvcfg_SSE (mword_of_int 0))), s)).
  { unfold read_senvcfg.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
    rewrite Hsenv Hmenv. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hrs).
  match goal with |- context[pmm_mode_backwards ?x] =>
    replace (pmm_mode_backwards x) with PMM_Disabled by (vm_compute; reflexivity) end.
  apply exec_returnM.
Qed.

Lemma exec_get_pmlen_load_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmlen (Load Data) User) s = Some (0, s).
Proof.
  intros Hmxr HES Hsenv Hmenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_load_u s Hmxr)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_user s HES Hsenv Hmenv)).
  apply exec_returnM.
Qed.

(* the pmlen-0 VA transform is the identity: sign-extending the full
   64-bit subrange returns the address unchanged *)
Require Import UptInv.

Lemma sext64_subrange63_id (x : mword 64) :
  sign_extend' 64 (subrange_vec_dec x (Z.sub (Z.sub xlen 0) 1) 0) = x.
Proof.
  change (Z.sub (Z.sub xlen 0) 1) with 63.
  rewrite subrange64_id.
  cbv [sign_extend' Operators_mwords.sign_extend exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed.
  rewrite bv_sign_extend_signed; [| apply N.leb_le; vm_compute; reflexivity].
  reflexivity.
Qed.

Lemma pm_transform_VA_0 (ea : mword 64) :
  pm_transform_VA (Virtaddr ea) 0 = Virtaddr ea.
Proof.
  unfold pm_transform_VA.
  f_equal.
  change (Z.sub (Z.sub xlen 0) 1) with (Z.sub (Z.sub xlen 0) 1).
  exact (sext64_subrange63_id ea).
Qed.

Lemma exec_transform_effective_address_load_u (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4) ->
  exec (transform_effective_address (Virtaddr ea) (Load Data)) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hmode.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_nm _ _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_load_u s Hmxr HES Hsenv Hmenv)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_translationMode_U_sv39 (register_lookup satp s.(sregs)) s
                HSXL eq_refl Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  rewrite <- (pm_transform_VA_0 ea) at 2.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §6 The virtual 8-byte user load: mem_read at User, and the             *)
(*    vmem_read_addr chain through the Sv39 hit translation.              *)
(* ===================================================================== *)

Lemma exec_mem_read_load_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_effectivePrivilege_load_nm _ _ s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match.
          apply exec_checked_mem_read_ram_8_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section VRU.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable a : mword 64.
  Variable v : bv 64.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := u_pa ent a vpn.
  Let data2 : mword (8*1*8) :=
    update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

  (* the stored-entry leaf facts, at Load Data *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Load Data) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Load Data)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.
  (* machine-state pins *)
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) (register_lookup satp s.(sregs)) : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = Some ent.
  (* va geometry at the (aligned) data address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side facts at the translated pa *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N ->
    s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_8_U :
    exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
      = Some (Ok data2, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        assert (Htr : exec (translateAddr
                  (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8)))
                  (Load Data)) s
                = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s)).
        { cbn [bits_of_virtaddr].
          replace (add_vec_int a (0 * 8)) with a by (symmetry; apply avi0).
          exact (exec_translateAddr_load_hit_u ent vpn a
                   (register_lookup satp s.(sregs))
                   (register_lookup tlb s.(sregs)) s
                   Hchk Hupd Hpbmt Hmatch Hcp HSXL Hmprv eq_refl Hsatpmode Hasid
                   eq_refl Hvec Hcanon Hvpn_def). }
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn match.
        match goal with
        | |- execR (Defs.bind ?mrm ?post) s = _ =>
          assert (Hmrm : execR mrm s = Some (inr data2, s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_load_U PBMT_PMA pa region v s
               HpmpA Hpmp_ord Hrange HpmpR Hpmam Hpalign Hread Hc Hsig Hh Hdev Hbytes
               Hmprv Hcp)).
          cbn match.
          rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite autocast_id. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
        cbn. apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. rewrite autocast_id. reflexivity.
  Qed.

End VRU.

(* ===================================================================== *)
(* §7 The register-generic U-mode 8-byte load: vmem_read from ANY rs1     *)
(*    (the pmlen-0 transform is the identity, so the effective address    *)
(*    needs no truncation), and the LOAD execute.                         *)
(* ===================================================================== *)
Section VRUg.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable v : bv 64.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let pa := u_pa ent ea vpn.
  Let data2 : mword (8*1*8) :=
    update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

  (* stored-entry leaf facts at Load Data *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Load Data) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Load Data)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
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
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 8 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side facts at the translated pa *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N ->
    s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_8_U :
    exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s
      = Some (Ok data2, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                   = Some (Ext_DataAddr_OK (Virtaddr ea), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_transform_effective_address_load_u ea s
                    Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hsatpmode)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr ea) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_8_U ent vpn ea v region s
               Hchk Hupd Hpbmt Hmatch Hcp HSXL Hmprv Hsatpmode Hasid Hvec
               Halign Hcanon Hvpn_def
               HpmpA Hpmp_ord Hrange HpmpR Hpmam Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.

  (* the LOAD execute on top (rd <> x0) *)
  Variable rd : mword 5.
  Variable imm : mword 12.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hoffset : offset = sign_extend' 64 imm.

  Lemma exec_execute_LOAD_8_U :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
      = Some (RETIRE_SUCCESS,
              set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value false data2))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
    unfold execute_LOAD.
    replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite <- Hoffset.
    rewrite (exec_bind_Some _ _ _ _ _ exec_vmem_read_8_U).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
                 = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value false data2)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.

End VRUg.

(* ===================================================================== *)
(* §8 The U-mode 8-byte STORE chain: pointer-masking at Store, checked    *)
(*    write under the user PMP grant, and the vmem_write / execute_STORE  *)
(*    chain through the Sv39 hit translation.                             *)
(* ===================================================================== *)

Lemma exec_is_pmm_applicable_store_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Store Data) User) s = Some (true, s).
Proof.
  intro Hmxr.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
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

Lemma exec_get_pmlen_store_u s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (get_pmlen (Store Data) User) s = Some (0, s).
Proof.
  intros Hmxr HES Hsenv Hmenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_store_u s Hmxr)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_user s HES Hsenv Hmenv)).
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_store_u (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4) ->
  exec (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (Virtaddr ea, s).
Proof.
  intros Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hmode.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_nm _ _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_store_u s Hmxr HES Hsenv Hmenv)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_translationMode_U_sv39 (register_lookup satp s.(sregs)) s
                HSXL eq_refl Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  rewrite <- (pm_transform_VA_0 ea) at 2.
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_ram_8_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt User tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr 8 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_8_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_nm _ _ s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_8_U pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section VWUg.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let pa := u_pa ent ea vpn.

  (* stored-entry leaf facts at Store Data *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Store Data) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Store Data)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
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
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 8 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side facts at the translated pa *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_8_U (data : bv 64) :
    exec (vmem_write_addr (Virtaddr ea) 8 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr ea) 8)) s = Some (inr (1, 8), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr ea) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        assert (Htr : exec (translateAddr
                  (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr ea)) (0 * 8)))
                  (Store Data)) s
                = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s)).
        { cbn [bits_of_virtaddr].
          replace (add_vec_int ea (0 * 8)) with ea by (symmetry; apply avi0).
          exact (exec_translateAddr_store_hit_u ent vpn ea
                   (register_lookup satp s.(sregs))
                   (register_lookup tlb s.(sregs)) s
                   Hchk Hupd Hpbmt Hmatch Hcp HSXL Hmprv eq_refl Hsatpmode Hasid
                   eq_refl Hvec Hcanon Hvpn_def). }
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                             = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea pa s)).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
               change (63 - 0 + 1) with 64. rewrite autocast_id.
               unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_8_U PBMT_PMA pa region data s
               HpmpA Hpmp_ord Hrange HpmpW Hpmam Hpalign Hwrite Hc Hsig Hh Hdev
               Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.

  Lemma exec_vmem_write_8_U (data : bv 64) :
    exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                   = Some (Ext_DataAddr_OK (Virtaddr ea), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_transform_effective_address_store_u ea s
                    Hcp Hmprv Hmxr HSXL HES Hsenv Hmenv Hsatpmode)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr ea) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_8_U data).
    reflexivity.
  Qed.

  Lemma exec_execute_STORE_8_U :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
      = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2) s.(mdev)).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
    unfold execute_STORE.
    replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_8_U _)).
    cbn match.
    rewrite (exec_returnM _ _).
    rewrite autocast_subrange_id.
    reflexivity.
  Qed.

End VWUg.
