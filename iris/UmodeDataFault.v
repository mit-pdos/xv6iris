(* UmodeDataFault.v -- DATA-side translateAddr page-fault reductions.

   The data-access analogs of [exec_translateAddr_fetch_walk_u_pagefault]
   (UmodeWalk.v): when a U-mode LOAD/STORE effective address misses the TLB
   and the page walk returns [Err f] (unmapped / kernel-denied vpn), the
   [translateAddr] for [Load Data] / [Store Data] returns
   [Err (E_Load_Page_Fault)] / [Err (E_SAMO_Page_Fault)] with NO state
   change.  Clones of the fetch reduction with the access type swapped
   (and the extra MPRV=0 hypothesis the data effectivePrivilege needs).
   The walk-[Err] itself comes from [upt_unmapped_walk_fault] (access-
   generic) and the caller supplies the [translationException] fact. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import SmodeCore.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeFetchFault UmodeWalk.
Require Import UmodeData.
Local Open Scope Z_scope.
Import Defs.

(* LOAD: translateAddr faults through the walk with a load page fault *)
Lemma exec_translateAddr_load_walk_u_pagefault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (Load Data) User
          (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
          (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
          root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (Load Data) f) s
    = Some (E_Load_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Load Data)) s
    = Some (Err (E_Load_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_err vpn (Load Data) User
                (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (Load Data) User
                   (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                   (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                   (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* STORE: translateAddr faults through the walk with a store/amo page fault *)
Lemma exec_translateAddr_store_walk_u_pagefault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (Store Data) User
          (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
          (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
          root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (Store Data) f) s
    = Some (E_SAMO_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Store Data)) s
    = Some (Err (E_SAMO_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_err vpn (Store Data) User
                (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (Store Data) User
                   (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                   (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                   (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.
