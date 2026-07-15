(* UmodeLrscWalk.v -- data-EA walk-translate lemmas for LoadReserved /
   StoreConditional, the colliding (nomatch) and empty (match) TLB-slot twins.
   Mechanical clones of exec_translateAddr_amo_walk_u{,_nomatch} (UmodeAmo4.v)
   with the access type swapped and the AMO effectivePrivilege / shadow-stack
   helpers replaced by the LoadReserved / StoreConditional ones (UmodeLrsc.v).
   These feed the walk-form Htr to the translate-agnostic LR/SC fault-execute
   towers so the combined (fetch x data hit/miss) LR/SC fault arms can walk+fill
   the data EA before the reservation failure. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr WpLoad.
Require Import UmodeFetch MemData4.
Require Import CommonWalk.
Require Import UmodeLrsc.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_translateAddr_loadres_walk_u
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
     exec (check_PTE_permission (LoadReserved Data) User mxr' do_sum'
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
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (LoadReserved Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (LoadReserved Data)) s
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_loadres_nm _ _ s HMPRV)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (LoadReserved Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


Lemma exec_translateAddr_loadres_walk_u_nomatch
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
     exec (check_PTE_permission (LoadReserved Data) User mxr' do_sum'
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
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (LoadReserved Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (LoadReserved Data)) s
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_loadres_nm _ _ s HMPRV)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user_nomatch vpn root pte2 pte1 pte0 (LoadReserved Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 ent' tlbvec s
                  Hmisa Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


Lemma exec_translateAddr_storecon_walk_u
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
     exec (check_PTE_permission (StoreConditional Data) User mxr' do_sum'
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
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (StoreConditional Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (StoreConditional Data)) s
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_storecon_nm _ _ s HMPRV)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user vpn root pte2 pte1 pte0 (StoreConditional Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 tlbvec s
                  Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


Lemma exec_translateAddr_storecon_walk_u_nomatch
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
     exec (check_PTE_permission (StoreConditional Data) User mxr' do_sum'
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
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (StoreConditional Data) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (StoreConditional Data)) s
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
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_storecon_nm _ _ s HMPRV)).
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
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ ?mxr0 ?do_sum0 _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn);
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_user_nomatch vpn root pte2 pte1 pte0 (StoreConditional Data) User mxr0 do_sum0
                  H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 mxr0 do_sum0 s0) H0N
                  (mword_of_int 0) menvcfg0 ent' tlbvec s
                  Hmisa Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)) end.
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


(* ===================================================================== *)
(* s'-threaded LR.W fault-execute: translate WALKS + FILLS the TLB       *)
(* (returning the post-fill state s'), then the reservation load fails.   *)
(* Translate-agnostic execute at the FILLED state.  One variant covers    *)
(* both the empty-slot (match) and colliding-slot (nomatch) walks.        *)
(* ===================================================================== *)
Section GenVMemReadLoadresFail4Walk.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s'.(sregs),
          make_sync_exception (E_Load_Access_Fault tt) a,
          register_lookup PC s'.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (LoadReserved Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (LoadReserved Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.

  Lemma exec_vmem_read_addr_loadres_fail_walk :
    exec (vmem_read_addr (Virtaddr a) 4 (LoadReserved Data) aq (andb aq rl) true) s
      = Some (Err W, s').
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
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s'))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s' = _ =>
          assert (Hbody : execR inner s' = Some (inl (Err W), s'))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_loadres_fail p PBMT_PMA pa region
               (register_lookup mstatus s'.(sregs)) aq rl s'
               Hpmp Hmatch Hpalign Hresv eq_refl Hmprv Hcp)).
          cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_Load_Access_Fault tt) s')).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.
End GenVMemReadLoadresFail4Walk.

Section GenExecLoadresFail4Walk.
  Variable p : Privilege.
  Variable rs1 rd : mword 5.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s'.(sregs),
          make_sync_exception (E_Load_Access_Fault tt) a,
          register_lookup PC s'.(sregs)).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (LoadReserved Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (LoadReserved Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (LoadReserved Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.

  Lemma exec_vmem_read_loadres_fail_walk :
    exec (vmem_read (Regidx rs1) (zeros' 64) 4 (LoadReserved Data) aq (andb aq rl) true) s
      = Some (Err W, s').
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
    rewrite (exec_vmem_read_addr_loadres_fail_walk p a region s s' pa aq rl
               Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hresv).
    reflexivity.
  Qed.

  Lemma exec_execute_LOADRES_fault_walk :
    exec (execute (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd))) s = Some (W, s').
  Proof.
    change (execute (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd)))
      with (execute_LOADRES aq rl (Regidx rs1) 4 (Regidx rd)).
    unfold execute_LOADRES.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_read_loadres_fail_walk)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecLoadresFail4Walk.

(* ===================================================================== *)
(* s'-threaded SC.W fault-execute: translate WALKS + FILLS (state s'),   *)
(* then the store-conditional PMA check fails on RsrvNone.                 *)
(* ===================================================================== *)
Section GenVMemWriteStoreconFail4Walk.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable dw : mword (8 * 4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Let W' : ExecutionResult :=
    Trap (register_lookup cur_privilege s'.(sregs),
          make_sync_exception (E_SAMO_Access_Fault tt) a,
          register_lookup PC s'.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (StoreConditional Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (StoreConditional Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.
  Hypothesis Hmatchrsv : match_reservation (bits_of_physaddr (Physaddr pa)) = false.

  Lemma exec_vmem_write_addr_storecon_fail_walk :
    exec (vmem_write_addr (Virtaddr a) 4 dw (StoreConditional Data) (andb aq rl) rl true) s
      = Some (Err W', s').
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
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W'), s'))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data))) "sys/vmem_utils.sail:197.50-197.51") s'
                      = Some (tt, s')) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s' = Some (inr tt, s'))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- execR (Defs.bind ?inner ?post) s' = _ =>
          assert (Hbody : execR inner s' = Some (inl (Err W'), s'))
        end.
        { match goal with
          | |- execR (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) s' = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          rewrite Hmatchrsv. cbn [negb andb].
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')). cbn beta.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')). cbn beta.
          rewrite Hcp.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_storecon_nm (register_lookup mstatus s'.(sregs)) p s' Hmprv)). cbn beta.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_phys_access_check_storecon_fail p PBMT_PMA pa region s' Hpmp Hmatch Hpalign Hresv)). cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_SAMO_Access_Fault tt) s')).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.
End GenVMemWriteStoreconFail4Walk.

Section GenExecStoreconFail4Walk.
  Variable p : Privilege.
  Variable rs1 rs2 rd : mword 5.
  Variable a : mword 64.
  Variable dw : mword (8 * 4).
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Variable aq rl : bool.
  Variable dw_src : mword 64.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let W' : ExecutionResult :=
    Trap (register_lookup cur_privilege s'.(sregs),
          make_sync_exception (E_SAMO_Access_Fault tt) a,
          register_lookup PC s'.(sregs)).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (StoreConditional Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (StoreConditional Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (StoreConditional Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hresv : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone.
  Hypothesis Hmatchrsv : match_reservation (bits_of_physaddr (Physaddr pa)) = false.
  Hypothesis Hrs2 : exec (rX_bits (Regidx rs2)) s = Some (dw_src, s).

  Lemma exec_vmem_write_storecon_fail_walk :
    exec (vmem_write (Regidx rs1) (zeros' 64) 4
            (autocast (T := mword) (subrange_vec_dec dw_src (Z.sub (Z.mul 4 8) 1) 0))
            (StoreConditional Data) (andb aq rl) rl true) s
      = Some (Err W', s').
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
    rewrite (exec_vmem_write_addr_storecon_fail_walk p a
               (autocast (T := mword) (subrange_vec_dec dw_src (Z.sub (Z.mul 4 8) 1) 0))
               region s s' pa aq rl Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hresv Hmatchrsv).
    reflexivity.
  Qed.

  Lemma exec_execute_STORECON_fault_walk :
    exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd))) s = Some (W', s').
  Proof.
    change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_STORECON.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ Hrs2).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_storecon_fail_walk)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreconFail4Walk.
