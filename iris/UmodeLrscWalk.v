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
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore WpGpr.
Require Import UmodeFetch MemData4 UmodeData.
Require Import CommonWalk RiscvPtsto.
Require Import UmodeAmo4 UmodeLrsc.
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

