(* UmodeWalk.v -- the full 3-level Sv39 page walk over an ABSTRACT page
   table (SmodeCore's exec_pt_walk_super handles only the kernel's
   single-level identity superpage).

   The walk lemma is generic over the ACCESS TYPE and the PRIVILEGE: only
   the leaf permission-check hypothesis mentions them, so the same lemma
   serves instruction fetches, loads, stores and AMOs.  The three PTE
   reads are taken as [read_pte] exec facts (dischargeable by
   [exec_read_pte_S] from owned PT-page bytes); the structural facts
   about the three PTE words (level 2/1 valid non-leaf, level 0 valid
   leaf, permission check passes, no NAPOT) are conditioned hypotheses
   in the style of the UmodeFetch hit chain -- the user-page-table
   invariant discharges them from pt_wf, a concrete demo by vm_compute.

   NOTE the walk itself performs NO A/D update -- that happens in
   translate_TLB_miss on the walk's output PTE (both the no-update
   success and the ADUE=0 needs-update page fault are handled there,
   the latter by UmodeFetchFault's exec_update_and_write_pte_needs_update). *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import WpDecodeBridge.
Require Import UmodeFetchFault.
Local Open Scope Z_scope.
Import Defs.

(* the PTE slot address at one walk level: base ppn ++ 9-bit index ++ 000 *)
Definition u_pte_addr (base : mword 44) (idx : mword 9) : mword 64 :=
  zero_extend' 64 (concat_vec base (concat_vec idx (zeros' 3))).

(* the next-level base ppn recorded in a non-leaf PTE *)
Definition u_next_base (pte : mword 64) : mword 44 :=
  autocast (T := mword) (PPN_of_PTE pte).

(* the accumulated global bit after the three levels *)
Definition u_gbit (pte : mword 64) : bool :=
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (subrange_vec_dec pte 7 0))) ('b"1").
Definition u_global (pte2 pte1 pte0 : mword 64) : bool :=
  orb (orb (orb false (u_gbit pte2)) (u_gbit pte1)) (u_gbit pte0).

(* NB: do NOT [destruct Zwf_guarded; vm_compute] here -- the Svnapot probe
   recurses (via the Zca gate, which reads misa) and vm_compute on an
   ABSTRACT state diverges.  Transport the concrete-state evaluation via
   the read-frame bridge instead; the read set is exactly {misa}. *)
Definition D_misa (r : register) : bool := register_beq r (R_bitvector_64 misa).

Lemma exec_currentlyEnabled_Svnapot s :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (currentlyEnabled Ext_Svnapot) s = Some (true, s).
Proof.
  intro Hmisa.
  apply (decode_state_bridge D_misa _ dstateM).
  - intros r Hr. unfold D_misa in Hr. apply register_beq_eq in Hr. subst r.
    rewrite Hmisa. vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Section UserWalk.
  Context (vpn : mword 27) (root : mword 44).
  Context (pte2 pte1 pte0 : mword 64).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* the three slot addresses the walk reads *)
  Let addr2 : mword 64 := u_pte_addr root (subrange_vec_dec vpn 26 18).
  Let addr1 : mword 64 := u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9).
  Let addr0 : mword 64 := u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0).

  (* levels 2 and 1: valid non-leaf PTEs *)
  Hypothesis H2i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                                     (ext_bits_of_PTE pte2)) s = Some (false, s).
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                                     (ext_bits_of_PTE pte1)) s = Some (false, s).
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  (* level 0: a valid leaf that passes the permission check, no NAPOT *)
  Hypothesis H0i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                                     (ext_bits_of_PTE pte0)) s = Some (false, s).
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false.
  Hypothesis Hchk0 : forall s, exec (check_PTE_permission acc p mxr do_sum
                                       (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                                       (ext_bits_of_PTE pte0) tt) s
                               = Some (PTE_Check_Success tt, s).
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false.

  (* level 0: the leaf, from any reclimit-0 Acc *)
  Lemma exec_rec_walk_leaf (g : bool) (menvcfg0 : mword 64)
        (wfacc : Acc (Zwf 0) 0) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte1) 0 g tt 0 wfacc) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := orb g (u_gbit pte0) |}, tt), s).
  Proof.
    intros Hmisa Hrd0 Hmenv HPBMTE.
    destruct wfacc as [a0].
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (0 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd0).
    rewrite (execR_liftR_seq _ _ _ _ _ (H0i s)).
    rewrite H0nl. cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite (Hchk0 s). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (0 >? 0) with false. cbv iota beta.
    (* the Svnapot gate sits under two binds: decompose with the plain
       execR_bind equations, resolve the probe, and let the N-bit kill it *)
    rewrite execR_bind.
    rewrite execR_bind.
    unfold Defs.and_boolM.
    rewrite execR_bind.
    rewrite execR_liftR.
    rewrite (exec_currentlyEnabled_Svnapot s Hmisa). cbn match beta.
    cbv iota beta.
    rewrite H0N. cbv iota beta.
    rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    cbn. reflexivity.
  Qed.

  (* level 1: a valid non-leaf step into the leaf, from any reclimit-1 Acc *)
  Lemma exec_rec_walk_l1 (g : bool) (menvcfg0 : mword 64)
        (wfacc : Acc (Zwf 0) 1) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte2) 1 g tt 1 wfacc) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := orb (orb g (u_gbit pte1)) (u_gbit pte0) |}, tt), s).
  Proof.
    intros Hmisa Hrd1 Hrd0 Hmenv HPBMTE.
    destruct wfacc as [a1].
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (1 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr1 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd1).
    rewrite (execR_liftR_seq _ _ _ _ _ (H1i s)).
    rewrite H1nl. cbv iota beta.
    change (1 >? 0) with true. cbv iota beta.
    rewrite execR_liftR.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    rewrite (exec_rec_walk_leaf _ menvcfg0 _ s Hmisa Hrd0 Hmenv HPBMTE).
    cbn. reflexivity.
  Qed.

  (* level 2 = the full walk *)
  Lemma exec_pt_walk_user (menvcfg0 : mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := u_global pte2 pte1 pte0 |}, tt), s).
  Proof.
    intros Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold pt_walk.
    destruct (Defs.Zwf_guarded _) as [a2].
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr2 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd2).
    rewrite (execR_liftR_seq _ _ _ _ _ (H2i s)).
    rewrite H2nl. cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    rewrite execR_liftR.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    rewrite (exec_rec_walk_l1 _ menvcfg0 _ s Hmisa Hrd1 Hrd0 Hmenv HPBMTE).
    cbn. reflexivity.
  Qed.

  (* the TLB entry a level-0 walk installs (masks are empty at level 0) *)
  Definition u_walk_entry (asid : mword 16) : TLB_Entry :=
    {| TLB_Entry_asid := asid;
       TLB_Entry_global := u_global pte2 pte1 pte0;
       TLB_Entry_pte := zero_extend' 64 ((autocast (T := mword) pte0) : mword 64);
       TLB_Entry_pteAddr := Physaddr addr0;
       TLB_Entry_levelMask := zero_extend' (57 - 12) (ones 0 : mword 0);
       TLB_Entry_vpn := sign_extend' (57 - 12)
                          (and_vec vpn (not_vec (zero_extend' 27 (ones 0 : mword 0))));
       TLB_Entry_ppn := zero_extend' 44
                          (and_vec ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44)) : mword 44)
                                   (not_vec (zero_extend' 44 (ones 0 : mword 0)))) |}.

  Lemma exec_add_to_TLB_user (asid : mword 16) s :
    exec (add_to_TLB 39 asid vpn
            (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44))
            (autocast (T := mword) pte0) (Physaddr addr0) 0 (u_global pte2 pte1 pte0)) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                                   (tlb_hash (__id 39) vpn) (Some (u_walk_entry asid)))).
  Proof.
    unfold add_to_TLB. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    reflexivity.
  Qed.

  (* success: the leaf's A (and D) bits need no update *)
  Lemma exec_translate_TLB_miss_user (asid : mword 16) (menvcfg0 : mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = None ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44), PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn) (Some (u_walk_entry asid)))).
  Proof.
    intros Hmisa Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_user menvcfg0 s Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?pv ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd pv ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte. rewrite Hnoupd. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_user asid s)).
    apply exec_returnm.
  Qed.

  (* fault: the leaf needs an A/D update the config forbids (ADUE = 0) *)
  Lemma exec_translate_TLB_miss_user_needs_update (asid : mword 16) (pte' : mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = Some pte' ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    exec (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Err (PTW_PTE_Needs_Update tt, tt), s).
  Proof.
    intros Hmisa Hupd_some Hrd2 Hrd1 Hrd0 Hmenv.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_user MENVCFG_S s Hmisa Hrd2 Hrd1 Hrd0 Hmenv
                  ltac:(vm_compute; reflexivity))).
    cbn match.
    erewrite exec_bind_Some.
    2:{ eapply exec_update_and_write_pte_needs_update; [ exact Hupd_some | exact Hmenv ]. }
    cbn match.
    apply exec_returnm.
  Qed.

  Lemma exec_translate_walk_user (asid : mword 16) (menvcfg0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = None ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44), PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                               (Some (u_walk_entry asid)))).
  Proof.
    intros Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss vpn asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_user asid menvcfg0 s Hmisa Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
  Qed.

  (* miss via hash collision: the slot holds a NON-matching entry *)
  Lemma exec_lookup_TLB_nomatch (asid : mword 16) (ent' : TLB_Entry)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
    match_TLB_Entry ent' asid (sign_extend' (57 - 12) vpn) = false ->
    exec (lookup_TLB 39 asid vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec Hnm.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. rewrite Hnm. apply exec_returnm.
  Qed.

  (* the translated physical address a level-0 walk yields for [va] *)
  Definition u_walk_pa (va : mword 64) : mword 64 :=
    zero_extend' 64 (concat_vec
      ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44)) : mword 44)
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)).

End UserWalk.
