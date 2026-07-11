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
Require Import UmodeFetch UmodeFetchFault.
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

(* ===================================================================== *)
(* The translateAddr wrapper for a FETCH through the walk path: TLB miss  *)
(* (empty slot) -> 3-level walk -> fill -> u_walk_pa.  State change: the  *)
(* TLB slot at [tlb_hash 39 vpn] gains the level-0 [u_walk_entry].        *)
(* ===================================================================== *)
Lemma exec_translateAddr_fetch_walk_u
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (mxr do_sum : bool) (va satp0 menvcfg0 : mword 64)
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
  (forall s0, exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (InstructionFetch tt) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va),
                PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
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
             (exec_translate_walk_user vpn root pte2 pte1 pte0 (InstructionFetch tt) User mxr do_sum
                H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N
                (mword_of_int 0) menvcfg0 tlbvec s
                Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* Fault walks: an INVALID PTE at any level, a leaf PERMISSION failure,   *)
(* and result-generic descend steps.  This is the exec layer of the       *)
(* translation trichotomy's FAULT arm: an unmapped or kernel-only vpn     *)
(* page-faults instead of translating.  The fault paths stop before the   *)
(* Svnapot gate, so (unlike the success walk) they need no misa premise;  *)
(* they also perform NO writes -- the machine state is preserved.         *)
(* ===================================================================== *)
Section UserWalkFault.
  Context (vpn : mword 27).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* level 0: the leaf slot holds an INVALID pte *)
  Lemma exec_rec_walk_leaf_invalid (base : mword 44) (pte : mword 64)
        (g : bool) (wfacc : Acc (Zwf 0) 0) s :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s).
  Proof.
    intros Hrd Hinv.
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
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    cbv iota beta.
    cbn. reflexivity.
  Qed.

  (* level 0: a valid leaf that FAILS the permission check (e.g. U = 0) *)
  Lemma exec_rec_walk_leaf_noperm (base : mword 44) (pte : mword 64)
        (g : bool) (f : pte_check_failure) (wfacc : Acc (Zwf 0) 0) s :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    (forall s0, exec (check_PTE_permission acc p mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte) tt) s0
       = Some (PTE_Check_Failure (tt, f), s0)) ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s
      = Some (Err (ext_get_ptw_error f, tt), s).
  Proof.
    intros Hrd Hinv Hnl Hchk.
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
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    rewrite Hnl. cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Failure (tt, f)), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite (Hchk s). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    cbn. reflexivity.
  Qed.

  (* level 1: the mid slot holds an INVALID pte *)
  Lemma exec_rec_walk_l1_invalid (base : mword 44) (pte : mword 64)
        (g : bool) (wfacc : Acc (Zwf 0) 1) s :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s).
  Proof.
    intros Hrd Hinv.
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
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    cbv iota beta.
    cbn. reflexivity.
  Qed.

  (* level 1: a valid non-leaf step whose LEVEL-0 sub-walk returns [r]
     (result-generic: instantiate with the invalid/noperm leaf faults;
     [r] must not depend on the accumulated global bit, which fault
     results never do) *)
  Lemma exec_rec_walk_l1_sub (base : mword 44) (pte : mword 64) (g : bool)
        (r : result (PTW_Output 39 * unit) (PTW_Error * unit))
        (wfacc : Acc (Zwf 0) 1) s :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 0),
       exec (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 0 g' tt 0 a) s
         = Some (r, s)) ->
    exec (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s = Some (r, s).
  Proof.
    intros Hrd Hinv Hnl Hsub.
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
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    rewrite Hnl. cbv iota beta.
    change (1 >? 0) with true. cbv iota beta.
    rewrite execR_liftR.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    rewrite Hsub.
    cbn. reflexivity.
  Qed.

  (* level 2 (= the full [pt_walk]): the root slot holds an INVALID pte *)
  Lemma exec_pt_walk_user_l2_invalid (root : mword 44) (pte : mword 64) s :
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    exec (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s).
  Proof.
    intros Hrd Hinv.
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
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    cbv iota beta.
    cbn. reflexivity.
  Qed.

  (* level 2: a valid non-leaf step whose LEVEL-1 sub-walk returns [r] *)
  Lemma exec_pt_walk_user_sub (root : mword 44) (pte : mword 64)
        (r : result (PTW_Output 39 * unit) (PTW_Error * unit)) s :
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 1),
       exec (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 1 g' tt 1 a) s
         = Some (r, s)) ->
    exec (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s = Some (r, s).
  Proof.
    intros Hrd Hinv Hnl Hsub.
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
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrd).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)).
    rewrite Hnl. cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    rewrite execR_liftR.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    rewrite Hsub.
    cbn. reflexivity.
  Qed.

  (* a faulting walk propagates through translate_TLB_miss unchanged
     (no TLB write on the fault path) *)
  Lemma exec_translate_TLB_miss_user_walk_err (asid : mword 16) (root : mword 44)
        (f : PTW_Error) s :
    exec (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Err (f, tt), s) ->
    exec (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Err (f, tt), s).
  Proof.
    intros Hwalk.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ Hwalk).
    cbn match.
    apply exec_returnm.
  Qed.

  (* ...and through translate, given a TLB miss (empty or colliding slot) *)
  Lemma exec_translate_walk_user_err (asid : mword 16) (root : mword 44)
        (f : PTW_Error) s :
    exec (lookup_TLB 39 asid vpn) s = Some (None, s) ->
    exec (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Err (f, tt), s) ->
    exec (translate 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Err (f, tt), s).
  Proof.
    intros Hlk Hmiss.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ Hlk).
    cbn match.
    exact Hmiss.
  Qed.

End UserWalkFault.

(* ===================================================================== *)
(* The translateAddr wrapper for a FETCH whose miss-path walk FAULTS:     *)
(* TLB miss -> walk hits an invalid/no-permission PTE -> fetch page       *)
(* fault.  No state change.  [Hte] is discharged per concrete PTW error   *)
(* by [unfold translationException; cbn match; apply exec_returnm].       *)
(* ===================================================================== *)
Lemma exec_translateAddr_fetch_walk_u_pagefault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (mxr do_sum : bool) (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (InstructionFetch tt) User mxr do_sum root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (InstructionFetch tt) f) s
    = Some (E_Fetch_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Err (E_Fetch_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
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
             (exec_translate_walk_user_err vpn (InstructionFetch tt) User mxr do_sum
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (InstructionFetch tt) User
                   mxr do_sum (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.
