(* ====================================================================== *)
(* UserFaultCert.v -- THE FAULT SIDE OF THE U-MODE TRANSLATION, PURE.      *)
(*                                                                        *)
(* [UserFetchCert.v] made the SUCCESS side of a U-mode translation pure    *)
(* ([u_fetch_pure]); the FAULT side existed only as Iris                   *)
(* ([UserPtTree.utlb_inv_pt_translateAddr_u_fault] over its three          *)
(* flavours).  This file is its pure twin, plus the [goodmb] certificate   *)
(* the per-node engine needs, at the tier's reference state               *)
(* [UserClassifyAsm.u_state rs mm].                                        *)
(*                                                                        *)
(* THE FAULT WALK DOES NOT MOVE THE STATE.  No arm of it fills the TLB     *)
(* and no arm write-backs A/D: [translate_TLB_miss] returns the walk's     *)
(* error before [add_to_TLB], and a denied HIT fails                       *)
(* [check_PTE_permission] BEFORE [update_and_write_pte] is even reached.   *)
(* So the post state is [u_state rs mm] ON THE NOSE, there is no           *)
(* [u_mem_step] conjunct, and the caller keeps the file and the tree it    *)
(* came in with.  (Checked against the model for all three flavours: the   *)
(* non-canonical fault fires before the TLB is consulted at all, the       *)
(* unmapped walk stops at an invalid word, and the denied walk stops at    *)
(* the leaf's permission check -- none of the three reaches a write.)      *)
(*                                                                        *)
(* Layout: section 1 the access-type hygiene the certificates need,        *)
(* read off the caller's own [exec] premises; section 2 the DENIED leaf's  *)
(* permission check, certified; section 3 the fault-side [translateAddr]   *)
(* front matter (the [_err] and [_noncanon] twins of                       *)
(* [PtWalkCert.goodmb_translateAddr_pt_front]); section 4 the denied TLB   *)
(* HIT; section 5 the BLOCKED walk; section 6 the DENIED walk; section 7   *)
(* [u_translate_fault_pure]; section 8 [u_fetch_fault_pure]; section 9     *)
(* the four [goodmb] shells of the 2-ALIGNED (split) fetch.                *)
(*                                                                        *)
(* THE SLOT/[translationMode] HELPERS COME FROM [UserFetchCert] DIRECTLY:  *)
(* [mword9_uint_range] / [mword9_uint_id] / [pt_page_maps_slot] /          *)
(* [ptree_maps_slot{0,1,2}] / [u_slot_mem_at] / [u_slot_owned] /           *)
(* [goodmb_currentlyEnabled_Ziccif] / [goodb_read_reg_D] /                 *)
(* [goodb_architecture_Supervisor] / [goodb_translationMode_U].  At the    *)
(* fold-back the worklist plans, the slot projections move to [UserMem.v]  *)
(* and the walk arms to [UserPtTree.v].                                    *)
(* ====================================================================== *)
Set Printing Depth 40.
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge HartGoodb HartMemRun HartMemAsm PtBytes.
Require Import MemAccessGen WpLoad WpMmodeLeafBase SmodePte.
Require Import CommonWalk PtAdBits Pt4kWalk PtreeType KptPt PtTree PtTreeAdue KptTree PtBuild.
Require Import ExecCommon UserTranslate UptTree UserPtTree UserBits UserMem UserFetch.
Require Import UserBytes PtWalkCert UserFetchPt.
Require Import SmodeCore.
Require Import UserFrame UserExec UserClassify UserClassifyAsm.
Require Import UserFetchCert.
(* [goodb_bind_forall] / [goodb_and_boolM] / [goodb_or_boolM] /
   [goodb_bind_read_reg], for the [Ext_Zca] gate of the split fetch's head.
   Kept UNIMPORTED (qualified uses only) so nothing here is shadowed. *)
Require DecodeTotalU.
Local Open Scope Z_scope.
Import Defs.


(* §1 access-type hygiene *)

Lemma u_ssa_ret (acc : MemoryAccessType mem_payload) (s : mstate) :
  exec (is_shadow_stack_access acc) s = Some (false, s) ->
  is_shadow_stack_access acc = Defs.returnm false.
Proof.
  intros Hss.
  destruct acc as [m | m | [[aq rl] m] | [[aq rl] m] | [[[[op aq] rl] m1] m2] | u | c];
    try destruct m; try destruct m1; try destruct m2; try destruct u;
    try destruct c;
    repeat match goal with u : unit |- _ => destruct u end;
    first [ reflexivity | (cbn in Hss; discriminate Hss) ].
Qed.

Lemma u_ssa_goodb (acc : MemoryAccessType mem_payload) (s : mstate) :
  exec (is_shadow_stack_access acc) s = Some (false, s) ->
  forall (Db : register -> bool) (s0 : mstate),
    goodb Db (is_shadow_stack_access acc) s0 = true.
Proof. intros Hss Db s0. rewrite (u_ssa_ret acc s Hss). reflexivity. Qed.

Lemma u_ssa_exec_any (acc : MemoryAccessType mem_payload) (s : mstate) :
  exec (is_shadow_stack_access acc) s = Some (false, s) ->
  forall s0 : mstate, exec (is_shadow_stack_access acc) s0 = Some (false, s0).
Proof. intros Hss s0. rewrite (u_ssa_ret acc s Hss). apply exec_returnM. Qed.

Lemma u_texc_goodb (acc : MemoryAccessType mem_payload) (err : PTW_Error)
    (e : ExceptionType) (s : mstate) :
  exec (translationException acc err) s = Some (e, s) ->
  forall (Db : register -> bool) (s0 : mstate),
    goodb Db (translationException acc err) s0 = true.
Proof.
  intros Hte Db s0. revert Hte.
  destruct acc as [m | m | [[aq rl] m] | [[aq rl] m] | [[[[op aq] rl] m1] m2] | u | c];
    try destruct m; try destruct m1; try destruct m2; try destruct u;
    try destruct c; destruct err;
    repeat match goal with u : unit |- _ => destruct u end;
    intros Hte;
    first [ reflexivity | (cbn in Hte; discriminate Hte) ].
Qed.

Lemma u_eff_goodb (acc : MemoryAccessType mem_payload) (m : mword 64)
    (pv : Privilege) (s : mstate) :
  exec (effectivePrivilege acc m pv) s = Some (pv, s) ->
  forall (Db : register -> bool) (s0 : mstate),
    goodb Db (effectivePrivilege acc m pv) s0 = true.
Proof.
  intros Heff Db s0. revert Heff. unfold effectivePrivilege.
  destruct (andb (generic_neq acc (InstructionFetch tt))
              (eq_vec (_get_Mstatus_MPRV m) ('b"1"))) eqn:E;
    cbn match; intros Heff; [ | reflexivity ].
  unfold privLevel_bits_forwards in Heff |- *.
  repeat (match goal with
          | |- context[if ?b then _ else _] =>
              let Eb := fresh "Eb" in
              destruct b eqn:Eb; rewrite ?Eb in Heff; cbn match in Heff
          end); try reflexivity.
  cbn in Heff. discriminate Heff.
Qed.

(* §2 the denied leaf's permission check, certified *)

Lemma goodb_check_PTE_permission_denied (acc : MemoryAccessType mem_payload)
    (w' : mword 64) (mxr do_sum : bool) (Db : register -> bool) (s ss : mstate) :
  exec (is_shadow_stack_access acc) ss = Some (false, ss) ->
  pte_check_denied acc User mxr do_sum (PTE_No_Permission tt) w' ->
  goodb Db (check_PTE_permission acc User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec w' 7 0)) (ext_bits_of_PTE w') tt) s = true.
Proof.
  intros Hss Hden.
  pose proof (Hden dstateM) as Hc0.
  unfold check_PTE_permission in Hc0 |- *.
  rewrite (u_ssa_ret acc ss Hss) in Hc0 |- *.
  destruct (mword1_cases (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HU|HU];
  destruct (mword1_cases (_get_PTE_Flags_R (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HR|HR];
  destruct (mword1_cases (_get_PTE_Flags_W (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HW|HW];
  destruct (mword1_cases (_get_PTE_Flags_X (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HX|HX];
  rewrite ?HU, ?HR, ?HW, ?HX in Hc0 |- *;
  first [ solve [ vm_compute; reflexivity ]
        | solve [ vm_compute in Hc0; discriminate Hc0 ] ].
Time Qed.

(* §3 the fault-side [translateAddr] front matter, certified *)

Section TranslateFrontFault.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege).
  Hypothesis HDms : Dr mstatus = true.
  Hypothesis HDcp : Dr cur_privilege = true.
  Hypothesis HDsatp : Dr satp = true.

  Lemma goodmb_translateAddr_pt_front_err (vpn : mword 27) (root : mword 44)
      (f : PTW_Error) (e : ExceptionType) (satp0 va : mword 64)
      (s : mstate) (mm : pamap) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s
      = Some (pv, s) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s = true ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    goodb Dr (is_shadow_stack_access acc) s = true ->
    register_lookup cur_privilege s.(sregs) = pv ->
    exec (translationMode pv) s = Some (Sv39, s) ->
    goodb Dr (translationMode pv) s = true ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0))
      = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)
      (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc pv mxr do_sum tt) s
       = Some (Err (f, tt), s)) ->
    (forall mxr do_sum,
       goodmb Dr Dw
         (translate 39 (mword_of_int 0 : mword 16) root vpn acc pv mxr do_sum tt)
         s mm = true) ->
    exec (translationException acc f) s = Some (e, s) ->
    goodb Dr (translationException acc f) s = true ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true.
  Proof.
    intros Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon Hvpn_def
           Htr Htrg Hte Hteg.
    unfold translateAddr. apply goodmb_cer.
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDcp)
              ltac:(apply (exec_read_reg cur_privilege)).
    rewrite Hcp.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Heffg) Heff.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Htmg) Htm.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Hssg) Hss.
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    gmm_lift (goodmb_returnm Dr Dw (E := exception) 39 s mm) Hwidth.
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
          by (vm_compute; reflexivity).
        unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    assert (Hgsg : goodmb Dr Dw (get_satp 39) s mm = true).
    { unfold get_satp.
      gmm_peelT ltac:(apply goodmb_assert_exp'_true)
                ltac:(apply exec_assert_exp'_true).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      gmm_rr satp HDsatp. apply goodmb_returnm. }
    gmm_lift Hgsg Hgs.
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true
        by (vm_compute; reflexivity).
      unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    gmm_liftT ltac:(apply goodmb_assert_exp'_true) ltac:(exact Hae2).
    rewrite Hcanon. cbn match.
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    match goal with |- context[translate 39 _ _ _ _ _ ?mx ?ds _] =>
      gmm_lift (Htrg mx ds) (Htr mx ds) end.
    cbn match.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Hteg) Hte.
    apply goodmb_returnm.
  Qed.

  Lemma goodmb_translateAddr_pt_front_noncanon (e : ExceptionType)
      (satp0 va : mword 64) (s : mstate) (mm : pamap) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s
      = Some (pv, s) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s = true ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    goodb Dr (is_shadow_stack_access acc) s = true ->
    register_lookup cur_privilege s.(sregs) = pv ->
    exec (translationMode pv) s = Some (Sv39, s) ->
    goodb Dr (translationMode pv) s = true ->
    register_lookup satp s.(sregs) = satp0 ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0))
      = true ->
    exec (translationException acc (PTW_Invalid_Addr tt)) s = Some (e, s) ->
    goodb Dr (translationException acc (PTW_Invalid_Addr tt)) s = true ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true.
  Proof.
    intros Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hcanon Hte Hteg.
    unfold translateAddr. apply goodmb_cer.
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDcp)
              ltac:(apply (exec_read_reg cur_privilege)).
    rewrite Hcp.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Heffg) Heff.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Htmg) Htm.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Hssg) Hss.
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    gmm_lift (goodmb_returnm Dr Dw (E := exception) 39 s mm) Hwidth.
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
          by (vm_compute; reflexivity).
        unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    assert (Hgsg : goodmb Dr Dw (get_satp 39) s mm = true).
    { unfold get_satp.
      gmm_peelT ltac:(apply goodmb_assert_exp'_true)
                ltac:(apply exec_assert_exp'_true).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      gmm_rr satp HDsatp. apply goodmb_returnm. }
    gmm_lift Hgsg Hgs.
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true
        by (vm_compute; reflexivity).
      unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    gmm_liftT ltac:(apply goodmb_assert_exp'_true) ltac:(exact Hae2).
    rewrite Hcanon. cbn match.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Hteg) Hte.
    apply goodmb_returnm.
  Qed.

End TranslateFrontFault.

(* §4 the DENIED TLB hit, certified *)

Section HitDeniedCert.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege) (mxr do_sum : bool).

  Lemma goodmb_translate_TLB_hit_denied_pt (vpn : mword 27) (q2 q1 q0 : mword 64)
      (asid : mword 16) (idx : Z) (s : mstate) (mm : pamap) :
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec q0 7 0))
                   (ext_bits_of_PTE q0) tt) s0 = true) ->
    pte_check_denied acc pv mxr do_sum (PTE_No_Permission tt) q0 ->
    goodmb Dr Dw (translate_TLB_hit 39 asid vpn acc pv mxr do_sum tt idx
                    (u_walk_entry vpn q2 q1 q0 asid)) s mm = true.
  Proof.
    intros Hgchk Hden.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte. rewrite autocast_id.
    gmm_peel (goodmb_of_goodb Dr Dw _ s mm (Hgchk Dr s)) (Hden s).
    cbn match. apply goodmb_returnm.
  Qed.

  (* ...and through [translate], given a TLB HIT at [idx] *)
  Lemma goodmb_translate_hit_err (asid : mword 16) (root : mword 44)
      (vpn : mword 27) (idx : Z) (ent : TLB_Entry) (s : mstate) (mm : pamap) :
    Dr tlb = true ->
    exec (lookup_TLB 39 asid vpn) s = Some (Some (idx, ent), s) ->
    goodmb Dr Dw (translate_TLB_hit 39 asid vpn acc pv mxr do_sum tt idx ent) s mm = true ->
    goodmb Dr Dw (translate 39 asid root vpn acc pv mxr do_sum tt) s mm = true.
  Proof.
    intros HD Hlk Hhit. unfold translate.
    gmm_peel (goodmb_lookup_TLB vpn Dr Dw asid s mm HD) Hlk.
    cbn match. exact Hhit.
  Qed.

End HitDeniedCert.

(* §5 the BLOCKED walk: slot memberships and the zero stop word *)

Lemma goodb_pte_is_invalid_zero (Db : register -> bool) (s : mstate) :
  goodb Db (pte_is_invalid
              (Mk_PTE_Flags (subrange_vec_dec (mword_of_int 0 : mword 64) 7 0))
              (ext_bits_of_PTE (mword_of_int 0 : mword 64))) s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ptree_blocks0_slots (t : ptree) (vpn : mword 27) :
  ptree_blocks0 t vpn ->
  (word_bytes (pt_addr2 t vpn) (mword_of_int 0 : mword 64) ∈ pt_maps 2 t)
  \/ (exists p2, pte_valid p2 /\ pte_ptr p2 /\
        word_bytes (pt_addr2 t vpn) p2 ∈ pt_maps 2 t /\
        word_bytes (pt_addr1 p2 vpn) (mword_of_int 0 : mword 64) ∈ pt_maps 2 t)
  \/ (exists p2 p1, pte_valid p2 /\ pte_ptr p2 /\ pte_valid p1 /\ pte_ptr p1 /\
        word_bytes (pt_addr2 t vpn) p2 ∈ pt_maps 2 t /\
        word_bytes (pt_addr1 p2 vpn) p1 ∈ pt_maps 2 t /\
        word_bytes (pt_addr0 p1 vpn) (mword_of_int 0 : mword 64) ∈ pt_maps 2 t).
Proof.
  intros [ (Hk & He)
         | [ (c1 & Hk2 & Hk1 & Hv2 & Hn2 & Hb1 & He)
           | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hn2 & Hv1 & Hn1 & Hb1 & Hb0 & He) ] ].
  - left. unfold pt_addr2. rewrite <- He.
    apply pt_maps_page. apply pt_page_maps_slot.
  - right; left. exists (pt_ents t (vpn_idx 2 vpn)). split_and!;
      [ exact Hv2 | exact Hn2 | | ].
    + unfold pt_addr2. apply pt_maps_page. apply pt_page_maps_slot.
    + unfold pt_addr1. rewrite Hb1. rewrite <- He.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply mword9_uint_range
        | rewrite mword9_uint_id; exact Hk2
        | apply pt_maps_page; apply pt_page_maps_slot ].
  - right; right.
    exists (pt_ents t (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)). split_and!;
      [ exact Hv2 | exact Hn2 | exact Hv1 | exact Hn1 | | | ].
    + unfold pt_addr2. apply pt_maps_page. apply pt_page_maps_slot.
    + unfold pt_addr1. rewrite Hb1.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply mword9_uint_range
        | rewrite mword9_uint_id; exact Hk2
        | apply pt_maps_page; apply pt_page_maps_slot ].
    + unfold pt_addr0. rewrite Hb0. rewrite <- He.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply mword9_uint_range | rewrite mword9_uint_id; exact Hk2 |].
      apply (pt_maps_kid 0 c1 c0 (uint (vpn_idx 1 vpn)));
        [ apply mword9_uint_range | rewrite mword9_uint_id; exact Hk1 |].
      rewrite pt_maps_O. apply pt_page_maps_slot.
Qed.

(* §5b ONE page-table slot of the owned tree, read: exec fact AND certificate *)

Lemma u_slot_read (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (b : mword 44) (i : mword 9) (q : mword 64) :
  u_mem_wf P t mm ->
  u_exec_pins P t rs ->
  word_bytes (u_pte_addr b i) q ∈ pt_maps 2 t ->
  exec (read_pte (Physaddr (u_pte_addr b i)) 8) (u_state rs mm)
    = Some (Ok q, u_state rs mm)
  /\ goodmb Du_r Du_w (read_pte (Physaddr (u_pte_addr b i)) 8) (u_state rs mm) mm
     = true.
Proof.
  intros Hwf Hpins Hin.
  destruct Hpins as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
  pose proof (u_slot_mem_at P t mm rs b i q Hwf Hin) as Hsm.
  destruct (Hpmar (u_pte_addr b i) (pt_slot_ram_access _ _ _ Hsm))
    as (region & Hm & Hs).
  split.
  - exact (pt_read_pte_slot (u_state rs mm) _ q region Hsm HA Hord HRp Hcovp Hm Hs Hhtif).
  - exact (goodmb_read_pte_slot Du_r Du_w
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             (u_state rs mm) mm _ q region Hsm
             (u_slot_owned P t mm _ q Hwf Hin)
             HA Hord HRp Hcovp Hm Hs Hhtif).
Qed.

(* §5c THE BLOCKED WALK, both sides.  The stop word is the LITERAL ZERO
   ([ptree_blocks0], which [upt_tree_spec] hands out for every vpn that is
   neither mapped nor one of the two S-mode top pages), and that is what
   makes its [pte_is_invalid] certificate hold at EVERY footprint -- the
   shape [PtWalkCert]'s fault-walk lemmas ask for. *)

Lemma u_translate_blocked (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (acc : MemoryAccessType mem_payload) (vpn : mword 27) (mxr do_sum : bool) :
  u_mem_wf P t mm ->
  u_exec_pins P t rs ->
  ptree_blocks0 t vpn ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) (u_state rs mm)
    = Some (None, u_state rs mm) ->
  exec (translate 39 (mword_of_int 0 : mword 16) (ud_root P) vpn acc User mxr do_sum tt)
       (u_state rs mm) = Some (Err (PTW_Invalid_PTE tt, tt), u_state rs mm)
  /\ goodmb Du_r Du_w
       (translate 39 (mword_of_int 0 : mword 16) (ud_root P) vpn acc User mxr do_sum tt)
       (u_state rs mm) mm = true.
Proof.
  intros Hwf Hpins Hblk Hlk.
  pose proof Hwf as (md & _ & _ & _ & _ & _ & _ & _ & _ & Hspec).
  pose proof Hspec as (Hbase & _).
  set (s := u_state rs mm) in *.
  assert (Hwalk : exec (pt_walk 39 vpn acc User mxr do_sum (ud_root P) 2 false tt) s
                  = Some (Err (PTW_Invalid_PTE tt, tt), s)
                  /\ goodmb Du_r Du_w
                       (pt_walk 39 vpn acc User mxr do_sum (ud_root P) 2 false tt)
                       s mm = true).
  { destruct (ptree_blocks0_slots t vpn Hblk) as
      [ H2 | [ (p2 & Hv2 & Hn2 & H2 & H1) | (p2 & p1 & Hv2 & Hn2 & Hv1 & Hn1 & H2 & H1 & H0) ] ].
    - (* the root slot is the zero word *)
      unfold pt_addr2 in H2. rewrite Hbase in H2.
      destruct (u_slot_read P t mm rs (ud_root P) (vpn_idx 2 vpn) _ Hwf Hpins H2)
        as (Hrd & Hrdg).
      split.
      + exact (exec_pt_walk_user_l2_invalid vpn acc User mxr do_sum (ud_root P)
                 (mword_of_int 0) s Hrd pte_invalid_zero).
      + exact (goodmb_pt_walk_user_l2_invalid vpn acc User mxr do_sum Du_r Du_w
                 (ud_root P) (mword_of_int 0) s mm Hrd Hrdg
                 (fun Db s0 => goodb_pte_is_invalid_zero Db s0) pte_invalid_zero).
    - (* the mid slot is the zero word *)
      unfold pt_addr2 in H2. rewrite Hbase in H2.
      unfold pt_addr1 in H1.
      destruct (u_slot_read P t mm rs (ud_root P) (vpn_idx 2 vpn) _ Hwf Hpins H2)
        as (Hrd2 & Hrd2g).
      destruct (u_slot_read P t mm rs (u_next_base p2) (vpn_idx 1 vpn) _ Hwf Hpins H1)
        as (Hrd1 & Hrd1g).
      split.
      + apply (exec_pt_walk_user_sub vpn acc User mxr do_sum (ud_root P) p2 _ s
                 Hrd2 Hv2 Hn2).
        intros g' a1.
        exact (exec_rec_walk_l1_invalid vpn acc User mxr do_sum (u_next_base p2)
                 (mword_of_int 0) g' a1 s Hrd1 pte_invalid_zero).
      + apply (goodmb_pt_walk_user_sub vpn acc User mxr do_sum Du_r Du_w
                 (ud_root P) p2 s mm Hrd2 Hrd2g
                 (fun Db s0 => goodb_pte_is_invalid_valid p2 Db s0 Hv2) Hv2 Hn2).
        intros g' a1.
        exact (goodmb_rec_walk_l1_invalid vpn acc User mxr do_sum Du_r Du_w
                 (u_next_base p2) (mword_of_int 0) g' a1 s mm Hrd1 Hrd1g
                 (fun Db s0 => goodb_pte_is_invalid_zero Db s0) pte_invalid_zero).
    - (* the leaf slot is the zero word *)
      unfold pt_addr2 in H2. rewrite Hbase in H2.
      unfold pt_addr1 in H1. unfold pt_addr0 in H0.
      destruct (u_slot_read P t mm rs (ud_root P) (vpn_idx 2 vpn) _ Hwf Hpins H2)
        as (Hrd2 & Hrd2g).
      destruct (u_slot_read P t mm rs (u_next_base p2) (vpn_idx 1 vpn) _ Hwf Hpins H1)
        as (Hrd1 & Hrd1g).
      destruct (u_slot_read P t mm rs (u_next_base p1) (vpn_idx 0 vpn) _ Hwf Hpins H0)
        as (Hrd0 & Hrd0g).
      split.
      + apply (exec_pt_walk_user_sub vpn acc User mxr do_sum (ud_root P) p2 _ s
                 Hrd2 Hv2 Hn2).
        intros g' a1.
        apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum (u_next_base p2) p1 g' _ a1 s
                 Hrd1 Hv1 Hn1).
        intros g'' a0.
        exact (exec_rec_walk_leaf_invalid vpn acc User mxr do_sum (u_next_base p1)
                 (mword_of_int 0) g'' a0 s Hrd0 pte_invalid_zero).
      + apply (goodmb_pt_walk_user_sub vpn acc User mxr do_sum Du_r Du_w
                 (ud_root P) p2 s mm Hrd2 Hrd2g
                 (fun Db s0 => goodb_pte_is_invalid_valid p2 Db s0 Hv2) Hv2 Hn2).
        intros g' a1.
        apply (goodmb_rec_walk_l1_sub vpn acc User mxr do_sum Du_r Du_w
                 (u_next_base p2) p1 g' a1 s mm Hrd1 Hrd1g
                 (fun Db s0 => goodb_pte_is_invalid_valid p1 Db s0 Hv1) Hv1 Hn1).
        intros g'' a0.
        exact (goodmb_rec_walk_leaf_invalid vpn acc User mxr do_sum Du_r Du_w
                 (u_next_base p1) (mword_of_int 0) g'' a0 s mm Hrd0 Hrd0g
                 (fun Db s0 => goodb_pte_is_invalid_zero Db s0) pte_invalid_zero). }
  destruct Hwalk as (Hw & Hwg). split.
  - exact (exec_translate_walk_user_err vpn acc User mxr do_sum (mword_of_int 0)
             (ud_root P) (PTW_Invalid_PTE tt) s Hlk
             (exec_translate_TLB_miss_user_walk_err vpn acc User mxr do_sum
                (mword_of_int 0) (ud_root P) (PTW_Invalid_PTE tt) s Hw)).
  - exact (goodmb_translate_walk_user_err vpn acc User mxr do_sum Du_r Du_w
             (mword_of_int 0) (ud_root P) s mm
             ltac:(vm_compute; reflexivity) Hlk
             (goodmb_translate_TLB_miss_user_walk_err vpn acc User mxr do_sum Du_r Du_w
                (mword_of_int 0) (ud_root P) (PTW_Invalid_PTE tt) s mm Hw Hwg)).
Qed.

(* §6 THE DENIED WALK, both sides.  A mapped leaf whose flags deny this
   access: the walk reaches the leaf and the check fails, and a RESIDENT
   entry replays the stored check and fails the same way.  Neither path
   writes anything. *)

Lemma u_translate_denied (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (acc : MemoryAccessType mem_payload) (w va : mword 64) (mxr do_sum : bool) :
  u_mem_wf P t mm ->
  u_exec_pins P t rs ->
  upt_leaf_at (ud_tfp P) (ud_um P) (svpn_of va) w ->
  uleaf_denied acc w ->
  exec (is_shadow_stack_access acc) (u_state rs mm) = Some (false, u_state rs mm) ->
  exec (translate 39 (mword_of_int 0 : mword 16) (ud_root P) (svpn_of va) acc User
          mxr do_sum tt) (u_state rs mm)
    = Some (Err (PTW_No_Permission tt, tt), u_state rs mm)
  /\ goodmb Du_r Du_w
       (translate 39 (mword_of_int 0 : mword 16) (ud_root P) (svpn_of va) acc User
          mxr do_sum tt) (u_state rs mm) mm = true.
Proof.
  intros Hwf Hpins Hleaf Hden Hss.
  pose proof Hwf as (md & _ & _ & _ & _ & _ & _ & _ & Hwfm & Hspec).
  pose proof Hspec as (Hbase & _).
  pose proof Hpins as (_ & _ & _ & Htlbok).
  set (s := u_state rs mm) in *.
  set (vpn := svpn_of va) in *.
  destruct (upt_spec_maps (ud_root P) (ud_tfp P) (ud_um P) t vpn w Hspec Hleaf)
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                       Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & _ & _).
  (* the leaf's per-variant certificate: the check is register-free at a
     DENIED leaf, exactly as it is at a permitted one *)
  assert (Hgchk : forall (a d : mword 1) (mxr0 do_sum0 : bool)
                    (Db : register -> bool) (s0 : mstate),
            goodb Db (check_PTE_permission acc User mxr0 do_sum0
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true).
  { intros a d mxr0 do_sum0 Db s0.
    exact (goodb_check_PTE_permission_denied acc (pte_set_ad w a d) mxr0 do_sum0
             Db s0 s Hss (Hden a d mxr0 do_sum0)). }
  (* the three slot reads *)
  assert (H2 : word_bytes (u_pte_addr (ud_root P) (vpn_idx 2 vpn)) p2 ∈ pt_maps 2 t).
  { rewrite <- Hbase. exact (ptree_maps_slot2 t vpn p2 p1 _ Hmaps). }
  destruct (u_slot_read P t mm rs (ud_root P) (vpn_idx 2 vpn) p2 Hwf Hpins H2)
    as (Hrd2 & Hrd2g).
  destruct (u_slot_read P t mm rs (u_next_base p2) (vpn_idx 1 vpn) p1 Hwf Hpins
              (ptree_maps_slot1 t vpn p2 p1 _ Hmaps)) as (Hrd1 & Hrd1g).
  destruct (u_slot_read P t mm rs (u_next_base p1) (vpn_idx 0 vpn) _ Hwf Hpins
              (ptree_maps_slot0 t vpn p2 p1 _ Hmaps)) as (Hrd0 & Hrd0g).
  (* the WALK-denied path, shared by the empty-slot and foreign-entry cases *)
  assert (Hwalk : exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
    exec (translate 39 (mword_of_int 0 : mword 16) (ud_root P) vpn acc User
            mxr do_sum tt) s = Some (Err (PTW_No_Permission tt, tt), s)
    /\ goodmb Du_r Du_w
         (translate 39 (mword_of_int 0 : mword 16) (ud_root P) vpn acc User
            mxr do_sum tt) s mm = true).
  { intros Hlk. split.
    - exact (exec_translate_pt_denied acc User mxr do_sum vpn (ud_root P)
               p2 p1 (pte_set_ad w a0 d0) s Hv2 Hn2 Hv1 Hn1 Hv0 Hl0
               (Hden a0 d0 mxr do_sum) Hrd2 Hrd1 Hrd0 Hlk).
    - apply (goodmb_translate_walk_user_err vpn acc User mxr do_sum Du_r Du_w
               (mword_of_int 0) (ud_root P) s mm
               ltac:(vm_compute; reflexivity) Hlk).
      apply (goodmb_translate_TLB_miss_user_walk_err vpn acc User mxr do_sum Du_r Du_w
               (mword_of_int 0) (ud_root P) (PTW_No_Permission tt) s mm).
      + apply (exec_pt_walk_user_sub vpn acc User mxr do_sum (ud_root P) p2 _ s
                 Hrd2 Hv2 Hn2).
        intros g' a1.
        apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum (u_next_base p2) p1 g' _ a1 s
                 Hrd1 Hv1 Hn1).
        intros g'' a1'.
        change (PTW_No_Permission tt) with (ext_get_ptw_error (PTE_No_Permission tt)).
        exact (exec_rec_walk_leaf_noperm vpn acc User mxr do_sum (u_next_base p1)
                 (pte_set_ad w a0 d0) g'' (PTE_No_Permission tt) a1' s Hrd0 Hv0 Hl0
                 (fun s0 => Hden a0 d0 mxr do_sum s0)).
      + apply (goodmb_pt_walk_user_sub vpn acc User mxr do_sum Du_r Du_w
                 (ud_root P) p2 s mm Hrd2 Hrd2g
                 (fun Db s0 => goodb_pte_is_invalid_valid p2 Db s0 Hv2) Hv2 Hn2).
        intros g' a1.
        apply (goodmb_rec_walk_l1_sub vpn acc User mxr do_sum Du_r Du_w
                 (u_next_base p2) p1 g' a1 s mm Hrd1 Hrd1g
                 (fun Db s0 => goodb_pte_is_invalid_valid p1 Db s0 Hv1) Hv1 Hn1).
        intros g'' a1'.
        exact (goodmb_rec_walk_leaf_noperm vpn acc User mxr do_sum Du_r Du_w
                 (u_next_base p1) (pte_set_ad w a0 d0) g'' (PTE_No_Permission tt) a1'
                 s mm Hrd0 Hrd0g
                 (fun Db s0 => goodb_pte_is_invalid_valid _ Db s0 Hv0)
                 Hv0 Hl0 (Hgchk a0 d0 mxr do_sum)
                 (fun s0 => Hden a0 d0 mxr do_sum s0)). }
  (* WHICH PATH: the TLB slot decides *)
  destruct (vec_access_dec (register_lookup tlb rs) (tlb_hash (__id 39) vpn))
    as [ent|] eqn:Hslot.
  - destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & q0 & a' & d' & Hm0' & Hh & ->).
    destruct (decide (vpn0 = vpn)) as [-> | Hne].
    + (* an A/D-variant of our OWN entry is resident: the hit replays the check *)
      destruct (ptree_maps_det t vpn q2 q1 q0 p2 p1 (pte_set_ad w a0 d0) Hm0' Hmaps)
        as (-> & -> & ->).
      assert (Hdenc : pte_check_denied acc User mxr do_sum (PTE_No_Permission tt)
                        (pte_set_ad (pte_set_ad w a0 d0) a' d')).
      { rewrite (pte_set_ad_absorb w a0 d0 a' d'). apply Hden. }
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) s
                    = Some (Some (tlb_hash (__id 39) vpn,
                                  u_walk_entry vpn p2 p1
                                    (pte_set_ad (pte_set_ad w a0 d0) a' d')
                                    (mword_of_int 0)), s))
        by exact (exec_lookup_TLB_hit_ent vpn (mword_of_int 0)
                    (register_lookup tlb rs) _ s eq_refl Hslot
                    (uwe_match_self vpn p2 p1 _)).
      split.
      * unfold translate.
        rewrite (exec_bind_Some _ _ _ _ _ Hlk). cbn match.
        apply (exec_translate_TLB_hit_denied_pt acc User mxr do_sum
                 vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')
                 (mword_of_int 0) (tlb_hash (__id 39) vpn) s Hdenc).
      * apply (goodmb_translate_hit_err Du_r Du_w acc User mxr do_sum
                 (mword_of_int 0) (ud_root P) vpn (tlb_hash (__id 39) vpn) _ s mm
                 ltac:(vm_compute; reflexivity) Hlk).
        apply (goodmb_translate_TLB_hit_denied_pt Du_r Du_w acc User mxr do_sum
                 vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')
                 (mword_of_int 0) (tlb_hash (__id 39) vpn) s mm).
        -- intros Db s0. rewrite (pte_set_ad_absorb w a0 d0 a' d').
           exact (Hgchk a' d' mxr do_sum Db s0).
        -- exact Hdenc.
    + (* a FOREIGN entry: the tag rejects it, the walk runs and denies *)
      apply Hwalk.
      exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _
               (register_lookup tlb rs) s eq_refl Hslot
               (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a' d')
                  (mword_of_int 0) Hne)).
  - (* the slot is empty: the walk runs and denies *)
    apply Hwalk.
    exact (exec_lookup_TLB_miss vpn (mword_of_int 0) (register_lookup tlb rs) s
             eq_refl Hslot).
Qed.

(* §7 [u_translate_fault_pure] *)

Lemma u_translate_fault_pure (P : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rs : regstate) (acc : MemoryAccessType mem_payload) (e : ExceptionType)
    (va : mword 64) :
  u_fault_flavor acc (ud_tfp P) (ud_um P) va ->
  exec (translationException acc (PTW_Invalid_Addr tt)) (u_state rs mm)
    = Some (e, u_state rs mm) ->
  exec (translationException acc (PTW_Invalid_PTE tt)) (u_state rs mm)
    = Some (e, u_state rs mm) ->
  exec (translationException acc (PTW_No_Permission tt)) (u_state rs mm)
    = Some (e, u_state rs mm) ->
  exec (effectivePrivilege acc (register_lookup mstatus rs) User) (u_state rs mm)
    = Some (User, u_state rs mm) ->
  exec (is_shadow_stack_access acc) (u_state rs mm) = Some (false, u_state rs mm) ->
  register_lookup cur_privilege rs = User ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exec (translateAddr (Virtaddr va) acc) (u_state rs mm)
    = Some (Err (e, tt), u_state rs mm)
  /\ goodmb Du_r Du_w (translateAddr (Virtaddr va) acc) (u_state rs mm) mm = true.
Proof.
  intros Hflavor Hte1 Hte2 Hte3 Heff Hss Lcp Lsxl Hpins Hwf.
  pose proof Hpins as (Hhw & _ & Hpt & Htlbok).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & _).
  destruct Hsatpok as (Hmode & Hasid & Hppn & _).
  pose proof Hwf as (md & _ & _ & _ & _ & _ & _ & _ & _ & Hspec).
  pose proof Hspec as (Hbase & _ & _ & _ & Hblkspec).
  set (s := u_state rs mm) in *.
  (* the probes' certificates, off the exec facts the caller supplies *)
  assert (Heffg : goodb Du_r
            (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s = true)
    by exact (u_eff_goodb acc (register_lookup mstatus rs) User s Heff Du_r s).
  assert (Hssg : goodb Du_r (is_shadow_stack_access acc) s = true)
    by exact (u_ssa_goodb acc s Hss Du_r s).
  assert (Htm : exec (translationMode User) s = Some (Sv39, s))
    by exact (exec_translationMode_U_sv39 usatp s Lsxl Hsatp Hmode).
  assert (Htmg : goodb Du_r (translationMode User) s = true)
    by exact (goodb_translationMode_U Du_r usatp s
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lsxl Hsatp Hmode).
  destruct Hflavor as
    [ Hnc | [ (Hcanon & Hnone & Hnt & Hntf) | (Hcanon & w & Hleaf & Hden) ] ].
  - (* NON-CANONICAL: the fault fires before the TLB or any memory read *)
    split.
    + exact (exec_translateAddr_pt_front_noncanon acc User e usatp va s
               Heff Hss Lcp Htm Hsatp Hnc Hte1).
    + exact (goodmb_translateAddr_pt_front_noncanon Du_r Du_w acc User
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               e usatp va s mm Heff Heffg Hss Hssg Lcp Htm Htmg Hsatp Hnc Hte1
               (u_texc_goodb acc (PTW_Invalid_Addr tt) e s Hte1 Du_r s)).
  - (* UNMAPPED: never TLB-resident, and the walk stops at a ZERO word *)
    assert (Hblk : ptree_blocks0 t (svpn_of va))
      by exact (Hblkspec (svpn_of va) Hnt Hntf Hnone).
    assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) (svpn_of va)) s
                  = Some (None, s))
      by exact (tlb_ok_pt_lookup_blocked t (svpn_of va) (register_lookup tlb rs) s
                  Htlbok (ptree_blocks0_blocks t (svpn_of va) Hblk) eq_refl).
    assert (Htr : forall mxr do_sum,
              exec (translate 39 (mword_of_int 0 : mword 16) (ud_root P)
                      (svpn_of va) acc User mxr do_sum tt) s
              = Some (Err (PTW_Invalid_PTE tt, tt), s))
      by (intros mxr do_sum;
          exact (proj1 (u_translate_blocked P t mm rs acc (svpn_of va) mxr do_sum
                          Hwf Hpins Hblk Hlk))).
    assert (Htrg : forall mxr do_sum,
              goodmb Du_r Du_w (translate 39 (mword_of_int 0 : mword 16) (ud_root P)
                      (svpn_of va) acc User mxr do_sum tt) s mm = true)
      by (intros mxr do_sum;
          exact (proj2 (u_translate_blocked P t mm rs acc (svpn_of va) mxr do_sum
                          Hwf Hpins Hblk Hlk))).
    split.
    + exact (exec_translateAddr_pt_front_err acc User (svpn_of va) (ud_root P)
               (PTW_Invalid_PTE tt) e usatp va s
               Heff Hss Lcp Htm Hsatp Hppn Hasid Hcanon eq_refl Htr Hte2).
    + exact (goodmb_translateAddr_pt_front_err Du_r Du_w acc User
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               (svpn_of va) (ud_root P) (PTW_Invalid_PTE tt) e usatp va s mm
               Heff Heffg Hss Hssg Lcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
               Htr Htrg Hte2 (u_texc_goodb acc (PTW_Invalid_PTE tt) e s Hte2 Du_r s)).
  - (* DENIED: the leaf is reached (or replayed off the TLB) and refuses *)
    assert (Htr : forall mxr do_sum,
              exec (translate 39 (mword_of_int 0 : mword 16) (ud_root P)
                      (svpn_of va) acc User mxr do_sum tt) s
              = Some (Err (PTW_No_Permission tt, tt), s))
      by (intros mxr do_sum;
          exact (proj1 (u_translate_denied P t mm rs acc w va mxr do_sum
                          Hwf Hpins Hleaf Hden Hss))).
    assert (Htrg : forall mxr do_sum,
              goodmb Du_r Du_w (translate 39 (mword_of_int 0 : mword 16) (ud_root P)
                      (svpn_of va) acc User mxr do_sum tt) s mm = true)
      by (intros mxr do_sum;
          exact (proj2 (u_translate_denied P t mm rs acc w va mxr do_sum
                          Hwf Hpins Hleaf Hden Hss))).
    split.
    + exact (exec_translateAddr_pt_front_err acc User (svpn_of va) (ud_root P)
               (PTW_No_Permission tt) e usatp va s
               Heff Hss Lcp Htm Hsatp Hppn Hasid Hcanon eq_refl Htr Hte3).
    + exact (goodmb_translateAddr_pt_front_err Du_r Du_w acc User
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               (svpn_of va) (ud_root P) (PTW_No_Permission tt) e usatp va s mm
               Heff Heffg Hss Hssg Lcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
               Htr Htrg Hte3 (u_texc_goodb acc (PTW_No_Permission tt) e s Hte3 Du_r s)).
Qed.

(* ===================================================================== *)
(* 8. [u_fetch_fault_pure] -- THE [F_Error] ARM OF [fetch].                *)
(*                                                                        *)
(* [UserFetchCert] has only the SUCCESS arm ([u_fetch_pure]), so           *)
(* [HartRunFull.run_fetch_post]'s [F_Error] arm had no producer.  The      *)
(* premise is the fetch's own flavour predicate                            *)
(* ([UserFetchPt.u_fetch_fault_flavor], which                              *)
(* [UserActiveClass.fetch_classify] produces); everything below the        *)
(* translation is [UserFetch]'s own plumbing, so the two shells here are   *)
(* [exec_fetch_bytes_fault] / [exec_fetch_fault_4]'s twins.                *)
(*                                                                        *)
(* [fetch_bytes] IS the [catch_early_return] region that THROWS -- the     *)
(* [Err] arm is an [early_return] -- so its certificate keeps the wrapper  *)
(* ON and is peeled with [gm_cer_bind], ending at [mcer_early_return]'s    *)
(* conversion.  The whole [fetch] does NOT throw (the [F_Error] value is   *)
(* returned normally), so its own wrapper comes off with [goodmb_cer].     *)
(*                                                                        *)
(* THE STATE DOES NOT MOVE, so where [u_fetch_pure] exhibits [rsf'],       *)
(* [mm'] and [t'] this one has nothing to exhibit: the landing-file        *)
(* disjunct would read [rsf = rsf] and is left out, and the last two       *)
(* conjuncts are stated at the INCOMING tree and map, which is exactly     *)
(* what [UserClassifyAsm.u_landing_map] needs of them.                     *)
(* ===================================================================== *)



Lemma goodmb_fetch_bytes_fault (Dr Dw : register -> bool) (width : Z)
    (fs gs : mword 64) (ex : ExceptionType) (s s' : mstate) (mm : PtBytes.pamap) :
  exec (translateAddr (Virtaddr gs) (InstructionFetch tt)) s
    = Some (Err (ex, tt), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr gs) (InstructionFetch tt)) s mm = true ->
  goodmb Dr Dw (fetch_bytes fs gs width) s mm = true.
Proof.
  intros Htr Htrg.
  unfold fetch_bytes.
  change (ext_fetch_check_pc fs gs) with (@None unit). cbv iota beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
    assert (Htrs : execR (Defs.bind0 a b) s
                   = Some (inr (Err (ex, tt)), s'));
    [ | assert (Htrsg : goodmb Dr Dw (Defs.bind0 a b) s mm = true) ] end.
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
  { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    apply goodmb_liftR. exact Htrg. }
  erewrite (gm_cer_bind Dr Dw _ _ s s' mm _ Htrsg Htrs). cbv iota beta.
  reflexivity.
Qed.

Section FetchFault4Cert.
  Context (Dr Dw : register -> bool).
  Context (s : mstate) (mm : PtBytes.pamap) (pc : mword 64) (ex : ExceptionType).
  Hypothesis HDpc : Dr PC = true.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr pc) (InstructionFetch tt)) s
                   = Some (Err (ex, tt), s).
  Hypothesis Htrg : goodmb Dr Dw (translateAddr (Virtaddr pc) (InstructionFetch tt))
                      s mm = true.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  Let HrdPCg : goodmb Dr Dw (Defs.read_reg PC : M _) s mm = true.
  Proof. rewrite goodmb_read_reg. exact HDpc. Qed.

  Lemma goodmb_fetch_fault_4 : goodmb Dr Dw (fetch tt) s mm = true.
  Proof using Dr Dw s mm pc ex HDpc HpcPC Hvalign Htr Htrg.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    unfold fetch. apply goodmb_cer.
    change (get_config_rvfi tt) with false. cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    gmm_lift HrdPCg HrdPC.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Halg : goodmb Dr Dw A s mm = true);
      [ | assert (Hale : execR A s = Some (inr false, s)) ] end.
    { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      unfold Defs.or_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hbit0. rewrite bindR_ret. cbv iota beta.
      unfold Defs.and_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hbit1. rewrite bindR_ret. cbv iota beta. reflexivity. }
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_returnR_fwd. }
      cbv iota beta.
      unfold Defs.and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
    erewrite (gm_bindR Dr Dw _ _ s s mm false Halg Hale). cbv iota beta.
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Hzg : goodmb Dr Dw A s mm = true);
      [ | assert (Hze : execR A s = Some (inr true, s)) ] end.
    { unfold Defs.and_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hvalign. rewrite bindR_ret. cbv iota beta.
      apply goodmb_liftR. apply goodmb_currentlyEnabled_Ziccif. }
    { unfold Defs.and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
          apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif.
      cbn match. reflexivity. }
    erewrite (gm_bindR Dr Dw _ _ s s mm true Hzg Hze). cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    gmm_lift HrdPCg HrdPC.
    erewrite gm_liftR_seq;
      [ | exact (goodmb_fetch_bytes_fault Dr Dw 4 pc pc ex s s mm Htr Htrg)
        | exact (exec_fetch_bytes_fault 4 pc pc ex s s Htr) ].
    cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    apply goodmb_returnm.
  Qed.

End FetchFault4Cert.

Lemma u_fetch_fault_pure (P : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rsf : regstate) (va : mword 64) (mi : bool) :
  UserFetchPt.u_fetch_fault_flavor (ud_tfp P) (ud_um P) va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  post_fetch_cfg (u_state rsf mm) va mi ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exec (fetch tt) (u_state rsf mm)
    = Some (F_Error (E_Fetch_Page_Fault tt, va), u_state rsf mm)
  /\ goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true
  /\ tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rsf)
  /\ u_mem_step P t t mm mm.
Proof.
  intros Hflavor Hal Hcfg Hpins Hwf.
  pose proof Hcfg as (Lpc & Lcp & Lms & Lmenv & _ & _).
  destruct Lms as (Lsxl & _).
  pose proof Hpins as (_ & _ & _ & Htlbok).
  set (s := u_state rsf mm) in *.
  destruct (u_translate_fault_pure P t mm rsf (InstructionFetch tt)
              (E_Fetch_Page_Fault tt) va Hflavor
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              (exec_effectivePrivilege_fetch (register_lookup mstatus rsf) User s)
              (exec_is_shadow_stack_fetch s) Lcp Lsxl Hpins Hwf)
    as (Htr & Htrg).
  split_and!.
  - exact (exec_fetch_fault_4 s va Lpc (E_Fetch_Page_Fault tt) Hal Htr).
  - exact (goodmb_fetch_fault_4 Du_r Du_w s mm va (E_Fetch_Page_Fault tt)
             ltac:(vm_compute; reflexivity) Lpc Hal Htr Htrg).
  - exact Htlbok.
  - exact (u_mem_step_refl P t mm Hwf).
Qed.

(* ===================================================================== *)
(* 9. THE 2-ALIGNED (SPLIT) FETCH, CERTIFIED.                             *)
(*                                                                        *)
(* [UserFetch] section 6's four [exec] reductions -- [exec_fetch_rvc_2],   *)
(* [exec_fetch_base_2], [exec_fetch_fault_2_second] and                    *)
(* [exec_fetch_fault_2_first] -- get their [goodmb] twins here, node for   *)
(* node against that section's [split_head].                              *)
(*                                                                        *)
(* The head differs from the 4-aligned one ([UserFetchCert.goodmb_fetch_   *)
(* ok_4] / [goodmb_fetch_fault_4] above) only in WHICH WAY the guards go:  *)
(* bit0 = 0 and bit1 = 1 with [Ext_Zca] ENABLED, so the misalignment test  *)
(* is still false (the model's third conjunct is [not (currentlyEnabled    *)
(* Ext_Zca)]), and then [is_aligned_vaddr .. 4] = false, which takes the   *)
(* width-2 arm instead of the width-4 one.  The tails are the SAME two     *)
(* width-generic bricks at width 2 ([UserFetchCert.goodmb_fetch_bytes_ok]  *)
(* and [goodmb_fetch_bytes_fault] above), plus, on the straddle, the       *)
(* second halfword's own pair at the state the first one left.            *)
(*                                                                        *)
(* [goodmb]'s MAP ARGUMENT IS THE PRE MAP [mm] THROUGHOUT, even where the  *)
(* exec facts move the state (s -> s1 -> s2): that is                      *)
(* [HartMemAsm.mm_after_dom]'s point, and [goodmb_fetch_ok_4] already      *)
(* does it.                                                               *)
(* ===================================================================== *)

(* THE [Ext_Zca] GATE, CERTIFIED.  [goodmb_currentlyEnabled_Ziccif] closes
   by computation because the [Ziccif] gate is register-FREE; the [Zca]
   gate is not -- it is [and_boolM (hartSupports Ext_Zca) (or_boolM
   (currentlyEnabled Ext_C) (not (hartSupports Ext_C)))] and the middle
   arm reads [misa].  So the certificate holds exactly when [Dr misa], and
   it is assembled with [DecodeTotalU]'s structural [goodb] rules, whose
   [_forall] shape means neither arm of the [misa] test has to be decided.
   The [Acc] argument is DESTRUCTED only where the recursion is actually
   entered: [Zwf_guarded] reduces on its own, and destructing it turns a
   computable [hartSupports] leaf into a stuck one. *)
Lemma goodb_rec_currentlyEnabled_C (D : register -> bool) (k : Z)
    (acc : Acc (Zwf 0) k) (s : mstate) :
  D misa = true -> Z.geb k 0 = true ->
  goodb D (_rec_currentlyEnabled Ext_C k acc) s = true.
Proof.
  intros HD Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  apply DecodeTotalU.goodb_bind_forall; [ reflexivity | intros ? ].
  apply DecodeTotalU.goodb_and_boolM; [ vm_compute; reflexivity | ].
  apply DecodeTotalU.goodb_bind_read_reg; [ exact HD | reflexivity ].
Qed.

Lemma goodb_currentlyEnabled_Zca (D : register -> bool) (s : mstate) :
  D misa = true -> goodb D (currentlyEnabled Ext_Zca) s = true.
Proof.
  intro HD. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zca) 0) with true
    by (vm_compute; reflexivity).
  cbn match.
  apply DecodeTotalU.goodb_bind_forall; [ reflexivity | intros ? ].
  apply DecodeTotalU.goodb_and_boolM; [ vm_compute; reflexivity | ].
  apply DecodeTotalU.goodb_or_boolM.
  - apply goodb_rec_currentlyEnabled_C; [ exact HD | vm_compute; reflexivity ].
  - apply DecodeTotalU.goodb_bind_forall;
      [ vm_compute; reflexivity | intros ?; reflexivity ].
Qed.

Lemma goodmb_currentlyEnabled_Zca (Dr Dw : register -> bool) (s : mstate)
    (mm : PtBytes.pamap) :
  Dr misa = true -> goodmb Dr Dw (currentlyEnabled Ext_Zca) s mm = true.
Proof.
  intro HD. apply goodmb_of_goodb. exact (goodb_currentlyEnabled_Zca Dr s HD).
Qed.

Section FetchSplit2Cert.
  Context (Dr Dw : register -> bool).
  Context (s s1 : mstate) (mm : PtBytes.pamap) (va pa : mword 64).
  Hypothesis HDpc : Dr PC = true.
  Hypothesis HDmisa : Dr misa = true.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HmisaC :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
  Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (va, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  Let HrdPCg : goodmb Dr Dw (Defs.read_reg PC : M _) s mm = true.
  Proof. rewrite goodmb_read_reg. exact HDpc. Qed.

  (* [UserFetch.split_head]'s twin: peel [fetch] down to the width-2
     [fetch_bytes] at [va], carrying the certificate and the [execR]
     value of each guard side by side. *)
  Local Ltac gsplit_head :=
    unfold fetch; apply goodmb_cer;
    change (get_config_rvfi tt) with false; cbv iota beta;
    gmm_lift HrdPCg HrdPC;
    gmm_lift HrdPCg HrdPC;
    change (ext_fetch_check_pc va va) with (@None unit); cbv iota beta;
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Halg : goodmb Dr Dw A s mm = true) by
        ( erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ];
          unfold Defs.or_boolM;
          erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ];
          rewrite Hbit0; rewrite bindR_ret; cbv iota beta;
          unfold Defs.and_boolM;
          erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ];
          rewrite Hbit1; rewrite bindR_ret; cbv iota beta;
          gmm_lift (goodmb_currentlyEnabled_Zca Dr Dw s mm HDmisa)
                   (exec_currentlyEnabled_Zca s HmisaC);
          reflexivity );
      assert (Hale : execR A s = Some (inr false, s)) by
        ( rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s));
          unfold Defs.or_boolM;
          rewrite (execR_bind_Some _ _ _ false s);
          [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hbit0;
              apply execR_returnR_fwd ];
          cbv iota beta;
          unfold Defs.and_boolM;
          rewrite (execR_bind_Some _ _ _ true s);
          [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hbit1;
              apply execR_returnR_fwd ];
          cbv iota beta;
          rewrite (execR_bind_Some _ _ _ true s);
          [ | rewrite execR_liftR; rewrite (exec_currentlyEnabled_Zca s HmisaC);
              cbn match; apply execR_returnR_fwd ];
          cbv iota beta; reflexivity );
      erewrite (gm_bindR Dr Dw _ _ s s mm false Halg Hale)
    end;
    cbv iota beta;
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Hzg : goodmb Dr Dw A s mm = true) by
        ( unfold Defs.and_boolM;
          erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ];
          rewrite Hvalign4; rewrite bindR_ret; cbv iota beta; reflexivity );
      assert (Hze : execR A s = Some (inr false, s)) by
        ( unfold Defs.and_boolM;
          rewrite (execR_bind_Some _ _ _ false s);
          [ | rewrite (execR_liftR_seq _ _ _ _ _ HrdPC); rewrite Hvalign4;
              apply execR_returnR_fwd ];
          cbv iota beta; reflexivity );
      erewrite (gm_bindR Dr Dw _ _ s s mm false Hzg Hze)
    end;
    cbv iota beta;
    gmm_lift HrdPCg HrdPC;
    gmm_lift HrdPCg HrdPC.

  (* --- the FIRST halfword translates and reads --- *)
  Section FirstHalfOkCert.
    Context (ilo : mword 16).
    Hypothesis Htrl : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
                      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1).
    Hypothesis Htrlg :
      goodmb Dr Dw (translateAddr (Virtaddr va) (InstructionFetch tt)) s mm = true.
    Hypothesis Hmrl : exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2
                              false false false) s1 = Some (Ok ilo, s1).
    Hypothesis Hmrlg : goodmb Dr Dw (mem_read (InstructionFetch tt) PBMT_PMA
                         (Physaddr pa) 2 false false false) s1 mm = true.

    Let Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1).
    Proof.
      rewrite (exec_fetch_bytes_ok 2 va va pa ilo s s1 Htrl Hmrl).
      rewrite autocast_mword_id_16. reflexivity.
    Qed.

    Let Hfb2lg : goodmb Dr Dw (fetch_bytes va va 2) s mm = true.
    Proof.
      exact (goodmb_fetch_bytes_ok Dr Dw 2 va va pa ilo s s1 mm
               Htrl Htrlg Hmrl Hmrlg).
    Qed.

    (* RVC: the low halfword is a compressed instruction *)
    Lemma goodmb_fetch_rvc_2 :
      isRVC ilo = true ->
      goodmb Dr Dw (fetch tt) s mm = true.
    Proof using Dr Dw s s1 mm va pa ilo HDpc HDmisa HpcPC HmisaC Hbit0 Hbit1
                Hvalign4 Htrl Htrlg Hmrl Hmrlg.
      intros HisRVC.
      gsplit_head.
      gmm_lift Hfb2lg Hfb2l.
      cbv iota beta.
      match goal with
      | |- context [isRVC ?x] =>
          replace (isRVC x) with true by (symmetry; exact HisRVC)
      end.
      cbv iota beta. reflexivity.
    Qed.

    Section SecondHalfCert.
      Context (s2 : mstate) (pah : mword 64).
      Hypothesis HpcPC1 : register_lookup PC s1.(sregs) = va.
      Hypothesis HnotRVC : isRVC ilo = false.

      Let HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1).
      Proof. rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. Qed.

      Let HrdPC1g : goodmb Dr Dw (Defs.read_reg PC : M _) s1 mm = true.
      Proof. rewrite goodmb_read_reg. exact HDpc. Qed.

      (* BASE: the second halfword translates (possibly onto ANOTHER page)
         and reads at the moved state *)
      Lemma goodmb_fetch_base_2 (ihi : mword 16) :
        exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) s1
          = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
        goodmb Dr Dw (translateAddr (Virtaddr (add_vec_int va 2))
                        (InstructionFetch tt)) s1 mm = true ->
        exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2
                false false false) s2 = Some (Ok ihi, s2) ->
        goodmb Dr Dw (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2
                 false false false) s2 mm = true ->
        goodmb Dr Dw (fetch tt) s mm = true.
      Proof using Dr Dw s s1 s2 mm va pa pah ilo HDpc HDmisa HpcPC HmisaC Hbit0
                  Hbit1 Hvalign4 Htrl Htrlg Hmrl Hmrlg HpcPC1 HnotRVC.
        intros Htrh Htrhg Hmrh Hmrhg.
        assert (Hfb2h : exec (fetch_bytes va (add_vec_int va 2) 2) s1
                        = Some (@FetchBytes_Success 2 ihi, s2)).
        { rewrite (exec_fetch_bytes_ok 2 va (add_vec_int va 2) pah ihi s1 s2
                     Htrh Hmrh).
          rewrite autocast_mword_id_16. reflexivity. }
        assert (Hfb2hg : goodmb Dr Dw (fetch_bytes va (add_vec_int va 2) 2)
                           s1 mm = true).
        { exact (goodmb_fetch_bytes_ok Dr Dw 2 va (add_vec_int va 2) pah ihi
                   s1 s2 mm Htrh Htrhg Hmrh Hmrhg). }
        gsplit_head.
        gmm_lift Hfb2lg Hfb2l.
        cbv iota beta.
        match goal with
        | |- context [isRVC ?x] =>
            replace (isRVC x) with false by (symmetry; exact HnotRVC)
        end.
        cbv iota beta.
        gmm_lift HrdPC1g HrdPC1.
        gmm_lift HrdPC1g HrdPC1.
        gmm_lift Hfb2hg Hfb2h.
        cbv iota beta. reflexivity.
      Qed.

      (* the SECOND halfword's translation faults: the reported va is pc+2 *)
      Lemma goodmb_fetch_fault_2_second (ex : ExceptionType) :
        exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) s1
          = Some (Err (ex, tt), s1) ->
        goodmb Dr Dw (translateAddr (Virtaddr (add_vec_int va 2))
                        (InstructionFetch tt)) s1 mm = true ->
        goodmb Dr Dw (fetch tt) s mm = true.
      Proof using Dr Dw s s1 mm va pa ilo HDpc HDmisa HpcPC HmisaC Hbit0
                  Hbit1 Hvalign4 Htrl Htrlg Hmrl Hmrlg HpcPC1 HnotRVC.
        intros Htrh Htrhg.
        gsplit_head.
        gmm_lift Hfb2lg Hfb2l.
        cbv iota beta.
        match goal with
        | |- context [isRVC ?x] =>
            replace (isRVC x) with false by (symmetry; exact HnotRVC)
        end.
        cbv iota beta.
        gmm_lift HrdPC1g HrdPC1.
        gmm_lift HrdPC1g HrdPC1.
        gmm_lift (goodmb_fetch_bytes_fault Dr Dw 2 va (add_vec_int va 2) ex
                    s1 s1 mm Htrh Htrhg)
                 (exec_fetch_bytes_fault 2 va (add_vec_int va 2) ex s1 s1 Htrh).
        cbv iota beta.
        gmm_lift HrdPC1g HrdPC1.
        reflexivity.
      Qed.

    End SecondHalfCert.
  End FirstHalfOkCert.

  (* the FIRST halfword's translation faults: the reported va is pc *)
  Lemma goodmb_fetch_fault_2_first (ex : ExceptionType) :
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Err (ex, tt), s) ->
    goodmb Dr Dw (translateAddr (Virtaddr va) (InstructionFetch tt)) s mm = true ->
    goodmb Dr Dw (fetch tt) s mm = true.
  Proof using Dr Dw s mm va HDpc HDmisa HpcPC HmisaC Hbit0 Hbit1 Hvalign4.
    intros Htr Htrg.
    gsplit_head.
    gmm_lift (goodmb_fetch_bytes_fault Dr Dw 2 va va ex s s mm Htr Htrg)
             (exec_fetch_bytes_fault 2 va va ex s s Htr).
    cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    reflexivity.
  Qed.

End FetchSplit2Cert.

(* ===================================================================== *)
(* 10. THE 2-ALIGNED PURE COMPOSERS -- the twins of                       *)
(*     [UserFetchCert.u_fetch_pure] and [u_fetch_fault_pure] for the      *)
(*     SPLIT geometry (bit0 = 0, bit1 = 1, not 4-aligned).                *)
(*                                                                        *)
(* Three lemmas, one per way the two halfword translations can go:         *)
(*   [u_fetch_pure_2]                 both halves fetchable;               *)
(*   [u_fetch_or_fault_pure_2_second] low half fetchable, high half faults;*)
(*   [u_fetch_fault_pure_2_first]     low half faults.                     *)
(*                                                                        *)
(* All three conclude in the shape [HartRunFull.run_fetch_post] consumes   *)
(* ([user-tier-port.md] section 14.6): the [FetchResult] is EXISTENTIAL    *)
(* with a constructor disjunct, the landing is [u_tlb_only] (which         *)
(* composes across the two walks, unlike the one-walk disjunction), and    *)
(* the certificate is delivered at the ORIGINAL map [mm].                  *)
(*                                                                        *)
(* THE SECOND WALK'S CERTIFICATE COMES OUT AT [mm1], NOT [mm], and the     *)
(* four shells in [FetchSplit2Cert] take every certificate at ONE shared   *)
(* map -- so it is transported by [HartMemRun.goodmb_dom] fed by           *)
(* [UserBytes.u_mem_step_dom] BEFORE the shell is applied.  The two READ   *)
(* certificates need no transport: [u_fetch_read_ok]'s [bytes_owned]       *)
(* conjunct is already stated at its FIRST map argument, which both calls  *)
(* instantiate to [mm].                                                    *)
(*                                                                        *)
(* BOTH DISJUNCTS OF THE SECOND-HALF FAULT LEMMA ARE LIVE, and that is not *)
(* a defect: the model reads the second halfword ONLY when the first is    *)
(* not compressed, so a compressed low half retires normally even though   *)
(* the next page is bad.                                                   *)
(* ===================================================================== *)

(* 2-alignment survives the +2 step.  [InstrBytes.align2_plus2] is the same
   fact but lives above this file in the dependency order; the page-offset
   modular law in [UserBits] gives it in four lines. *)
Lemma u_align2_plus2 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 2 = true ->
  is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true.
Proof.
  intro Hal.
  assert (Hdv : (2 | 4096)%Z) by (exists 2048; reflexivity).
  pose proof (aligned_even va 2 ltac:(exists 1; reflexivity) ltac:(lia) Hal) as Hev.
  pose proof (uint_add_vec_int_mod4096 va 2 ltac:(lia)) as Hm.
  rewrite !uint_unsigned in Hm.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite (uint_unsigned_n _).
  rewrite Z.rem_mod_nonneg; [ | apply bv_unsigned_in_range | lia ].
  rewrite (Znumtheory.Zmod_div_mod 2 4096 (bv_unsigned (add_vec_int va 2)))
    by (lia || exact Hdv).
  rewrite Hm.
  rewrite <- (Znumtheory.Zmod_div_mod 2 4096 (bv_unsigned va + 2))
    by (lia || exact Hdv).
  rewrite Zplus_mod, Hev. reflexivity.
Qed.

Lemma u_fetch_pure_2 (P : uptd) (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
    (w wh va : mword 64) (mi : bool) :
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (InstructionFetch tt) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  ud_um P !! svpn_of (add_vec_int va 2) = Some wh ->
  uleaf_ok (InstructionFetch tt) wh ->
  neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
                        (Z.sub 39 1) 0)) = false ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  post_fetch_cfg (u_state rsf mm) va mi ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exists (rsf' : regstate) (mm' : PtBytes.pamap) (t' : ptree) (fr : FetchResult),
    exec (fetch tt) (u_state rsf mm) = Some (fr, u_state rsf' mm') /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true /\
    ((exists h : mword 16, fr = F_RVC h) \/ (exists iw : mword 32, fr = F_Base iw)) /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hl Hleaf Hcanon Hlh Hleafh Hcanonh Hbit0 Hbit1 Hnal4 Hcfg Hpins Hwf.
  pose proof Hcfg as (Lpc & Lcp & Lms & Lmenv & Hal2 & _).
  pose proof Lms as (Lsxl & _).
  pose proof Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsf)) ('b"1") = true)
    by (rewrite Hmisa; vm_compute; reflexivity).
  (* ---- FIRST WALK, at [va] ---- *)
  destruct (u_walk_fetch_pure P t mm rsf w va Hl Hleaf Hcanon Lcp Lsxl Lmenv
              Hpins Hwf)
    as (rsf1 & mm1 & t1 & Htr1 & Htr1g & Hfile1 & Htlbok1 & Hstep1).
  assert (Tr1 : u_tlb_only rsf rsf1) by exact (u_tlb_only_land rsf rsf1 Hfile1).
  assert (Hwf1 : u_mem_wf P t1 mm1)
    by exact (u_mem_step_wf P t t1 mm mm1 Hwf Hstep1).
  (* ---- THE LOW HALFWORD, read at the state the first walk landed on ---- *)
  destruct (u_fetch_bytes_2 P t1 mm1 w va Hwf1 Hl Hal2) as (ilo & Hbytes1).
  destruct (u_fetch_read_ok P t t1 mm mm1 rsf rsf1 2 w va
              ltac:(lia) (Z.divide_factor_l 2 2048) ltac:(lia)
              ltac:(vm_compute; reflexivity) Hal2 Hl Lcp Hpins Hwf Hwf1 Tr1)
    as (region1 & HA1 & Hord1 & Hrange1 & HX1 & Hpmam1 & Halp1 & Hexecp1 &
        Hclint1 & Hsig1 & Hhtif1 & Hdev1 & Hown1 & Lcp1).
  assert (Hmr1 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                         (Physaddr (u_walk_pa w va)) 2 false false false)
                   (u_state rsf1 mm1) = Some (Ok ilo, u_state rsf1 mm1))
    by exact (exec_mem_read_fetch_2_U PBMT_PMA (u_walk_pa w va) region1 ilo
                (u_state rsf1 mm1) HA1 Hord1 Hrange1 HX1 Hpmam1 Halp1 Hexecp1
                Hclint1 Hsig1
                (within_htif_false (u_walk_pa w va) 2 (u_state rsf1 mm1) Hhtif1)
                Hdev1 Hbytes1 Lcp1).
  assert (Hmr1g : goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
                           (Physaddr (u_walk_pa w va)) 2 false false false)
                    (u_state rsf1 mm1) mm = true)
    by exact (goodmb_mem_read_fetch_2_U Du_r Du_w PBMT_PMA (u_walk_pa w va)
                region1 ilo (u_state rsf1 mm1) mm
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA1 Hord1 Hrange1 HX1 Hpmam1 Halp1 Hexecp1 Hclint1 Hsig1 Hhtif1
                Hdev1 Hown1 Hbytes1 Lcp1).
  destruct (isRVC ilo) eqn:Hrvc.
  - (* COMPRESSED: the fetch retires on the low halfword alone *)
    exists rsf1, mm1, t1, (F_RVC ilo). split_and!.
    + exact (exec_fetch_rvc_2 (u_state rsf mm) (u_state rsf1 mm1) va
               (u_walk_pa w va) Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1 Hrvc).
    + exact (goodmb_fetch_rvc_2 Du_r Du_w (u_state rsf mm) (u_state rsf1 mm1) mm
               va (u_walk_pa w va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Htr1g Hmr1 Hmr1g Hrvc).
    + left. exists ilo. reflexivity.
    + exact Tr1.
    + exact Htlbok1.
    + exact Hstep1.
  - (* NOT COMPRESSED: a SECOND, independent walk at [va+2] *)
    assert (Hpins1 : u_exec_pins P t1 rsf1)
      by exact (u_exec_pins_only P t t1 rsf rsf1 Tr1 Htlbok1 Hpins).
    assert (Lsxl1 : _get_Mstatus_SXL (register_lookup mstatus rsf1) = 'b"10")
      by (rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact Lsxl).
    assert (Lmenv1 : register_lookup menvcfg rsf1 = MENVCFG_S)
      by (rewrite (Tr1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
    assert (Lpc1 : register_lookup PC rsf1 = va)
      by (rewrite (Tr1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
    destruct (u_walk_fetch_pure P t1 mm1 rsf1 wh (add_vec_int va 2)
                Hlh Hleafh Hcanonh Lcp1 Lsxl1 Lmenv1 Hpins1 Hwf1)
      as (rsf2 & mm2 & t2 & Htr2 & Htr2g & Hfile2 & Htlbok2 & Hstep2).
    assert (Tr2 : u_tlb_only rsf1 rsf2)
      by exact (u_tlb_only_land rsf1 rsf2 Hfile2).
    assert (Tr12 : u_tlb_only rsf rsf2)
      by exact (u_tlb_only_trans rsf rsf1 rsf2 Tr1 Tr2).
    assert (Hwf2 : u_mem_wf P t2 mm2)
      by exact (u_mem_step_wf P t1 t2 mm1 mm2 Hwf1 Hstep2).
    (* THE TRANSPORT: the second walk's certificate is at [mm1]; the shell
       wants every certificate at [mm]. *)
    assert (Hdom1 : (dom mm : gset Arch.pa) = dom mm1)
      by (symmetry; exact (u_mem_step_dom P t t1 mm mm1 Hwf Hstep1)).
    assert (Htr2gm : goodmb Du_r Du_w (translateAddr (Virtaddr (add_vec_int va 2))
                              (InstructionFetch tt)) (u_state rsf1 mm1) mm = true).
    { rewrite (goodmb_dom Du_r Du_w
                 (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt))
                 (u_state rsf1 mm1) mm mm1 Hdom1).
      exact Htr2g. }
    (* ---- THE HIGH HALFWORD ---- *)
    assert (Hal2h : is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true)
      by exact (u_align2_plus2 va Hal2).
    destruct (u_fetch_bytes_2 P t2 mm2 wh (add_vec_int va 2) Hwf2 Hlh Hal2h)
      as (ihi & Hbytes2).
    destruct (u_fetch_read_ok P t t2 mm mm2 rsf rsf2 2 wh (add_vec_int va 2)
                ltac:(lia) (Z.divide_factor_l 2 2048) ltac:(lia)
                ltac:(vm_compute; reflexivity) Hal2h Hlh Lcp Hpins Hwf Hwf2 Tr12)
      as (region2 & HA2 & Hord2 & Hrange2 & HX2 & Hpmam2 & Halp2 & Hexecp2 &
          Hclint2 & Hsig2 & Hhtif2 & Hdev2 & Hown2 & Lcp2).
    assert (Hmr2 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                           (Physaddr (u_walk_pa wh (add_vec_int va 2))) 2
                           false false false)
                     (u_state rsf2 mm2) = Some (Ok ihi, u_state rsf2 mm2))
      by exact (exec_mem_read_fetch_2_U PBMT_PMA
                  (u_walk_pa wh (add_vec_int va 2)) region2 ihi
                  (u_state rsf2 mm2) HA2 Hord2 Hrange2 HX2 Hpmam2 Halp2 Hexecp2
                  Hclint2 Hsig2
                  (within_htif_false (u_walk_pa wh (add_vec_int va 2)) 2
                     (u_state rsf2 mm2) Hhtif2)
                  Hdev2 Hbytes2 Lcp2).
    assert (Hmr2g : goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
                             (Physaddr (u_walk_pa wh (add_vec_int va 2))) 2
                             false false false)
                      (u_state rsf2 mm2) mm = true)
      by exact (goodmb_mem_read_fetch_2_U Du_r Du_w PBMT_PMA
                  (u_walk_pa wh (add_vec_int va 2)) region2 ihi
                  (u_state rsf2 mm2) mm
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  HA2 Hord2 Hrange2 HX2 Hpmam2 Halp2 Hexecp2 Hclint2 Hsig2 Hhtif2
                  Hdev2 Hown2 Hbytes2 Lcp2).
    exists rsf2, mm2, t2, (F_Base (concat_vec ihi ilo)). split_and!.
    + exact (exec_fetch_base_2 (u_state rsf mm) (u_state rsf1 mm1) va
               (u_walk_pa w va) Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1
               (u_state rsf2 mm2) (u_walk_pa wh (add_vec_int va 2)) Lpc1 Hrvc
               ihi Htr2 Hmr2).
    + exact (goodmb_fetch_base_2 Du_r Du_w (u_state rsf mm) (u_state rsf1 mm1) mm
               va (u_walk_pa w va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Htr1g Hmr1 Hmr1g
               (u_state rsf2 mm2) (u_walk_pa wh (add_vec_int va 2)) Lpc1 Hrvc
               ihi Htr2 Htr2gm Hmr2 Hmr2g).
    + right. exists (concat_vec ihi ilo). reflexivity.
    + exact Tr12.
    + exact Htlbok2.
    + exact (u_mem_step_trans P t t1 t2 mm mm1 mm2 Hstep1 Hstep2).
Qed.

(* THE HIGH HALF'S PAGE IS BAD.  Both disjuncts are live -- see the section
   header: the model never looks at [va+2] when the low halfword is
   compressed, so the RVC outcome survives a faulting next page. *)
Lemma u_fetch_or_fault_pure_2_second (P : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rsf : regstate) (w va : mword 64) (mi : bool) :
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (InstructionFetch tt) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  UserFetchPt.u_fetch_fault_flavor (ud_tfp P) (ud_um P) (add_vec_int va 2) ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  post_fetch_cfg (u_state rsf mm) va mi ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exists (rsf' : regstate) (mm' : PtBytes.pamap) (t' : ptree) (fr : FetchResult),
    exec (fetch tt) (u_state rsf mm) = Some (fr, u_state rsf' mm') /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true /\
    ((exists h : mword 16, fr = F_RVC h)
     \/ (exists ex : ExceptionType, fr = F_Error (ex, add_vec_int va 2)
                                    /\ user_exc ex = true)) /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hl Hleaf Hcanon Hflavor Hbit0 Hbit1 Hnal4 Hcfg Hpins Hwf.
  pose proof Hcfg as (Lpc & Lcp & Lms & Lmenv & Hal2 & _).
  pose proof Lms as (Lsxl & _).
  pose proof Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsf)) ('b"1") = true)
    by (rewrite Hmisa; vm_compute; reflexivity).
  destruct (u_walk_fetch_pure P t mm rsf w va Hl Hleaf Hcanon Lcp Lsxl Lmenv
              Hpins Hwf)
    as (rsf1 & mm1 & t1 & Htr1 & Htr1g & Hfile1 & Htlbok1 & Hstep1).
  assert (Tr1 : u_tlb_only rsf rsf1) by exact (u_tlb_only_land rsf rsf1 Hfile1).
  assert (Hwf1 : u_mem_wf P t1 mm1)
    by exact (u_mem_step_wf P t t1 mm mm1 Hwf Hstep1).
  destruct (u_fetch_bytes_2 P t1 mm1 w va Hwf1 Hl Hal2) as (ilo & Hbytes1).
  destruct (u_fetch_read_ok P t t1 mm mm1 rsf rsf1 2 w va
              ltac:(lia) (Z.divide_factor_l 2 2048) ltac:(lia)
              ltac:(vm_compute; reflexivity) Hal2 Hl Lcp Hpins Hwf Hwf1 Tr1)
    as (region1 & HA1 & Hord1 & Hrange1 & HX1 & Hpmam1 & Halp1 & Hexecp1 &
        Hclint1 & Hsig1 & Hhtif1 & Hdev1 & Hown1 & Lcp1).
  assert (Hmr1 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                         (Physaddr (u_walk_pa w va)) 2 false false false)
                   (u_state rsf1 mm1) = Some (Ok ilo, u_state rsf1 mm1))
    by exact (exec_mem_read_fetch_2_U PBMT_PMA (u_walk_pa w va) region1 ilo
                (u_state rsf1 mm1) HA1 Hord1 Hrange1 HX1 Hpmam1 Halp1 Hexecp1
                Hclint1 Hsig1
                (within_htif_false (u_walk_pa w va) 2 (u_state rsf1 mm1) Hhtif1)
                Hdev1 Hbytes1 Lcp1).
  assert (Hmr1g : goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
                           (Physaddr (u_walk_pa w va)) 2 false false false)
                    (u_state rsf1 mm1) mm = true)
    by exact (goodmb_mem_read_fetch_2_U Du_r Du_w PBMT_PMA (u_walk_pa w va)
                region1 ilo (u_state rsf1 mm1) mm
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA1 Hord1 Hrange1 HX1 Hpmam1 Halp1 Hexecp1 Hclint1 Hsig1 Hhtif1
                Hdev1 Hown1 Hbytes1 Lcp1).
  destruct (isRVC ilo) eqn:Hrvc.
  - (* COMPRESSED: the bad page at [va+2] is never consulted *)
    exists rsf1, mm1, t1, (F_RVC ilo). split_and!.
    + exact (exec_fetch_rvc_2 (u_state rsf mm) (u_state rsf1 mm1) va
               (u_walk_pa w va) Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1 Hrvc).
    + exact (goodmb_fetch_rvc_2 Du_r Du_w (u_state rsf mm) (u_state rsf1 mm1) mm
               va (u_walk_pa w va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Htr1g Hmr1 Hmr1g Hrvc).
    + left. exists ilo. reflexivity.
    + exact Tr1.
    + exact Htlbok1.
    + exact Hstep1.
  - (* NOT COMPRESSED: the second translation faults, at [va+2] *)
    assert (Hpins1 : u_exec_pins P t1 rsf1)
      by exact (u_exec_pins_only P t t1 rsf rsf1 Tr1 Htlbok1 Hpins).
    assert (Lsxl1 : _get_Mstatus_SXL (register_lookup mstatus rsf1) = 'b"10")
      by (rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact Lsxl).
    assert (Lpc1 : register_lookup PC rsf1 = va)
      by (rewrite (Tr1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
    destruct (u_translate_fault_pure P t1 mm1 rsf1 (InstructionFetch tt)
                (E_Fetch_Page_Fault tt) (add_vec_int va 2) Hflavor
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                ltac:(unfold translationException; cbn match; apply exec_returnm)
                (exec_effectivePrivilege_fetch (register_lookup mstatus rsf1) User
                   (u_state rsf1 mm1))
                (exec_is_shadow_stack_fetch (u_state rsf1 mm1))
                Lcp1 Lsxl1 Hpins1 Hwf1)
      as (Htr2 & Htr2g).
    assert (Hdom1 : (dom mm : gset Arch.pa) = dom mm1)
      by (symmetry; exact (u_mem_step_dom P t t1 mm mm1 Hwf Hstep1)).
    assert (Htr2gm : goodmb Du_r Du_w (translateAddr (Virtaddr (add_vec_int va 2))
                              (InstructionFetch tt)) (u_state rsf1 mm1) mm = true).
    { rewrite (goodmb_dom Du_r Du_w
                 (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt))
                 (u_state rsf1 mm1) mm mm1 Hdom1).
      exact Htr2g. }
    exists rsf1, mm1, t1,
      (F_Error (E_Fetch_Page_Fault tt, add_vec_int va 2)). split_and!.
    + exact (exec_fetch_fault_2_second (u_state rsf mm) (u_state rsf1 mm1) va
               (u_walk_pa w va) Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Hmr1
               Lpc1 Hrvc (E_Fetch_Page_Fault tt) Htr2).
    + exact (goodmb_fetch_fault_2_second Du_r Du_w (u_state rsf mm)
               (u_state rsf1 mm1) mm va (u_walk_pa w va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Lpc HmisaC Hbit0 Hbit1 Hnal4 ilo Htr1 Htr1g Hmr1 Hmr1g
               Lpc1 Hrvc (E_Fetch_Page_Fault tt) Htr2 Htr2gm).
    + right. exists (E_Fetch_Page_Fault tt).
      split; [ reflexivity | vm_compute; reflexivity ].
    + exact Tr1.
    + exact Htlbok1.
    + exact Hstep1.
Qed.

(* THE LOW HALF'S PAGE IS BAD: nothing translates, nothing moves.  This is
   [u_fetch_fault_pure] with the 4-aligned shells replaced by the split
   ones and its alignment premise replaced by the three bit/align facts. *)
Lemma u_fetch_fault_pure_2_first (P : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rsf : regstate) (va : mword 64) (mi : bool) :
  UserFetchPt.u_fetch_fault_flavor (ud_tfp P) (ud_um P) va ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  post_fetch_cfg (u_state rsf mm) va mi ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exists (rsf' : regstate) (mm' : PtBytes.pamap) (t' : ptree) (fr : FetchResult),
    exec (fetch tt) (u_state rsf mm) = Some (fr, u_state rsf' mm') /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true /\
    (exists ex : ExceptionType, fr = F_Error (ex, va) /\ user_exc ex = true) /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hflavor Hbit0 Hbit1 Hnal4 Hcfg Hpins Hwf.
  pose proof Hcfg as (Lpc & Lcp & Lms & Lmenv & _ & _).
  pose proof Lms as (Lsxl & _).
  pose proof Hpins as (Hhw & _ & _ & Htlbok).
  pose proof Hhw as (Hmisa & _ & _ & _ & _ & _).
  assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsf)) ('b"1") = true)
    by (rewrite Hmisa; vm_compute; reflexivity).
  destruct (u_translate_fault_pure P t mm rsf (InstructionFetch tt)
              (E_Fetch_Page_Fault tt) va Hflavor
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              ltac:(unfold translationException; cbn match; apply exec_returnm)
              (exec_effectivePrivilege_fetch (register_lookup mstatus rsf) User
                 (u_state rsf mm))
              (exec_is_shadow_stack_fetch (u_state rsf mm)) Lcp Lsxl Hpins Hwf)
    as (Htr & Htrg).
  exists rsf, mm, t, (F_Error (E_Fetch_Page_Fault tt, va)). split_and!.
  - exact (exec_fetch_fault_2_first (u_state rsf mm) va Lpc HmisaC Hbit0 Hbit1
             Hnal4 (E_Fetch_Page_Fault tt) Htr).
  - exact (goodmb_fetch_fault_2_first Du_r Du_w (u_state rsf mm) mm va
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lpc HmisaC Hbit0 Hbit1 Hnal4 (E_Fetch_Page_Fault tt) Htr Htrg).
  - exists (E_Fetch_Page_Fault tt).
    split; [ reflexivity | vm_compute; reflexivity ].
  - exact (u_tlb_only_refl rsf).
  - exact Htlbok.
  - exact (u_mem_step_refl P t mm Hwf).
Qed.

