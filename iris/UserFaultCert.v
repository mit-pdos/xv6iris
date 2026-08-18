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
(* Layout: section 0 nine lemmas borrowed from [UserFetchCert] (see the    *)
(* note there); section 1 the access-type hygiene the certificates need,   *)
(* read off the caller's own [exec] premises; section 2 the DENIED leaf's  *)
(* permission check, certified; section 3 the fault-side [translateAddr]   *)
(* front matter (the [_err] and [_noncanon] twins of                       *)
(* [PtWalkCert.goodmb_translateAddr_pt_front]); section 4 the denied TLB   *)
(* HIT; section 5 the BLOCKED walk; section 6 the DENIED walk; section 7   *)
(* [u_translate_fault_pure]; section 8 [u_fetch_fault_pure].               *)
(*                                                                        *)
(* WHY THIS FILE DOES NOT [Require] [UserFetchCert]: at the time of        *)
(* writing [UserFetchCert.v] does not compile -- P4b's new                 *)
(* [UserBytes.u_walk_pa_window] (4 arguments) SHADOWS                      *)
(* [UserMem.u_walk_pa_window] (3 arguments) at [UserFetchCert.u_fetch_     *)
(* bytes], which imports [UserBytes] after [UserMem].  Section 0 restates  *)
(* the nine helpers this file needed under a [ufa_] prefix; DELETE THEM    *)
(* and Require [UserFetchCert] once that is fixed (or, better, at the      *)
(* fold-back the worklist already plans, when section 3 moves to           *)
(* [UserMem.v] and section 6 to [UserPtTree.v]).                           *)
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
Local Open Scope Z_scope.
Import Defs.


(* §0 BORROWED FROM [UserFetchCert] SECTIONS 3 AND 6.
   [UserFetchCert.v] does not compile against the current [UserBytes.v]
   (P4b's new [UserBytes.u_walk_pa_window] SHADOWS [UserMem.u_walk_pa_window]
   at [u_fetch_bytes]), so this file cannot Require it; these nine lemmas are
   its section-3 slot projections and its section-6 [translationMode] chain,
   restated under a [ufa_] prefix.  DELETE THEM at the fold-back, when
   section 3 moves to [UserMem.v] and section 6 to [UserPtTree.v]. *)

Lemma ufa_mword9_uint_range (x : mword 9) : (0 <= uint x < 512)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  change (bv_modulus (MachineWord.MachineWord.Z_idx 9)) with 512%Z in Hr.
  exact Hr.
Qed.

Lemma ufa_mword9_uint_id (x : mword 9) : (mword_of_int (uint x) : mword 9) = x.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N,
         SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ufa_pt_page_maps_slot (t : ptree) (i : mword 9) :
  word_bytes (u_pte_addr (pt_base t) i) (pt_ents t i) ∈ pt_page_maps t.
Proof.
  pose proof (pt_page_map_mem t (uint i) (ufa_mword9_uint_range i)) as Hm.
  rewrite ufa_mword9_uint_id in Hm. exact Hm.
Qed.

Lemma ufa_maps_slot2 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (u_pte_addr (pt_base t) (vpn_idx 2 vpn)) p2 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & _ & _ & He2 & _). rewrite <- He2.
  apply pt_maps_page. apply ufa_pt_page_maps_slot.
Qed.

Lemma ufa_maps_slot1 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (pt_addr1 p2 vpn) p1 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & Hk1 & Hk0 & He2 & He1 & He0 & Hb1 & Hb0 & _).
  unfold pt_addr1. rewrite Hb1. rewrite <- He1.
  apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
    [ apply ufa_mword9_uint_range
    | rewrite ufa_mword9_uint_id; exact Hk1
    | apply pt_maps_page; apply ufa_pt_page_maps_slot ].
Qed.

Lemma ufa_maps_slot0 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (pt_addr0 p1 vpn) p0 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & Hk1 & Hk0 & He2 & He1 & He0 & Hb1 & Hb0 & _).
  unfold pt_addr0. rewrite Hb0. rewrite <- He0.
  apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
    [ apply ufa_mword9_uint_range | rewrite ufa_mword9_uint_id; exact Hk1 |].
  apply (pt_maps_kid 0 c1 c0 (uint (vpn_idx 1 vpn)));
    [ apply ufa_mword9_uint_range | rewrite ufa_mword9_uint_id; exact Hk0 |].
  rewrite pt_maps_O. apply ufa_pt_page_maps_slot.
Qed.

Lemma ufa_slot_mem_at (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (b : mword 44) (i : mword 9) (q : mword 64) :
  u_mem_wf P t mm ->
  word_bytes (u_pte_addr b i) q ∈ pt_maps 2 t ->
  pt_slot_mem (u_state rs mm) (u_pte_addr b i) q.
Proof.
  intros Hwf Hin.
  pose proof (u_mem_wf_sub P t mm _ q Hwf Hin) as Hsub.
  assert (Hlk : forall j : nat, (N.of_nat j < 8)%N ->
            mm !! pa_add (u_pte_addr b i) j = Some (nth_byte q j)).
  { intros j Hj. apply (lookup_weaken (word_bytes (u_pte_addr b i) q) mm);
      [ apply word_bytes_lookup; lia | exact Hsub ]. }
  assert (Hram : forall j : nat, (N.of_nat j < 8)%N ->
            addr_is_ram (pa_add (u_pte_addr b i) j)).
  { intros j Hj. destruct Hwf as (md & _ & _ & _ & _ & Hr & _).
    apply Hr. apply elem_of_dom. exists (nth_byte q j). exact (Hlk j Hj). }
  split_and!.
  - exact Hlk.
  - rewrite <- (pa_add_0 (u_pte_addr b i)). apply Hram. lia.
  - apply Hram. lia.
  - exact (pte_addr_at_aligned8 b i).
Qed.

Lemma ufa_slot_owned (P : uptd) (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  u_mem_wf P t mm -> word_bytes a q ∈ pt_maps 2 t -> bytes_owned mm a 8 = true.
Proof. intros Hwf Hin. exact (u_mem_wf_owned P t mm a q Hwf Hin). Qed.

Lemma ufa_goodb_read_reg_D (Db : register -> bool) {E} (r : register) (s : mstate) :
  Db r = true -> goodb Db (Defs.read_reg r : Defs.monad E _) s = true.
Proof. intros HD. unfold Defs.read_reg. cbn [goodb]. by rewrite HD. Qed.

Lemma ufa_goodb_architecture_Supervisor (Db : register -> bool) (s : mstate) :
  Db mstatus = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  goodb Db (architecture Supervisor) s = true.
Proof.
  intros HD HSXL. unfold architecture. cbn match.
  match goal with |- goodb _ (Defs.bind ?L _) _ = true =>
    assert (Hin : exec L s
                  = Some (_get_Mstatus_SXL (register_lookup mstatus s.(sregs)), s));
    [ | assert (Hing : goodb Db L s = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). apply exec_returnM. }
  { rewrite (goodb_bind Db _ _ s _ (ufa_goodb_read_reg_D Db mstatus s HD)
               (exec_read_reg mstatus s)). reflexivity. }
  rewrite (goodb_bind Db _ _ s _ Hing Hin).
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. reflexivity.
Qed.

Lemma ufa_goodb_translationMode_U (Db : register -> bool) (satp0 : mword 64)
    (s : mstate) :
  Db mstatus = true -> Db satp = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  goodb Db (translationMode User) s = true.
Proof.
  intros HDms HDsatp HSXL Hsatp Hmode.
  unfold translationMode.
  change (generic_eq User Machine) with false. cbn match.
  rewrite (goodb_bind Db _ _ s RV64
             (ufa_goodb_architecture_Supervisor Db s HDms HSXL)
             (exec_architecture_Supervisor s HSXL)).
  assert (Hae : exec (Defs.assert_exp' (Z.geb xlen 64) "sys/vmem.sail:254.25-254.26") s
                = Some (eq_refl, s)).
  { replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
  assert (Haeg : goodb Db (Defs.assert_exp' (Z.geb xlen 64)
                             "sys/vmem.sail:254.25-254.26" : M _) s = true).
  { unfold Defs.assert_exp'.
    replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    cbn match. reflexivity. }
  match goal with |- goodb _ (Defs.bind ?L _) _ = true =>
    assert (Hmb : exec L s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s));
    [ | assert (Hmbg : goodb Db L s = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  { rewrite (goodb_bind Db _ _ s _ Haeg Hae).
    rewrite (goodb_bind Db _ _ s _ (ufa_goodb_read_reg_D Db satp s HDsatp)
               (exec_read_reg satp s)). reflexivity. }
  rewrite (goodb_bind Db _ _ s _ Hmbg Hmb).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. reflexivity.
Qed.

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
    apply pt_maps_page. apply ufa_pt_page_maps_slot.
  - right; left. exists (pt_ents t (vpn_idx 2 vpn)). split_and!;
      [ exact Hv2 | exact Hn2 | | ].
    + unfold pt_addr2. apply pt_maps_page. apply ufa_pt_page_maps_slot.
    + unfold pt_addr1. rewrite Hb1. rewrite <- He.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply ufa_mword9_uint_range
        | rewrite ufa_mword9_uint_id; exact Hk2
        | apply pt_maps_page; apply ufa_pt_page_maps_slot ].
  - right; right.
    exists (pt_ents t (vpn_idx 2 vpn)), (pt_ents c1 (vpn_idx 1 vpn)). split_and!;
      [ exact Hv2 | exact Hn2 | exact Hv1 | exact Hn1 | | | ].
    + unfold pt_addr2. apply pt_maps_page. apply ufa_pt_page_maps_slot.
    + unfold pt_addr1. rewrite Hb1.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply ufa_mword9_uint_range
        | rewrite ufa_mword9_uint_id; exact Hk2
        | apply pt_maps_page; apply ufa_pt_page_maps_slot ].
    + unfold pt_addr0. rewrite Hb0. rewrite <- He.
      apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
        [ apply ufa_mword9_uint_range | rewrite ufa_mword9_uint_id; exact Hk2 |].
      apply (pt_maps_kid 0 c1 c0 (uint (vpn_idx 1 vpn)));
        [ apply ufa_mword9_uint_range | rewrite ufa_mword9_uint_id; exact Hk1 |].
      rewrite pt_maps_O. apply ufa_pt_page_maps_slot.
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
  pose proof (ufa_slot_mem_at P t mm rs b i q Hwf Hin) as Hsm.
  destruct (Hpmar (u_pte_addr b i) (pt_slot_ram_access _ _ _ Hsm))
    as (region & Hm & Hs).
  split.
  - exact (pt_read_pte_slot (u_state rs mm) _ q region Hsm HA Hord HRp Hcovp Hm Hs Hhtif).
  - exact (goodmb_read_pte_slot Du_r Du_w
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             (u_state rs mm) mm _ q region Hsm
             (ufa_slot_owned P t mm _ q Hwf Hin)
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
  { rewrite <- Hbase. exact (ufa_maps_slot2 t vpn p2 p1 _ Hmaps). }
  destruct (u_slot_read P t mm rs (ud_root P) (vpn_idx 2 vpn) p2 Hwf Hpins H2)
    as (Hrd2 & Hrd2g).
  destruct (u_slot_read P t mm rs (u_next_base p2) (vpn_idx 1 vpn) p1 Hwf Hpins
              (ufa_maps_slot1 t vpn p2 p1 _ Hmaps)) as (Hrd1 & Hrd1g).
  destruct (u_slot_read P t mm rs (u_next_base p1) (vpn_idx 0 vpn) _ Hwf Hpins
              (ufa_maps_slot0 t vpn p2 p1 _ Hmaps)) as (Hrd0 & Hrd0g).
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
    by exact (ufa_goodb_translationMode_U Du_r usatp s
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
