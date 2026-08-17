(* CommonWalk.v -- the GENERIC (privilege- and access-type-parametric)
   3-level Sv39 page walk over an ABSTRACT page table.

   These lemmas were factored out of UmodeWalk.v so that BOTH the
   user-mode fetch/load/store proofs AND the S-mode device (UART/PLIC)
   load/store proofs can reuse the identical walk core: every lemma here
   is generic over the access type [acc : MemoryAccessType] and the
   [Privilege] [p]; only the leaf permission-check hypothesis mentions
   them.  UmodeWalk.v `Require Export`s this file, so existing user-mode
   callers see these names unchanged.

   Contents: the slot-address / next-base / global-bit helpers, the
   Svnapot/Svadu extension probes and the A/D-update page-fault leaf,
   [Section UserWalk] (the success walk: three PTE reads -> level-0 leaf,
   TLB fill), and [Section UserWalkFault] (invalid / no-permission
   faults, no state change).  The walk itself performs NO A/D update --
   that happens in translate_TLB_miss on the walk's output PTE. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge.
(* the [swp] layer's vocabulary: the walk's memory reads become obligations
   at this level (main-cycle-port), so the lemmas below are stated over
   frames rather than over a whole state. *)
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import RiscvPtsto HartSwp HartLift HartRegNode HartSpan HartSpanChar
        HartGoodb.
Local Open Scope Z_scope.
Import Defs.

(* the PTE slot address at one walk level: base ppn ++ 9-bit index ++ 000 *)
Definition u_pte_addr (base : mword 44) (idx : mword 9) : mword 64 :=
  zero_extend' 64 (concat_vec base (concat_vec idx (zeros' 3))).

(* NB the address premise a walk's PMA lookups need is NOT a no-wraparound
   bound (that was enough only for the one-region idealization of the platform
   table): it is the RAM CLASS, and its one supplier is
   [PtTree.pt_slot_ram_access], out of the [pt_slot_mem] fact the walk already
   holds of every slot it reads.  [Pt4kWalk.pte_addr_at_no_wrap] is still the
   slot-geometry bound if a caller ever needs it; [u_pte_addr] IS
   [Pt4kWalk.pte_addr_at]. *)

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

(* the leaf check's read set: the Svnapot probe reads misa, the PBMTE gate
   reads menvcfg, and nothing else in the region touches a register. *)
Definition D_leafchk (r : register) : bool :=
  orb (register_beq r (R_bitvector_64 misa))
      (register_beq r (R_bitvector_64 menvcfg)).

Lemma D_misa_leafchk (r : register) : D_misa r = true -> D_leafchk r = true.
Proof. unfold D_misa, D_leafchk. intros ->. reflexivity. Qed.

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


(* its footprint certificate, by the same reference-state transport: the
   probe's read set IS [D_misa], and [MISA_C] is the reference value, so the
   certificate computes there and [goodb_congr] carries it to any state that
   pins misa the same way. *)
Lemma goodb_currentlyEnabled_Svnapot s :
  register_lookup misa s.(sregs) = MISA_C ->
  goodb D_misa (currentlyEnabled Ext_Svnapot) s = true.
Proof.
  intro Hmisa.
  apply (goodb_congr D_misa (currentlyEnabled Ext_Svnapot) dstateM s).
  - intros r Hr. unfold D_misa in Hr. apply register_beq_eq in Hr. subst r.
    rewrite Hmisa. vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* The A/D-update extension probe.                                        *)
(* ===================================================================== *)
Lemma exec_currentlyEnabled_Svadu s :
  exec (currentlyEnabled Ext_Svadu) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  vm_compute. reflexivity.
Qed.

(* Sv39 TLB tags are 45-bit sign-extensions of the 27-bit vpn; since the
   top 12 bits of a 27-bit word never overflow the sign extension, the tag
   determines the vpn.  Used to discriminate device (UART/PLIC) TLB entries
   from RAM svpn tags. *)
Lemma u_sext45_inj (x y : mword 27) :
  sign_extend' (57 - 12) x = sign_extend' (57 - 12) y -> x = y.
Proof.
  intros H.
  apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H; [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

(* The walk body's shared head: the recursion-limit assert, the xlen assert, and
   the PTE read.  Peeling it with [exec_assert_exp'_true] keeps the two assertion
   MESSAGES -- which are "<file>:<line>" positions in the Sail source -- out of
   the proofs entirely; six copies of this head used to spell them out, and every
   one of them broke on the model bump for no reason of its own. *)
Local Ltac walk_peel_asserts lvl st :=
  cbn [_rec_pt_walk];
  change (lvl >=? 0) with true;
  rewrite (exec_bind_Some _ _ _ _ _ (exec_assert_exp'_true _ st)); cbn beta zeta;
  change ((39 =? 32) || (xlen =? 64)) with true;
  rewrite (exec_bind_Some _ _ _ _ _ (exec_assert_exp'_true _ st)); cbn beta zeta.

(* ...and the PTE read that follows, once the caller has named the slot address
   (the address only becomes visible after the asserts are peeled). *)
Local Ltac walk_peel_read st Hrd :=
  rewrite (exec_bind_Some _ _ _ _ _ Hrd); cbn match beta zeta.

Section UserWalk.
  (* the [swp] layer's parameters, used only by the [swp_] lemmas below *)
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
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

  (* the EVENT-FREENESS companions of the two monadic hypotheses above.  Both
     are pure tests on the leaf word, so an instance discharges them at its
     concrete flag byte exactly where it discharges the exec versions. *)
  Hypothesis H0ig : forall (Db : register -> bool) s,
    goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                (ext_bits_of_PTE pte0)) s = true.
  Hypothesis Hchk0g : forall (Db : register -> bool) s,
    goodb Db (check_PTE_permission acc p mxr do_sum
                (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                (ext_bits_of_PTE pte0) tt) s = true.

  (* ------------------------------------------------------------------ *)
  (* [check_leaf_pte]: Steps 3 and 5-8 of the VATP, which the fork factored *)
  (* OUT of [pt_walk] so that the atomic A/D update can re-run them on the  *)
  (* freshly read PTE ([update_and_write_pte]).  Factor it out on the proof  *)
  (* side too, for the same reason: this one lemma serves the walk's leaf    *)
  (* arm AND the A/D update's re-check, and nothing else in either proof     *)
  (* has to know what the leaf checks are.                                   *)
  (*                                                                        *)
  (* Level 0, so the misaligned-superpage test and the superpage PPN         *)
  (* composition are both dead ([level > 0] is false); the Svnapot gate is    *)
  (* what [H0N] kills.                                                       *)
  (* ------------------------------------------------------------------ *)
  Lemma exec_check_leaf_pte_leaf0 (pa : physaddr) (menvcfg0 : mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (check_leaf_pte 39 vpn acc p mxr do_sum pte0 pa 0 tt) s
      = Some (Ok (autocast (T := mword) (PPN_of_PTE pte0), PBMT_PMA, tt), s).
  Proof.
    intros Hmisa Hmenv HPBMTE.
    unfold check_leaf_pte. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (H0i s)). cbv iota beta.
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


  (* ------------------------------------------------------------------ *)
  (* ...and its FOOTPRINT CERTIFICATE, mirroring the proof above step for   *)
  (* step with the same sub-facts, so no page-table reasoning is restated.  *)
  (* This is the shape that made the walk bridgeable at all: the region is  *)
  (* a [catch_early_return] block, so it goes through [goodb_cer] and then  *)
  (* [goodb_bindR] -- the EARLY-RETURN interpreter's bind.                  *)
  (*                                                                       *)
  (* TWO HABITS MAKE IT GO THROUGH, and neither is optional.  [execR]'s     *)
  (* bind equations peel a goal structurally; [goodb]'s must be GIVEN their *)
  (* left operand, and a hand-written copy of that operand does not match   *)
  (* (the [and_boolM] carries type arguments that do not survive retyping). *)
  (* So: [set] the operand straight OUT of the goal, and make its VALUE     *)
  (* EXISTENTIAL -- the certificate never needs to know the ppn, only that  *)
  (* the step returned rather than early-returned.                          *)
  (* ------------------------------------------------------------------ *)
  Lemma goodb_check_leaf_pte_leaf0 (pa : physaddr) (menvcfg0 : mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodb D_leafchk (check_leaf_pte 39 vpn acc p mxr do_sum pte0 pa 0 tt) s
    = true.
  Proof.
    intros Hmisa Hmenv HPBMTE.
    unfold check_leaf_pte. apply goodb_cer.
    rewrite (goodb_bindR D_leafchk _ _ s false
               (goodb_liftR D_leafchk _ s (H0ig D_leafchk s))
               ltac:(rewrite execR_liftR; rewrite (H0i s); reflexivity)).
    cbv iota beta.
    rewrite H0nl. cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s
                    = Some (inr (PTE_Check_Success tt), s));
      [| assert (HABg : goodb D_leafchk (Defs.bind0 A B) s = true) ] end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite (Hchk0 s). cbn match. reflexivity. }
    { match goal with |- goodb _ (Defs.bind0 ?A ?B) _ = true =>
        rewrite (goodb_bind0R D_leafchk A B s ltac:(reflexivity)
                   ltac:(apply execR_returnR)) end.
      apply (goodb_liftR D_leafchk _ s (Hchk0g D_leafchk s)). }
    rewrite (goodb_bindR D_leafchk _ _ s (PTE_Check_Success tt) HABg HAB).
    cbv iota beta. cbn match.
    change (0 >? 0) with false. cbv iota beta.
    (* The Svnapot gate sits under TWO binds, as in the exec proof.  Neither
       operand is written out here: [set] takes the outer one straight from
       the goal (so the rewrite matches syntactically), and its VALUE is
       existential -- the certificate never needs to know the ppn, only that
       the step returned. *)
    match goal with |- goodb _ (Defs.bind ?A _) _ = true => set (Aout := A) end.
    assert (Houtg : goodb D_leafchk Aout s = true).
    { subst Aout.
      match goal with |- goodb _ (Defs.bind ?A ?B) _ = true =>
        rewrite (goodb_bindR D_leafchk A B s false
                   ltac:(unfold Defs.and_boolM;
                         match goal with |- goodb _ (Defs.bind ?C ?D) _ = true =>
                           rewrite (goodb_bindR D_leafchk C D s true
                             ltac:(apply (goodb_liftR D_leafchk _ s);
                                   apply (goodb_mono D_misa D_leafchk _ s
                                            D_misa_leafchk);
                                   exact (goodb_currentlyEnabled_Svnapot s Hmisa))
                             ltac:(rewrite execR_liftR;
                                   rewrite (exec_currentlyEnabled_Svnapot s Hmisa);
                                   reflexivity)) end;
                         reflexivity)
                   ltac:(unfold Defs.and_boolM; rewrite execR_bind;
                         rewrite execR_liftR;
                         rewrite (exec_currentlyEnabled_Svnapot s Hmisa);
                         cbn match; rewrite execR_returnR; rewrite H0N;
                         reflexivity)) end.
      reflexivity. }
    assert (Hout : exists v, execR Aout s = Some (inr v, s)).
    { subst Aout. eexists. rewrite execR_bind.
      unfold Defs.and_boolM. rewrite execR_bind. rewrite execR_liftR.
      rewrite (exec_currentlyEnabled_Svnapot s Hmisa). cbn match.
      rewrite execR_returnR. rewrite H0N. cbn match.
      rewrite execR_returnR. reflexivity. }
    destruct Hout as (vout & Hout).
    match goal with |- goodb _ (Defs.bind _ ?B) _ = true =>
      rewrite (goodb_bindR D_leafchk Aout B s vout Houtg Hout) end.
    cbv iota beta.
    (* the PBMTE gate's menvcfg read: the region's last node *)
    match goal with |- goodb _ (Defs.bind ?A ?B) _ = true => set (Amenv := A) end.
    rewrite (goodb_bindR D_leafchk Amenv _ s
               (register_lookup menvcfg s.(sregs))
               ltac:(subst Amenv; apply (goodb_liftR D_leafchk _ s);
                     reflexivity)
               ltac:(subst Amenv; rewrite execR_liftR;
                     rewrite (exec_read_reg menvcfg s); reflexivity)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    reflexivity.
  Qed.


  (* the pair, as the fuel-free characterization [swp_span] consumes.  A
     caller that takes [dst] to be a state carrying its OWN register file
     discharges the agreement by [reflexivity]. *)
  Lemma hval_check_leaf_pte_leaf0 (D Drw : gset register) (rs : regstate)
      (dst : mstate) (pa : physaddr) (menvcfg0 : mword 64) :
    (forall r : register, D_leafchk r = true -> r ∈ D) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hval D Drw rs (check_leaf_pte 39 vpn acc p mxr do_sum pte0 pa 0 tt)
      (Ok (autocast (T := mword) (PPN_of_PTE pte0), PBMT_PMA, tt)) rs.
  Proof.
    intros HD Hag Hmisa Hmenv HPBMTE.
    eapply (hval_of_goodb D_leafchk D Drw _ dst rs _ HD Hag).
    - exact (goodb_check_leaf_pte_leaf0 pa menvcfg0 dst Hmisa Hmenv HPBMTE).
    - exact (exec_check_leaf_pte_leaf0 pa menvcfg0 dst Hmisa Hmenv HPBMTE).
  Qed.

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
    (* the walk body is no longer an early-return block: the leaf arm's escapes
       moved into [check_leaf_pte], so this level peels in the plain monad. *)
    assert (Hae1 : exec (Defs.assert_exp' (0 >=? 0) "recursion limit reached") s
                   = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae1). cbn beta zeta.
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64))
                          "sys/vmem.sail:277.36-277.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae2). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd0). cbn match beta zeta.
    (* the follow-a-pointer test: valid AND non-leaf AND level > 0.  A leaf
       fails the second conjunct, so the [check_leaf_pte] arm is taken. *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (false, s)) end.
    { unfold Defs.and_boolM.
      (* the left conjunct is itself a bind ([pte_is_invalid] then [not]), so it
         has to be valued before the outer bind can be peeled *)
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H0i s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      change (0 >? 0) with false. rewrite andb_false_r. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hnl). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_check_leaf_pte_leaf0 (Physaddr addr0) menvcfg0 s Hmisa Hmenv HPBMTE)).
    cbn match beta zeta.
    apply exec_returnM.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE SAME LEVEL AT THE SWP LAYER.  One thing changes shape and only    *)
  (* one: the PTE read is a MEMORY EVENT, so it cannot be a pure premise   *)
  (* the way [Hrd0] is above -- under per-node stepping another hart may    *)
  (* step between this walk's nodes, so what the read returns has to be     *)
  (* justified where it happens.  It becomes the caller's OBLIGATION.       *)
  (*                                                                      *)
  (* Everything else is carried, not re-proved: the two asserts reduce, the *)
  (* follow-a-pointer test and the leaf check come across as [hval] through *)
  (* the [goodb] bridge, with the same sub-facts the exec proof uses.       *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_rec_walk_leaf (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (g : bool) (menvcfg0 : mword 64)
      (wfacc : Acc (Zwf 0) 0) :
    Drw ## Dro ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr addr0) 8)
         (fun r => ⌜r = Values.Ok pte0⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte1) 0 g tt 0 wfacc)
      (fun r => ⌜r = Values.Ok
                       ({| PTW_Output_ppn := autocast (T := mword)
                             ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44);
                           PTW_Output_pte := autocast (T := mword) pte0;
                           PTW_Output_pteAddr := Physaddr addr0;
                           PTW_Output_level := 0;
                           PTW_Output_pbmt := PBMT_PMA;
                           PTW_Output_global := orb g (u_gbit pte0) |}, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD Hag Hmisa Hmenv HPBMTE.
    iIntros "#Hcert Hrw Hro Hrd".
    destruct wfacc as [a0].
    cbn [_rec_pt_walk].
    (* the two asserts are literal [true]s here, so they reduce rather than
       needing a rule *)
    change (0 >=? 0) with true.
    unfold Defs.assert_exp'. cbn match. rewrite mbind_ret. cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    cbn match. rewrite mbind_ret. cbn beta zeta.
    (* THE MEMORY EVENT *)
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    iApply (swp_bind_use (read_pte (Physaddr addr0) 8) _ _ _
              with "[Hrw Hro Hrd] [-]").
    { iApply ("Hrd" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match beta zeta.
    (* the follow-a-pointer test: carried, not re-proved.  This level peels
       in the PLAIN monad (the leaf arm's escapes live in [check_leaf_pte]),
       so it is [goodb_bind] and [exec], not their early-return twins. *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      set (Anl := Defs.and_boolM A B) end.
    assert (Hinner : exec (Defs.bind (pte_is_invalid
                             (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                             (ext_bits_of_PTE pte0))
                             (fun w => Defs.returnm (negb w))) dst
                     = Some (true, dst)).
    { rewrite (exec_bind_Some _ _ _ _ _ (H0i dst)). cbn match beta.
      apply exec_returnm. }
    assert (Hinnerg : goodb D_leafchk (Defs.bind (pte_is_invalid
                             (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                             (ext_bits_of_PTE pte0))
                             (fun w => Defs.returnm (negb w))) dst = true).
    { rewrite (goodb_bind D_leafchk _ _ dst false (H0ig D_leafchk dst)
                 (H0i dst)). reflexivity. }
    assert (Hnl : exec Anl dst = Some (false, dst)).
    { subst Anl. unfold Defs.and_boolM.
      rewrite (exec_bind_Some _ _ _ _ _ Hinner). cbn match beta.
      change (0 >? 0) with false. rewrite andb_false_r. apply exec_returnm. }
    assert (Hnlg : goodb D_leafchk Anl dst = true).
    { subst Anl. unfold Defs.and_boolM.
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind D_leafchk _ E dst true Hinnerg Hinner) end.
      reflexivity. }
    iApply (swp_bind_use Anl _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs Anl false Hdisj
                (hval_of_goodb D_leafchk (Drw ∪ Dro) Drw Anl dst rs false
                   HD Hag Hnlg Hnl)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match beta.
    (* the leaf check, likewise *)
    iApply (swp_bind_use (check_leaf_pte 39 vpn acc p mxr do_sum pte0
                            (Physaddr addr0) 0 tt) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_check_leaf_pte_leaf0 (Drw ∪ Dro) Drw rs dst
                   (Physaddr addr0) menvcfg0 HD Hag Hmisa Hmenv HPBMTE)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match beta zeta.
    iApply swp_ret. by iFrame.
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
    assert (Hae1 : exec (Defs.assert_exp' (1 >=? 0) "recursion limit reached") s
                   = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae1). cbn beta zeta.
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64))
                          "sys/vmem.sail:277.36-277.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae2). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr1 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd1). cbn match beta zeta.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H1i s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      rewrite H1nl. change (1 >? 0) with true. cbn [andb]. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hnl). cbn match beta.
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
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s
                   = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae1). cbn beta zeta.
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64))
                          "sys/vmem.sail:277.36-277.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (exec_bind_Some _ _ _ _ _ Hae2). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr2 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd2). cbn match beta zeta.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H2i s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      rewrite H2nl. change (2 >? 0) with true. cbn [andb]. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hnl). cbn match beta.
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
    (* [update_and_write_pte] takes the whole tablewalk context now (it re-runs
       the leaf checks on a freshly read PTE when it DOES write), and returns the
       ext_ptw alongside.  The no-write case is still one step. *)
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec (update_and_write_pte w vp a pv lv ac pr mx ds e) s
                     = Some (Ok (None, tt), s)) end.
    { unfold update_and_write_pte. rewrite Hnoupd. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_user asid s)).
    apply exec_returnm.
  Qed.


  (* miss via hash collision: the slot holds a NON-matching entry *)

  (* miss via hash collision: same as [exec_translate_walk_user], but the
     slot holds a NON-matching entry instead of being empty *)

  (* the translated physical address a level-0 walk yields for [va] *)
  Definition u_walk_pa (va : mword 64) : mword 64 :=
    zero_extend' 64 (concat_vec
      ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44)) : mword 44)
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)).

End UserWalk.

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

  (* [check_leaf_pte]'s two failure outcomes, at any level: an INVALID pte, and
     a valid leaf that fails the permission check. *)
  Lemma exec_check_leaf_pte_invalid (pte : mword 64) (pa : physaddr) (lvl : Z) s :
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    exec (check_leaf_pte 39 vpn acc p mxr do_sum pte pa lvl tt) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s).
  Proof.
    intro Hinv.
    unfold check_leaf_pte. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)). cbv iota beta.
    cbn. reflexivity.
  Qed.

  Lemma exec_check_leaf_pte_noperm0 (pte : mword 64) (pa : physaddr)
        (f : pte_check_failure) s :
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    (forall s0, exec (check_PTE_permission acc p mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte) tt) s0
       = Some (PTE_Check_Failure (tt, f), s0)) ->
    exec (check_leaf_pte 39 vpn acc p mxr do_sum pte pa 0 tt) s
      = Some (Err (ext_get_ptw_error f, tt), s).
  Proof.
    intros Hinv Hnl Hchk.
    unfold check_leaf_pte. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv s)). cbv iota beta.
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
    walk_peel_asserts 0 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (false, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hnl). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_check_leaf_pte_invalid pte
                  (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 0 s Hinv)).
    cbn match beta zeta. apply exec_returnM.
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
    walk_peel_asserts 0 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. cbn [andb]. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_check_leaf_pte_noperm0 pte
                  (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) f s Hinv Hnl Hchk)).
    cbn match beta zeta. apply exec_returnM.
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
    walk_peel_asserts 1 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_check_leaf_pte_invalid pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 1 s Hinv)).
    cbn match beta zeta. apply exec_returnM.
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
    walk_peel_asserts 1 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. change (1 >? 0) with true. cbn [andb]. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    rewrite Hsub. reflexivity.
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
    walk_peel_asserts 2 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_check_leaf_pte_invalid pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 2 s Hinv)).
    cbn match beta zeta. apply exec_returnM.
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
    walk_peel_asserts 2 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_peel_read s Hrd.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. change (2 >? 0) with true. cbn [andb]. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hab). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    rewrite Hsub. reflexivity.
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
