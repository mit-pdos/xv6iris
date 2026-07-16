(* UmodeFetchFault.v -- the PAGE-FAULT arm of user-mode fetch.

   User pages carry ARBITRARY A/D bits: nothing in the user-execution
   theorem may assume they are preset.  Under the pinned post-boot
   menvcfg (MENVCFG_S: ADUE = 0, i.e. Svade behaviour), an instruction
   fetch whose leaf PTE needs an A-bit update does NOT write the PTE --
   [update_and_write_pte] returns [PTW_PTE_Needs_Update], which
   [translationException] turns into E_Fetch_Page_Fault, [fetch] into
   [F_Error], [run_hart_active] into [Step_Fetch_Failure], and the
   try_step dispatch into [handle_exception] -- i.e. a legitimate trap
   into stvec, the same kernel re-entry point as every other trap.  The
   same plumbing covers a leaf that fails the permission check (no X,
   no U): only the PTW error differs, and every non-No_Access error
   maps to the same page fault.

   §1 exec chain: update_and_write_pte / translate_TLB_hit / translate /
      translateAddr / fetch, ending in F_Error (E_Fetch_Page_Fault, pc).
   §2 run_hart_active on a fetch failure: Step_Fetch_Failure, state
      untouched.
   §3 [wp_user_fetch_pagefault]: the Iris capstone -- one whole machine
      step from User mode whose fetch page-faults, landing at stvec's
      direct base with scause = fetch-page-fault, sepc = stval = the
      faulting pc.                                                     *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import WpIntrCore.
Require Import UmodeTrap UmodeFetch UmodeStep.
Require Import CommonWalk.
Local Open Scope
Z_scope.
Import Defs.

(* the post-trap scause value, parametric in the cause *)
Definition utrap_scause (c : TrapCause) (sc_old : mword 64) : mword 64 :=
  update_subrange_vec_dec
    (update_subrange_vec_dec sc_old (64 - 1) (64 - 1) (bool_to_bit (trapCause_is_interrupt c)))
    (64 - 2) 0 (zero_extend' (64 - 1) (trapCause_bits_forwards c)).

(* the post-trap mstatus tower from USER mode (cause-independent) *)
Definition utrap_ms (ms_v : mword 64) (elp_v : mword 1) : mword 64 :=
  update_subrange_vec_dec
    (update_subrange_vec_dec
       (update_subrange_vec_dec
          (update_subrange_vec_dec ms_v 23 23 elp_v)
          5 5 (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp_v)))
       1 1 ('b"0"))
    8 8 (spp_bits User).

(* ===================================================================== *)
(* §1 The exec chain of the fetch page fault (TLB hit, A-bit clear).      *)
(* ===================================================================== *)


Section UTranslateHitFault.
  Context (ent : TLB_Entry) (vpn : mword 27).

  (* the permission check still passes (V/X/U leaf) ... *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s,
    exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
      = Some (PTE_Check_Success tt, s).
  (* ... but the A bit is clear: the fetch needs an update *)
  Context (pte' : mword 64).
  Hypothesis Hupd_some :
    update_PTE_Bits (tlb_get_pte 8 ent) (InstructionFetch tt) = Some pte'.
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.

  Lemma exec_translate_TLB_hit_u_needs_update (mxr do_sum : bool) s :
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (InstructionFetch tt) User mxr do_sum
            tt (tlb_hash (__id 39) vpn) ent) s
      = Some (Err (PTW_PTE_Needs_Update tt, tt), s).
  Proof.
    intros Hmenv.
    unfold translate_TLB_hit. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk mxr do_sum s)). cbn match.
    erewrite exec_bind_Some.
    2:{ eapply exec_update_and_write_pte_needs_update; [ exact Hupd_some | exact Hmenv ]. }
    cbn match.
    apply exec_returnm.
  Qed.

  Lemma exec_translate_u_needs_update (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (InstructionFetch tt) User mxr do_sum tt) s
      = Some (Err (PTW_PTE_Needs_Update tt, tt), s).
  Proof.
    intros Htlb Hvec Hmenv.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_lookup_TLB_hit_u ent vpn Hmatch tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_u_needs_update; exact Hmenv.
  Qed.

  Lemma exec_translateAddr_fetch_u_pagefault (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Err (E_Fetch_Page_Fault tt, tt), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hmenv Hcanon Hvpn_def.
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
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_u_needs_update _ _ _ tlbvec s Htlb Hvec Hmenv)).
    cbn match.
    assert (Hte : exec (translationException (InstructionFetch tt) (PTW_PTE_Needs_Update tt)) s
                  = Some (E_Fetch_Page_Fault tt, s)).
    { unfold translationException. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hte).
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

  (* the 4-aligned fetch turns the translate fault into F_Error at pc *)
  Lemma exec_fetch_u_pagefault_4 (va : mword 64) s :
    register_lookup PC s.(sregs) = va ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Err (E_Fetch_Page_Fault tt, tt), s) ->
    exec (fetch tt) s = Some (F_Error (E_Fetch_Page_Fault tt, va), s).
  Proof.
    intros HpcPC Hvalign Htr.
    destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    assert (Hfb4 : exec (fetch_bytes va va 4) s
                   = Some (@FetchBytes_Exception 4 (E_Fetch_Page_Fault tt), s)).
    { unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Err (E_Fetch_Page_Fault tt, tt)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
      cbv iota beta.
      unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* the ODD pc turns fetch into a deliverable fetch-address-misaligned fault
     BEFORE any translation: the first or_boolM disjunct [neq_vec PC[0] 'b"0"]
     short-circuits true, and the outer [if w__7] returns F_Error at pc. *)
  Lemma exec_fetch_u_addr_align (va : mword 64) (s : mstate) :
    register_lookup PC s.(sregs) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = true ->
    exec (fetch tt) s = Some (F_Error (E_Fetch_Addr_Align tt, va), s).
  Proof.
    intros HpcPC Hodd.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hodd. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End UTranslateHitFault.

(* ===================================================================== *)
(* §1b The NOPERM twin: a MAPPED but NON-EXECUTABLE leaf (fetch denied).   *)
(*     The permission check FAILS with No_Permission, short-circuiting     *)
(*     translate_TLB_hit to PTW_No_Permission BEFORE update_and_write_pte. *)
(* ===================================================================== *)

Section UTranslateHitNoperm.
  Context (acc : MemoryAccessType mem_payload) (ent : TLB_Entry) (vpn : mword 27).

  (* the leaf DENIES the access (no X/R/W or no U) *)
  Hypothesis Hchk_denied : forall (mxr do_sum : bool) s,
    exec (check_PTE_permission acc User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
      = Some (PTE_Check_Failure (tt, PTE_No_Permission tt), s).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.

  Lemma exec_translate_TLB_hit_u_noperm (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn acc User mxr do_sum
            tt (tlb_hash (__id 39) vpn) ent) s
      = Some (Err (PTW_No_Permission tt, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk_denied mxr do_sum s)). cbn match.
    apply exec_returnm.
  Qed.

  Lemma exec_translate_u_noperm (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn acc User mxr do_sum tt) s
      = Some (Err (PTW_No_Permission tt, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_lookup_TLB_hit_u ent vpn Hmatch tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_u_noperm.
  Qed.

End UTranslateHitNoperm.

(* miss-path NOPERM: the TLB lookup misses, the 3-level walk reaches the
   leaf, and the leaf DENIES the access -> [translate] errors with
   No_Permission.  Access-generic; the leaf permission failure short-
   circuits BEFORE the Svnapot gate (no misa premise, no leaf N-bit). *)
Lemma exec_translate_walk_user_noperm
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (acc : MemoryAccessType mem_payload) (mxr do_sum : bool)
    (H2i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                             (ext_bits_of_PTE pte2)) s = Some (false, s))
    (H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true)
    (H1i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                             (ext_bits_of_PTE pte1)) s = Some (false, s))
    (H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true)
    (H0i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                             (ext_bits_of_PTE pte0)) s = Some (false, s))
    (H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false)
    (Hchk0 : forall s, exec (check_PTE_permission acc User mxr do_sum
                               (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                               (ext_bits_of_PTE pte0) tt) s
       = Some (PTE_Check_Failure (tt, PTE_No_Permission tt), s))
    (asid : mword 16) s :
  exec (lookup_TLB 39 asid vpn) s = Some (None, s) ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  exec (translate 39 asid root vpn acc User mxr do_sum tt) s
    = Some (Err (PTW_No_Permission tt, tt), s).
Proof.
  intros Hlk Hrd2 Hrd1 Hrd0.
  apply (exec_translate_walk_user_err vpn acc User mxr do_sum
           asid root (PTW_No_Permission tt) s Hlk).
  apply (exec_translate_TLB_miss_user_walk_err vpn acc User mxr do_sum
           asid root (PTW_No_Permission tt) s).
  apply (exec_pt_walk_user_sub vpn acc User mxr do_sum root pte2 _ s Hrd2 H2i H2nl).
  intros g' a.
  apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum
           (u_next_base pte2) pte1 g' _ a s Hrd1 H1i H1nl).
  intros g'' a0.
  exact (exec_rec_walk_leaf_noperm vpn acc User mxr do_sum
           (u_next_base pte1) pte0 g'' (PTE_No_Permission tt) a0 s Hrd0 H0i H0nl Hchk0).
Qed.

(* ===================================================================== *)
(* §2 run_hart_active on a fetch failure: Step_Fetch_Failure, no state    *)
(*    change (the TLB-hit fault path performs no write).                  *)
(* ===================================================================== *)

Lemma exec_run_hart_active_fetch_fault (s : mstate) (p : Privilege)
    (e : ExceptionType) (va : mword 64) :
  register_lookup cur_privilege s.(sregs) = p ->
  exec (dispatchInterrupt p) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Error (e, va), s) ->
  exec (run_hart_active 0) s = Some (Step_Fetch_Failure (Virtaddr va, e), s).
Proof.
  intros Hpriv Hdisp Hfetch.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match.
  unfold ext_fetch_hook. cbn match.
  rewrite execR_returnR. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The Iris capstone: one machine step from User whose fetch           *)
(*    page-faults (A-bit clear under ADUE = 0), trapping to stvec.        *)
(* ===================================================================== *)

Section WpUserFetchFault.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation pf_cause := (rv64d_types.Exception (E_Fetch_Page_Fault tt)).

  Lemma wp_user_fetch_pagefault
      (ent : TLB_Entry) (vpn : mword 27) (va satp0 : mword 64) (pte' : mword 64)
      (ms_v sc_old stval_old sepc_old stvec_v : mword 64)
      (mie_v midl_v mip_v medl_v menvcfg0 : mword 64) (meip seip : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) {dq dqc : dfrac} :
    ↑minstretN ⊆ E ->
    (* no interrupt can be pending *)
    and_vec mie_v (not_vec midl_v) = zeros' 64 ->
    and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v midl_v) = zeros' 64 ->
    (* mstatus / satp: Sv39, asid 0 *)
    _get_Mstatus_SXL ms_v = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    (* the user TLB entry: present, matching, permission check passes, but
       the A bit is CLEAR -- the access needs an update the config forbids *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    (forall (mxr do_sum : bool) s,
       exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
         = Some (PTE_Check_Success tt, s)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (InstructionFetch tt) = Some pte' ->
    match_TLB_Entry ent (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = true ->
    (* va geometry *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (* stvec: direct mode; fetch-page-fault delegated *)
    trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct ->
    bit_to_bool (access_vec_dec medl_v
                   (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_old -∗
    stval ↦ᵣ stval_old -∗
    sepc ↦ᵣ sepc_old -∗
    stvec ↦ᵣ{ dqc } stvec_v -∗
    mie ↦ᵣ{ dqc } mie_v -∗
    mideleg ↦ᵣ{ dqc } midl_v -∗
    medeleg ↦ᵣ{ dqc } medl_v -∗
    mip ↦ᵣ{ dqc } mip_v -∗
    sig_meip ↦ᵣ{ dqc } meip -∗
    sig_seip ↦ᵣ{ dqc } seip -∗
    satp ↦ᵣ{ dqc } satp0 -∗
    tlb ↦ᵣ{ dqc } tlbvec -∗
    menvcfg ↦ᵣ{ dqc } menvcfg0 -∗
    pc_is va -∗
    ( cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
      scause ↦ᵣ utrap_scause pf_cause sc_old -∗
      stval ↦ᵣ va -∗
      sepc ↦ᵣ va -∗
      stvec ↦ᵣ{ dqc } stvec_v -∗
      mie ↦ᵣ{ dqc } mie_v -∗
      mideleg ↦ᵣ{ dqc } midl_v -∗
      medeleg ↦ᵣ{ dqc } medl_v -∗
      mip ↦ᵣ{ dqc } mip_v -∗
      sig_meip ↦ᵣ{ dqc } meip -∗
      sig_seip ↦ᵣ{ dqc } seip -∗
      satp ↦ᵣ{ dqc } satp0 -∗
      tlb ↦ᵣ{ dqc } tlbvec -∗
      menvcfg ↦ᵣ{ dqc } menvcfg0 -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      pc_is (stvec_base stvec_v) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmm Hs0 HSXL Hsatpmode Hasid Hvec Hchk Hupd_some Hmatch
           Hval Hcanon Hvpn_def Htvd Hdel12 Hmenvval.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hscause Hstval Hsepc Hstvec Hmie Hmidl
             Hmedl Hmip Hmeip Hseip Hsatp Htlb Hmenv Hpc Hcont".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- pure facts ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; exact Hmenvval).
    pose proof (exec_translateAddr_fetch_u_pagefault ent vpn Hchk pte' Hupd_some Hmatch
                  va satp0 tlbvec σ Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Lmenv'
                  Hcanon Hvpn_def) as Htr.
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ (state unchanged by the fault) *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel12).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_old stvec_v elp0
                  (or_introl eq_refl) Lpriv Lms Lsc Lstvec Lelp LmisaS Htvd Lpc
                  (bits_of_virtaddr (Virtaddr va)) (E_Fetch_Page_Fault tt)
                  eq_refl eq_refl Lmedl') as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch (Step_Fetch_Failure (Virtaddr va, E_Fetch_Page_Fault tt))) σ
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    (* ---- ghost updates in tower order ---- *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) σ.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite Lelp. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hscause") as "[Hreg Hscause]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_old)
            with "Hreg Hscause") as "[Hreg Hscause]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va))))
            with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Fetch_Failure (Virtaddr va, E_Fetch_Page_Fault tt)), σ, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem".
    { unfold s_trap, set_reg; cbn [sregs mem].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    assert (Hstv : tval (xtval_exception_value (E_Fetch_Page_Fault tt)
                           (bits_of_virtaddr (Virtaddr va))) = va)
      by reflexivity.
    iEval (rewrite Hstv) in "Hstval".
    iApply ("Hcont" with "Hpriv Hms Hscause Hstval Hsepc Hstvec Hmie Hmidl Hmedl
                          Hmip Hmeip Hseip Hsatp Htlb Hmenv Hhs [$Hpcr $Hnpc]").
  Qed.

End WpUserFetchFault.
