(* WpUserFetch.v -- the fetch-fault USTEP arms (non-canonical / unmapped / A-D fault).
   Split from the monolithic WpUserExec.v; all lemmas close over the
   single parameter bundle [uctx] (see WpUserBase).                      *)
(* WpUserExec.v -- the user-execution theorem: the loop frames and the
   Löb skeleton.

   [user_frame] is the loop invariant P of [wp_user_loop]: an ARBITRARY
   user machine -- existential GPRs, pc, trap CSRs, TLB (consistent with
   the page-table spec) -- over the loop-constant configuration (the
   [user_cfg] cells, the page-table ownership [upt_inv], the persistent
   user code bytes, and the writable user data bytes).

   [user_trap_frame] is Tr: the same machine handed to the kernel
   re-entry continuation -- Supervisor privilege, pc at stvec's direct
   base, trap CSRs written (existential here; refined per-cause by the
   USTEP cases that produce it).

   [wp_user_exec] is the Löb capstone: one USTEP obligation -- a single
   machine step from [user_frame] re-establishes [user_frame] (retire)
   or produces [user_trap_frame] (trap), with both continuations under a
   later -- runs arbitrary user code forever.  The USTEP obligation is
   discharged case by case in the companion files (fetch trichotomy x
   decode totality x execute families); the proven instances so far are
   the wp_user_ecall / wp_user_fetch_pagefault vertical slices.        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpIntrCore.
Require Import UmodeTrap UmodeFetch UmodeStep UmodeFetchFault UmodeWalk.
Require Import UptInv.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

(* ================================================================== *)
(* A-update (ADUE=0) FETCH page fault, walk plumbing (fetch-uncond.).  *)
(* A mapped leaf whose A/D bits need an update the config forbids      *)
(* makes [translate] return [PTW_PTE_Needs_Update]; [translateAddr]    *)
(* turns that into [E_Fetch_Page_Fault].  These pure exec facts are    *)
(* the miss-path twins of [exec_translate_walk_user] /                 *)
(* [exec_translateAddr_fetch_walk_u], and a translate-abstract         *)
(* [translateAddr] wrapper shared by the TLB-hit and walk paths.       *)
(* ================================================================== *)

(* miss-path: TLB lookup misses, the 3-level walk reaches the leaf, but
   the leaf needs an A/D update -> [translate] errors with Needs_Update *)
Lemma exec_translate_walk_user_needs_update
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64) (mxr do_sum : bool)
    (H2i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                             (ext_bits_of_PTE pte2)) s = Some (false, s))
    (H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true)
    (H1i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                             (ext_bits_of_PTE pte1)) s = Some (false, s))
    (H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true)
    (H0i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                             (ext_bits_of_PTE pte0)) s = Some (false, s))
    (H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false)
    (Hchk0 : forall s, exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                               (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                               (ext_bits_of_PTE pte0) tt) s = Some (PTE_Check_Success tt, s))
    (H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false)
    (asid : mword 16) (pte' : mword 64) s :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (lookup_TLB 39 asid vpn) s = Some (None, s) ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (InstructionFetch tt) = Some pte' ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (translate 39 asid root vpn (InstructionFetch tt) User mxr do_sum tt) s
    = Some (Err (PTW_PTE_Needs_Update tt, tt), s).
Proof.
  intros Hmisa Hlk Hupd_some Hrd2 Hrd1 Hrd0 Hmenv.
  apply (exec_translate_walk_user_err vpn (InstructionFetch tt) User mxr do_sum
           asid root (PTW_PTE_Needs_Update tt) s Hlk).
  exact (exec_translate_TLB_miss_user_needs_update vpn root pte2 pte1 pte0
           (InstructionFetch tt) User mxr do_sum
           H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N asid pte' s
           Hmisa Hupd_some Hrd2 Hrd1 Hrd0 Hmenv).
Qed.

(* translate-abstract wrapper: whatever makes [translate] error (a TLB
   hit or the walk above), [translateAddr] for a fetch turns it into
   [E_Fetch_Page_Fault], no state change.  Generic over the [PTW_Error] f:
   the caller supplies the [translationException] reduction (which holds
   for Needs_Update, No_Permission, Invalid_PTE -- every non-access,
   non-extension fetch error). *)
Lemma exec_translateAddr_fetch_u_needs_update_of_translate
    (vpn : mword 27) (root : mword 44) (f : PTW_Error) (mxr do_sum : bool) (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (translate 39 (mword_of_int 0 : mword 16) root vpn (InstructionFetch tt) User mxr do_sum tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (InstructionFetch tt) f) s = Some (E_Fetch_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Err (E_Fetch_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hasid Hppn Htranslate Hte Hcanon Hvpn_def.
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
  rewrite (execR_liftR_seq _ _ _ _ _ Htranslate).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.


Section WpUserFetch.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation mie_v := (WpUserBase.mie_v U).
  Local Notation midl_v := (WpUserBase.midl_v U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation mip_v := (WpUserBase.mip_v U).
  Local Notation meip := (WpUserBase.meip U).
  Local Notation seip := (WpUserBase.seip U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation dqc := (WpUserBase.dqc U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation Htvd := (WpUserBase.Htvd U).
  Local Notation Hdel_ecall := (WpUserBase.Hdel_ecall U).
  Local Notation Hdel_fetchpf := (WpUserBase.Hdel_fetchpf U).
  Local Notation Hdel_loadpf := (WpUserBase.Hdel_loadpf U).
  Local Notation Hdel_samopf := (WpUserBase.Hdel_samopf U).
  Local Notation Hdel_illegal := (WpUserBase.Hdel_illegal U).
  Local Notation Hdel_break := (WpUserBase.Hdel_break U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).


  (* ------------------------------------------------------------------ *)
  (* USTEP case: the pc's vpn is UNMAPPED (or kernel-only).  One whole    *)
  (* machine step -- fetch page-faults through the walk, the delegated    *)
  (* trap tower runs, and the machine lands in [user_trap_frame].  The    *)
  (* first USTEP case proven against the loop frames.                     *)
  (* ------------------------------------------------------------------ *)
  Notation pf_cause := (rv64d_types.Exception (E_Fetch_Page_Fault tt)).


  Lemma ustep_fetch_unmapped
      (va : mword 64) (vpn : mword 27)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    upt_tlb_ok spec tlbvec ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va geometry (the 2-aligned RVC pc is a separate future case) *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvpn Hfwf Hok HSXL Hval Hcanon Hvpn_def.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    (* ---- pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    (* the fault fact, borrowing the state interp and the PT slots *)
    iAssert (⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
               = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr.
    { iApply (upt_translateAddr_fetch_unmapped root slots spec vpn va satp0 tlbvec
                false false σ Hvpn Hfwf Hok Lpriv HSXL' Lsatp Ltlb
                Hsatpmode Hasid Hroot Hcanon Hvpn_def
                HA' Hord' HR' Hcov' Hpter
                with "Hhw [Hreg Hmem] Hupt"). iFrame. }
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_v stvec_v elp0
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
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
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
            with "Hreg Hstv") as "[Hreg Hstv]".
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
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
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
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), va, va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* USTEP case: the pc's vpn IS mapped and hits the TLB, but the leaf's  *)
  (* A bit is clear -- under ADUE = 0 the needed update page-faults.      *)
  (* Same trap tower, no memory reads (the hit path reads no PT slots).   *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_fetch_adfault_hit
      (va : mword 64) (vpn : mword 27) (i : uwalk_info) (pte' : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) ->
    uw_check_ok (InstructionFetch tt) i ->
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = Some pte' ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk Hupd HSXL Hval Hcanon Hvpn_def.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    (* the hit-path fault, through the upt_entry bridges *)
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn i)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn i))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn i)) (InstructionFetch tt)
                      = Some pte').
    { rewrite upt_entry_pte. exact Hupd. }
    pose proof (exec_translateAddr_fetch_u_pagefault (upt_entry vpn i) vpn Hchk' pte' Hupd'
                  (upt_entry_match vpn i) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Lmenv'
                  Hcanon Hvpn_def) as Htr.
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_v stvec_v elp0
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
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
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
            with "Hreg Hstv") as "[Hreg Hstv]".
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
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
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
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), va, va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* USTEP case: the pc is NON-CANONICAL for Sv39 -- translateAddr faults *)
  (* before the TLB or the walk.  No memory reads, no PT dependence.      *)
  (* ------------------------------------------------------------------ *)
  (* the spatial fault fact for the A-update (ADUE=0) FETCH page fault:
     a mapped, permission-OK leaf whose A/D bits need an update the config
     forbids page-faults the fetch, whatever the TLB state (hit / hash
     collision / empty).  Reads the owned PT slots for the walk path; no
     state change.  The fetch-unconditional twin of the hit-only
     translate fact used by [ustep_fetch_adfault_hit]. *)
  Lemma upt_translateAddr_fetch_adfault
      (vpn : mword 27) (i : uwalk_info) (pte' : mword 64) (va : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (sigma : mstate) :
    spec !! vpn = Some i ->
    uw_check_ok (InstructionFetch tt) i ->
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = Some pte' ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege sigma.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus sigma.(sregs)) = 'b"10" ->
    register_lookup satp sigma.(sregs) = satp0 ->
    register_lookup tlb sigma.(sregs) = tlbvec ->
    register_lookup menvcfg sigma.(sregs) = MENVCFG_S ->
    register_lookup misa sigma.(sregs) = MISA_C ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sigma.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sigma.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sigma.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sigma.(sregs)) 0) * 4)%Z ->
    hw_config -∗
    mstate_interp sigma -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) sigma
       = Some (Err (E_Fetch_Page_Fault tt, tt), sigma)⌝.
  Proof.
    iIntros (Hsome Hchk Hupd Hok Lpriv LSXL Lsatp Ltlb Lmenv Lmisa Hcanon Hvpn_def HA Hord HR Hcov)
            "#Hhw Hint Hupt".
    iDestruct (upt_walk_read_ptes root slots spec vpn i sigma Hsome HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(Hrd2 & Hrd1 & Hrd0 & Hwf).
    iPureIntro.
    unfold uw_addr2, uw_addr1, uw_addr0 in Hrd2, Hrd1, Hrd0.
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    assert (Hupd' : update_PTE_Bits (autocast (T := mword) (uw_pte0 i) : mword 64)
                      (InstructionFetch tt) = Some pte').
    { rewrite autocast_id. exact Hupd. }
    assert (Htranslate : exec (translate 39 (mword_of_int 0 : mword 16) root vpn
                                 (InstructionFetch tt) User false false tt) sigma
                         = Some (Err (PTW_PTE_Needs_Update tt, tt), sigma)).
    { destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
      - destruct (Hok vpn ent Hslot) as (vpn0 & i0 & Hspec0 & Hhash & Hent).
        subst ent.
        destruct (eq_vec (sign_extend' (57 - 12) vpn0) (sign_extend' (57 - 12) vpn)) eqn:Hmv.
        + (* genuine TLB hit: vpn0 = vpn, i0 = i *)
          apply eq_vec_true_iff in Hmv. apply sext45_inj in Hmv. subst vpn0.
          rewrite Hsome in Hspec0. injection Hspec0 as Heqi. subst i0.
          assert (Hchk_te : forall (mxr do_sum : bool) s,
                    exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn i)) 7 0))
                            (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn i))) tt) s
                      = Some (PTE_Check_Success tt, s)).
          { rewrite upt_entry_pte. exact Hchk. }
          assert (Hupd_te : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn i))
                              (InstructionFetch tt) = Some pte').
          { rewrite upt_entry_pte. exact Hupd. }
          exact (exec_translate_u_needs_update (upt_entry vpn i) vpn Hchk_te pte' Hupd_te
                   (upt_entry_match vpn i) false false root tlbvec sigma Ltlb Hslot Lmenv).
        + (* hash collision: lookup misses, walk the page table *)
          assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sigma = Some (None, sigma)).
          { apply (exec_lookup_TLB_nomatch vpn (mword_of_int 0) (upt_entry vpn0 i0) tlbvec sigma
                     Ltlb Hslot).
            rewrite upt_entry_match_gen. exact Hmv. }
          exact (exec_translate_walk_user_needs_update vpn root (uw_pte2 i) (uw_pte1 i) (uw_pte0 i)
                   false false H2i H2nl H1i H1nl H0i H0nl (fun s => Hchk false false s) H0N
                   (mword_of_int 0) pte' sigma Lmisa Hlk Hupd' Hrd2 Hrd1 Hrd0 Lmenv).
      - (* empty slot: lookup misses, walk the page table *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sigma = Some (None, sigma)).
        { unfold lookup_TLB.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb sigma)).
          rewrite Ltlb. rewrite Hslot. apply exec_returnm. }
        exact (exec_translate_walk_user_needs_update vpn root (uw_pte2 i) (uw_pte1 i) (uw_pte0 i)
                 false false H2i H2nl H1i H1nl H0i H0nl (fun s => Hchk false false s) H0N
                 (mword_of_int 0) pte' sigma Lmisa Hlk Hupd' Hrd2 Hrd1 Hrd0 Lmenv). }
    assert (Hte : exec (translationException (InstructionFetch tt) (PTW_PTE_Needs_Update tt)) sigma
                  = Some (E_Fetch_Page_Fault tt, sigma)).
    { unfold translationException. cbn match. apply exec_returnm. }
    exact (exec_translateAddr_fetch_u_needs_update_of_translate vpn root (PTW_PTE_Needs_Update tt)
             false false va satp0 sigma
             Lpriv LSXL Lsatp Hsatpmode Hasid Hroot Htranslate Hte Hcanon Hvpn_def).
  Qed.

  Lemma ustep_fetch_adfault_u
      (va : mword 64) (vpn : mword 27) (i : uwalk_info) (pte' : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some i ->
    uw_check_ok (InstructionFetch tt) i ->
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = Some pte' ->
    upt_tlb_ok spec tlbvec ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va geometry (the 2-aligned RVC pc is a separate future case) *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hchk Hupd Hok HSXL Hval Hcanon Hvpn_def.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    (* ---- pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    (* the fault fact, borrowing the state interp and the PT slots *)
    iAssert (⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
               = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr.
    { assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
        by (rewrite Lmisa; exact Hmisa_val0).
      iApply (upt_translateAddr_fetch_adfault vpn i pte' va tlbvec σ
                Hsome Hchk Hupd Hok Lpriv HSXL' Lsatp Ltlb Lmenv Lmisa' Hcanon Hvpn_def
                HA' Hord' HR' Hcov'
                with "Hhw [Hreg Hmem] Hupt"). iFrame. }
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_v stvec_v elp0
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
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
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
            with "Hreg Hstv") as "[Hreg Hstv]".
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
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
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
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), va, va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  (* the spatial fault fact for the NOEXEC (no-permission) FETCH page
     fault: a mapped leaf that DENIES the fetch (no X / no U) page-faults,
     whatever the TLB state.  Fetch-unconditional twin analogous to the
     A-update fault, but the leaf FAILS the permission check (rather than
     needing an A-bit update). *)
  Lemma upt_translateAddr_fetch_noexec
      (vpn : mword 27) (i : uwalk_info) (va : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (sigma : mstate) :
    spec !! vpn = Some i ->
    uw_check_denied (InstructionFetch tt) i ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege sigma.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus sigma.(sregs)) = 'b"10" ->
    register_lookup satp sigma.(sregs) = satp0 ->
    register_lookup tlb sigma.(sregs) = tlbvec ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sigma.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sigma.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sigma.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sigma.(sregs)) 0) * 4)%Z ->
    hw_config -∗
    mstate_interp sigma -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) sigma
       = Some (Err (E_Fetch_Page_Fault tt, tt), sigma)⌝.
  Proof.
    iIntros (Hsome Hden Hok Lpriv LSXL Lsatp Ltlb Hcanon Hvpn_def HA Hord HR Hcov)
            "#Hhw Hint Hupt".
    iDestruct (upt_walk_read_ptes root slots spec vpn i sigma Hsome HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(Hrd2 & Hrd1 & Hrd0 & Hwf).
    iPureIntro.
    unfold uw_addr2, uw_addr1, uw_addr0 in Hrd2, Hrd1, Hrd0.
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    assert (Htranslate : exec (translate 39 (mword_of_int 0 : mword 16) root vpn
                                 (InstructionFetch tt) User false false tt) sigma
                         = Some (Err (PTW_No_Permission tt, tt), sigma)).
    { destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
      - destruct (Hok vpn ent Hslot) as (vpn0 & i0 & Hspec0 & Hhash & Hent).
        subst ent.
        destruct (eq_vec (sign_extend' (57 - 12) vpn0) (sign_extend' (57 - 12) vpn)) eqn:Hmv.
        + (* genuine TLB hit: vpn0 = vpn, i0 = i *)
          apply eq_vec_true_iff in Hmv. apply sext45_inj in Hmv. subst vpn0.
          rewrite Hsome in Hspec0. injection Hspec0 as Heqi. subst i0.
          assert (Hchk_te : forall (mxr do_sum : bool) s,
                    exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn i)) 7 0))
                            (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn i))) tt) s
                      = Some (PTE_Check_Failure (tt, PTE_No_Permission tt), s)).
          { rewrite upt_entry_pte. exact Hden. }
          exact (exec_translate_u_noperm (InstructionFetch tt) (upt_entry vpn i) vpn Hchk_te
                   (upt_entry_match vpn i) false false root tlbvec sigma Ltlb Hslot).
        + (* hash collision: lookup misses, walk the page table *)
          assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sigma = Some (None, sigma)).
          { apply (exec_lookup_TLB_nomatch vpn (mword_of_int 0) (upt_entry vpn0 i0) tlbvec sigma
                     Ltlb Hslot).
            rewrite upt_entry_match_gen. exact Hmv. }
          exact (exec_translate_walk_user_noperm vpn root (uw_pte2 i) (uw_pte1 i) (uw_pte0 i)
                   (InstructionFetch tt) false false H2i H2nl H1i H1nl H0i H0nl
                   (fun s => Hden false false s)
                   (mword_of_int 0) sigma Hlk Hrd2 Hrd1 Hrd0).
      - (* empty slot: lookup misses, walk the page table *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sigma = Some (None, sigma)).
        { unfold lookup_TLB.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb sigma)).
          rewrite Ltlb. rewrite Hslot. apply exec_returnm. }
        exact (exec_translate_walk_user_noperm vpn root (uw_pte2 i) (uw_pte1 i) (uw_pte0 i)
                 (InstructionFetch tt) false false H2i H2nl H1i H1nl H0i H0nl
                 (fun s => Hden false false s)
                 (mword_of_int 0) sigma Hlk Hrd2 Hrd1 Hrd0). }
    assert (Hte : exec (translationException (InstructionFetch tt) (PTW_No_Permission tt)) sigma
                  = Some (E_Fetch_Page_Fault tt, sigma)).
    { unfold translationException. cbn match. apply exec_returnm. }
    exact (exec_translateAddr_fetch_u_needs_update_of_translate vpn root (PTW_No_Permission tt)
             false false va satp0 sigma
             Lpriv LSXL Lsatp Hsatpmode Hasid Hroot Htranslate Hte Hcanon Hvpn_def).
  Qed.

  Lemma ustep_noexec_fetch_fault
      (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some i ->
    uw_check_denied (InstructionFetch tt) i ->
    upt_tlb_ok spec tlbvec ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va geometry (the 2-aligned RVC pc is a separate future case) *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hden Hok HSXL Hval Hcanon Hvpn_def.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    (* ---- pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    (* the fault fact, borrowing the state interp and the PT slots *)
    iAssert (⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
               = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr.
    { iApply (upt_translateAddr_fetch_noexec vpn i va tlbvec σ
                Hsome Hden Hok Lpriv HSXL' Lsatp Ltlb Hcanon Hvpn_def
                HA' Hord' HR' Hcov'
                with "Hhw [Hreg Hmem] Hupt"). iFrame. }
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_v stvec_v elp0
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
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
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
            with "Hreg Hstv") as "[Hreg Hstv]".
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
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
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
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), va, va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  Lemma ustep_fetch_noncanonical
      (va : mword 64)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok HSXL Hval Hcanon.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             Hcode Hdata Hcfg Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_u_noncanonical va satp0 σ
                  Lpriv HSXL' Lsatp Hsatpmode Hcanon) as Htr.
    pose proof (exec_fetch_u_pagefault_4 va σ Lpc Hval Htr) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) va
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr va)))
                  ms_v sc_v stvec_v elp0
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
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
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
            with "Hreg Hstv") as "[Hreg Hstv]".
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
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
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
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), va, va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


End WpUserFetch.
