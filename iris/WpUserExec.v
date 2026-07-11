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
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeTrap UmodeFetch UmodeStep UmodeEcall UmodeFetchFault UmodeWalk.
Require Import UptInv WpUserLoop WpUserEcall WpGprAddi WpGprLogic WpGprLui WpAuipc WpGprAuipc WpGprShift WpGprJal WpGprJalr WpMemsetS.
Local Open Scope Z_scope.
Import Defs.

Section WpUserExec.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* Loop-constant parameters: the boot configuration, the page table,   *)
  (* and the user memory image.                                          *)
  (* ------------------------------------------------------------------ *)
  Context (stvec_v mie_v midl_v medl_v mip_v : mword 64).
  Context (meip seip : mword 1).
  Context (satp0 : mword 64).
  Context (root : mword 44).
  Context (slots : gmap (mword 64) (mword 64)).
  Context (spec : gmap (mword 27) uwalk_info).
  Context (pmpcfg0 : type_of_register pmpcfg_n).
  Context (pmpaddr00 : type_of_register pmpaddr_n).
  (* user code bytes: immutable, hence persistent ([↦ₘ□]) *)
  Context (code : gmap Arch.pa (bv 8)).
  (* user data byte addresses: owned writable, contents existential *)
  Context (data : gset Arch.pa).
  Context {dq dqc : dfrac}.

  (* ---- pure boot-config hypotheses (loop-constant) ---- *)
  (* no interrupt can become pending in U-mode *)
  Hypothesis Hmm : and_vec mie_v (not_vec midl_v) = zeros' 64.
  Hypothesis Hs0 :
    and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v midl_v) = zeros' 64.
  (* satp: Sv39, asid 0, rooted at [root] *)
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid :
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16).
  Hypothesis Hroot :
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
  (* stvec: direct mode *)
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  (* every synchronous U-mode cause the loop can raise is delegated *)
  Hypothesis Hdel_ecall : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true.
  Hypothesis Hdel_fetchpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true.
  Hypothesis Hdel_loadpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Load_Page_Fault tt)))) = true.
  Hypothesis Hdel_samopf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_SAMO_Page_Fault tt)))) = true.
  Hypothesis Hdel_illegal : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true.
  Hypothesis Hdel_break : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true.
  (* PMP entry 0: an RWX TOR entry covering all of RAM *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false.
  Hypothesis HpmpX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis Hpmp_cov : (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z.
  (* the boot PMA list supports PTE reads everywhere (concrete-list fact) *)
  Hypothesis Hpter : forall regions, pma_allows_all regions -> pma_allows_pte_read regions.
  (* the slot map describes the page table rooted at [root] *)
  Hypothesis Hspec : upt_spec root slots spec.

  (* ------------------------------------------------------------------ *)
  (* The frames                                                          *)
  (* ------------------------------------------------------------------ *)

  (* the loop-constant config cells (fraction [dqc]: never written) *)
  Definition user_cfg : iProp Σ :=
    (stvec ↦ᵣ{ dqc } stvec_v ∗
     mie ↦ᵣ{ dqc } mie_v ∗
     mideleg ↦ᵣ{ dqc } midl_v ∗
     medeleg ↦ᵣ{ dqc } medl_v ∗
     mip ↦ᵣ{ dqc } mip_v ∗
     sig_meip ↦ᵣ{ dqc } meip ∗
     sig_seip ↦ᵣ{ dqc } seip ∗
     satp ↦ᵣ{ dqc } satp0 ∗
     menvcfg ↦ᵣ{ dqc } MENVCFG_S ∗
     senvcfg ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     mstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     sstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 32) ∗
     pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 ∗
     pmpaddr_n ↦ᵣ{ dqc } pmpaddr00)%I.

  (* the user memory image: persistent code bytes + owned data bytes
     (contents existential -- stores retarget them freely) *)
  Definition user_code : iProp Σ :=
    ([∗ map] a ↦ b ∈ code, a ↦ₘ□ b)%I.
  Definition user_data : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8), ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₘ b)%I.

  Global Instance user_code_persistent : Persistent user_code.
  Proof. apply _. Qed.

  (* P: an arbitrary user machine over the constant config.  Everything
     an instruction can change is existential: GPRs, pc, the trap CSRs
     (traps leave the loop, but the OLD values are unconstrained on
     entry), mstatus (SXL pinned), and the TLB (walk fills change it,
     [upt_tlb_ok] survives by upt_tlb_ok_fill). *)
  Definition user_frame : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v va : mword 64)
       (g : gmap regidx (mword 64))
       (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      ⌜_get_Mstatus_SXL ms_v = 'b"10"⌝ ∗
      ⌜upt_tlb_ok spec tlbvec⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ User ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      tlb ↦ᵣ tlbvec ∗
      pc_is va ∗
      gpr_file g ∗
      upt_inv root slots spec ∗
      user_code ∗
      user_data ∗
      user_cfg)%I.

  (* Tr: the machine handed to the kernel re-entry continuation.  The
     trap CSR VALUES are existential at this level; the USTEP cases that
     produce Tr know the exact cause/tval/sepc and can be consumed
     directly when a caller needs them -- this frame is the join point
     the Löb loop needs. *)
  Definition user_trap_frame : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v : mword 64)
       (g : gmap regidx (mword 64))
       (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      ⌜upt_tlb_ok spec tlbvec⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ Supervisor ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      tlb ↦ᵣ tlbvec ∗
      pc_is (stvec_base stvec_v) ∗
      gpr_file g ∗
      upt_inv root slots spec ∗
      user_code ∗
      user_data ∗
      user_cfg)%I.

  (* ------------------------------------------------------------------ *)
  (* The USTEP obligation and the capstone                               *)
  (* ------------------------------------------------------------------ *)

  (* one machine step from the user frame: retire back into the frame,
     or trap into the kernel re-entry frame -- both under a later, as
     the step engines provide *)
  Definition user_step_obligation E (Φ : mval -> iProp Σ) : iProp Σ :=
    (□ (user_frame -∗
        ▷ ((user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
           (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}))%I.

  (* the user-execution theorem, given the per-step case analysis *)
  Theorem wp_user_exec E (Φ : mval -> iProp Σ) :
    user_step_obligation E Φ -∗
    user_frame -∗
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros "#Hstep HP Htr".
    iApply (wp_user_loop with "Hstep HP Htr").
  Qed.

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
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
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
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
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
  (* The U-mode RETIRE engine (TLB-hit, 4-byte, integer families): the    *)
  (* user analog of InstrBytes' [wp_instr].  Fetch goes through the Sv39  *)
  (* hit path at the stored walk entry; decode is a per-word hypothesis   *)
  (* at the concrete [dstateU] (the shape [decode_total_u] instances      *)
  (* provide); the caller supplies ONE execute fact (RETIRE_SUCCESS) at   *)
  (* nextPC := va + 4 and gets the ticked PC back under a later.  FP is   *)
  (* excluded structurally: mstatus.FS = Off in U makes every FP          *)
  (* instruction trap, so the retire engine never sees one.               *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_instr_u_hit
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ tlbvec -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the leaf facts, transported onto the stored TLB entry *)
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- the instruction bytes + RAM-ness of the user code page ---- *)
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* ---- pure facts: fetch, decode, dispatch at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- the caller's execute fact ---- *)
    iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
            with "[$Hreg $Hmem]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* USTEP case: the pc is NON-CANONICAL for Sv39 -- translateAddr faults *)
  (* before the TLB or the walk.  No memory reads, no PT dependence.      *)
  (* ------------------------------------------------------------------ *)
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
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
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
  (* USTEP case: ECALL.  The pc's vpn is mapped, hits the TLB at its walk *)
  (* entry, A bit set, the code bytes at the translated pa spell ecall -- *)
  (* the whole wp_user_ecall vertical slice, replayed against the loop    *)
  (* frames and landing in [user_trap_frame].                             *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_ecall
      (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some i ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) ->
    uw_check_ok (InstructionFetch tt) i ->
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None ->
    (* the fetched bytes are the ecall word *)
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte ecall_w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true ->
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
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hok Hvec Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the leaf facts, transported onto the stored TLB entry *)
    destruct (Hspec vpn i Hsome) as (_ & _ & _ & Hwf).
    destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & Hpbmt0).
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn i)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn i))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn i)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn i)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn i s0 Hpbmt0). }
    (* the persistent ecall bytes, looked up in the code image *)
    iAssert ([∗ list] j ∈ seq 0 4,
               (pa_add (u_pa (upt_entry vpn i) va vpn) j) ↦ₘ□ nth_byte ecall_w j)%I
      as "#Hbytes".
    { iApply big_sepL_intro. iIntros "!>" (k y Hky).
      apply lookup_seq in Hky. destruct Hky as [-> Hk].
      assert (Heq : (0 + k)%nat = k) by lia. rewrite Heq.
      iApply (big_sepM_lookup _ _ _ _ (Hcw k Hk) with "Hcode"). }
    iApply (wp_user_ecall (upt_entry vpn i) vpn va satp0 ms_v sc_v stval_v sepc_v
              stvec_v mie_v midl_v mip_v medl_v MENVCFG_S meip seip tlbvec
              pmpcfg0 pmpaddr00 E Φ
              HN Hmm Hs0 HSXL Hsatpmode Hasid Hvec Hchk' Hupd' Hpbmt'
              (upt_entry_match vpn i) Hval Hcanon Hvpn_def Hpaal
              HpmpA Hpmp_ord HpmpX Hpmp_cov Htvd Hdel_ecall eq_refl
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Hstvec Hmie Hmidl
                    Hmedl Hmip Hmeip Hseip Hsatp Htlbc Hmenv Hsenv Hmst0 Hsst0
                    Hpmpc Hpmpa Hbytes Hpc").
    iIntros "Hpriv Hms Hsc Hstv Hsepc Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip
             Hsatp Htlbc Hmenv Hsenv Hmst0 Hsst0 Hpmpc Hpmpa Hhs Hpc".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (u_trap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (u_trap_cause sc_v), (tval None), va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpc".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* USTEP case: ADDI (rd <> x0) -- the FIRST RETIRING instruction case.  *)
  (* Rides [wp_instr_u_hit]; the machine steps and RE-ESTABLISHES the     *)
  (* user frame: rd updated in the gpr file, pc advanced by 4, everything *)
  (* else unchanged.  The template for every integer compute family.      *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_addi
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this ADDI *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0)) ->
    uint rd <> 0 ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    (* completeness gives the (total) lookups for rs1 and rd *)
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC first, so we read rs1 against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read the rs1 entry (x0 or a real register) -> the ADDI value *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addi_val rs1 imm (set_reg σ nextPC (add_vec_int va 4))
                  = add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val. rewrite Hrv. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (g !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int va 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: rebuild the user frame at pc+4 with rd updated *)
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (g !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (add_vec (g !!! Regidx rs1)
                              (sign_extend' 64 imm))]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The GENERIC ITYPE retire case: any immediate-compute op whose        *)
  (* execute writes rd := f(rs1-value, imm) and retires.  Instantiated    *)
  (* by the per-op [exec_execute_ITYPE_*_gpr] lemmas (ADDI / ORI / ANDI / *)
  (* XORI / ...), so each op needs NO further Iris proof.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_itype (op : iop) (f : mword 64 -> mword 12 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact *)
    (forall (rs1' rd' : mword 5) (imm' : mword 12) s,
       exec (execute (ITYPE (imm', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            imm')))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this ITYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (ITYPE (imm, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u_hit va vpn ie w (ITYPE (imm, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) imm))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) imm))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) imm))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) imm)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* the four proven immediate-compute ops, as direct instantiations *)
  Definition ustep_ori := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ORI (fun v i => or_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ORI_gpr rs1' rd' imm' s).
  Definition ustep_andi := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ANDI (fun v i => and_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ANDI_gpr rs1' rd' imm' s).
  Definition ustep_xori := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype XORI (fun v i => xor_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_XORI_gpr rs1' rd' imm' s).
  Definition ustep_addi' := fun va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_itype ADDI (fun v i => add_vec v (sign_extend' 64 i))
      va vpn ie w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' imm' s => exec_execute_ITYPE_ADDI_gpr rs1' rd' imm' s).

  (* ------------------------------------------------------------------ *)
  (* The GENERIC RTYPE retire case: any register-register op whose        *)
  (* execute writes rd := f(rs1-value, rs2-value) and retires.            *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_rtype (op : rop) (f : mword 64 -> mword 64 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op's register-generic execute fact (nonzero-rd form) *)
    (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
       exec (execute (RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                 (regval_into_reg
                    (f (if Z.eqb (uint rs1') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                       (if Z.eqb (uint rs2') 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode: w is this RTYPE op *)
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
                       = false) by (destruct op; reflexivity).
    iApply (wp_instr_u_hit va vpn ie w (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs2 rs1 rd (set_reg σ nextPC (add_vec_int va 4)) Hrd) as HE.
      rewrite Hrv1 in HE. rewrite Hrv2 in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2)))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) (g !!! Regidx rs2))]> g),
            tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ADD's if-form execute fact, in the nonzero-rd shape the generic wants *)
  Lemma exec_execute_RTYPE_ADD_gpr_nz (rs2 rs1 rd : mword 5) s :
    uint rd <> 0 ->
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (gpr_rd_val rs2 rs1 s))).
  Proof.
    intro Hrd.
    pose proof (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s) as H.
    replace (Z.eqb (uint rd) 0) with false in H
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    exact H.
  Qed.

  (* the four proven register-register ops, as direct instantiations *)
  Definition ustep_add := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype ADD (fun v1 v2 => add_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_ADD_gpr_nz rs2' rs1' rd' s Hrd).
  Definition ustep_or := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype OR (fun v1 v2 => or_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_OR_gpr rs2' rs1' rd' s Hrd).
  Definition ustep_and := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype AND (fun v1 v2 => and_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_AND_gpr rs2' rs1' rd' s Hrd).
  Definition ustep_xor := fun va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_rtype XOR (fun v1 v2 => xor_vec v1 v2)
      va vpn ie w rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs2' rs1' rd' s Hrd => exec_execute_RTYPE_XOR_gpr rs2' rs1' rd' s Hrd).

  (* ------------------------------------------------------------------ *)
  (* The GENERIC UTYPE retire case (LUI / AUIPC): no source register; the *)
  (* written value [V imm s] may read the pc (AUIPC), pinned to [v] by    *)
  (* the [HV] agreement hypothesis at any state whose PC is [va].         *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_utype (op : uop) (V : mword 20 -> mstate -> mword 64) (v : mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 20) (rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rd' : mword 5) (imm' : mword 20) s,
       exec (execute (UTYPE (imm', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg (V imm' s)))) ->
    (forall s', register_lookup PC s'.(sregs) = va -> V imm s' = v) ->
    upt_tlb_ok spec tlbvec ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op HV Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (UTYPE (imm, Regidx rd, op)) = false)
      by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (UTYPE (imm, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* PC is untouched by the nextPC tick, so [V] evaluates to [v] *)
    assert (HpcX : register_lookup PC
              (set_reg σ nextPC (add_vec_int va 4)).(sregs) = va).
    { unfold set_reg; cbn [sregs]. tmig. exact Hpceq. }
    pose proof (HV (set_reg σ nextPC (add_vec_int va 4)) HpcX) as Hv.
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rd imm (set_reg σ nextPC (add_vec_int va 4))) as HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hv in HE.
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg v]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* LUI: the value is imm-only *)
  Definition ustep_lui := fun va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_utype LUI (fun imm' _ => luival imm') (luival imm)
      va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rd' imm' s => exec_execute_UTYPE_LUI_gpr rd' imm' s)
      (fun s' _ => eq_refl).
  (* AUIPC: the value reads the pc *)
  Definition ustep_auipc := fun va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_utype AUIPC (fun imm' s => add_vec (register_lookup PC s.(sregs)) (auipc_off imm'))
      (add_vec va (auipc_off imm))
      va vpn ie w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rd' imm' s => exec_execute_UTYPE_AUIPC_gpr rd' imm' s)
      (fun s' Hpc => f_equal (fun x => add_vec x (auipc_off imm)) Hpc).

  (* ------------------------------------------------------------------ *)
  (* The GENERIC SHIFTIOP retire case (SLLI / SRLI): rd := f(rs1, shamt). *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_shiftiop (op : sop) (f : mword 64 -> mword 6 -> mword 64)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (shamt : mword 6) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (rs1' rd' : mword 5) (shamt' : mword 6) s,
       exec (execute (SHIFTIOP (shamt', Regidx rs1', Regidx rd', op))) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg
                         (f (if Z.eqb (uint rs1') 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                            shamt')))) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op), s0)) ->
    uint rd <> 0 ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_op Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hrd.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int va 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (f (g !!! Regidx rs1) shamt))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (f (g !!! Regidx rs1) shamt))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int va 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (f (g !!! Regidx rs1) shamt))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_op rs1 rd shamt (set_reg σ nextPC (add_vec_int va 4))) as HE.
      rewrite Hrv in HE.
      replace (Z.eqb (uint rd) 0) with false in HE
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int va 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (f (g !!! Regidx rs1) shamt))).(sregs)
             = add_vec_int va 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4),
            (<[Regidx rd := regval_into_reg (f (g !!! Regidx rs1) shamt)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Definition ustep_slli := fun va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_shiftiop SLLI (fun v sh => shift_bits_left v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0))
      va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' shamt' s => exec_execute_SHIFTIOP_SLLI_gpr rs1' rd' shamt' s).
  Definition ustep_srli := fun va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_shiftiop SRLI (fun v sh => shift_bits_right v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0))
      va vpn ie w shamt rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun rs1' rd' shamt' s => exec_execute_SHIFTIOP_SRLI_gpr rs1' rd' shamt' s).

  (* ------------------------------------------------------------------ *)
  (* USTEP case: JAL (rd <> x0) -- the first CONTROL TRANSFER.  The       *)
  (* machine retires with nextPC := va + imm and rd := va + 4; the frame  *)
  (* repacks with pc_is at the JUMP TARGET.  (The target's alignment      *)
  (* hypotheses match exec_execute_JAL_gpr's non-RVC check form.)         *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_jal
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 21) (rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0)) ->
    uint rd <> 0 ->
    (* target alignment (the non-RVC check form of exec_execute_JAL_gpr) *)
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (JAL (imm, Regidx rd)) = false)
      by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (JAL (imm, Regidx rd))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HpcX : register_lookup PC s1.(sregs) = va).
    { unfold s1, set_reg; cbn [sregs]. tmig. exact Hpceq. }
    assert (HnpcX : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    (* the execute writes nextPC := target, then rd := va + 4 *)
    iMod (reg_update _ nextPC _ (add_vec va (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int va 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int va 4)) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int va 4))).
    iSplitR.
    { iPureIntro.
      pose proof (exec_execute_JAL_gpr imm rd s1 Hrd) as HE.
      rewrite HpcX in HE.
      specialize (HE Hal0 Hal1).
      rewrite HnpcX in HE.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int va 4))).(sregs)
             = add_vec va (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec va (sign_extend' 64 imm)),
            (<[Regidx rd := regval_into_reg (add_vec_int va 4)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* decode-state agreement survives a nextPC write (nextPC is outside
     the decode read set D_u) *)
  Lemma agree_u_set_nextPC (s : mstate) (v : mword 64) :
    agree_on D_u s dstateU ->
    agree_on D_u (set_reg s nextPC v) dstateU.
  Proof.
    intros H r Hr.
    pose proof Hr as Hr'.
    unfold D_u in Hr'.
    unfold set_reg; cbn [sregs].
    repeat (apply orb_true_elim in Hr' as [Hr'|Hr']);
      apply register_beq_eq in Hr'; subst r;
      (rewrite irrelevant_register_set; [ exact (H _ Hr) | vm_compute; reflexivity ]).
  Qed.

  (* Zicfilp is disabled at the user decode state (mseccfg.MLPE = 0,
     menvcfg.LPE = 0): transported by the read-frame bridge, like the
     per-word decode facts *)
  Lemma exec_cE_zicfilp_false_u (s : mstate) :
    agree_on D_u s dstateU ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
  Proof.
    intros Hag.
    apply (decode_state_bridge D_u _ dstateU);
      [ exact Hag | vm_compute; reflexivity | vm_compute; reflexivity ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* USTEP case: JALR (rd <> x0) -- indirect jump.  Target = (rs1 + imm)  *)
  (* with bit 0 cleared; rd := va + 4; pc_is repacks at the target.       *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_jalr
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0)) ->
    uint rd <> 0 ->
    (* target alignment, in terms of the FRAME's rs1 value *)
    eq_vec (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 1) = false ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hrd Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (JALR (imm, Regidx rs1, Regidx rd)) = false)
      by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (JALR (imm, Regidx rs1, Regidx rd))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : g !! Regidx rd = Some (g !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HnpcX : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    (* rs1's value at the execute state is the frame's *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hjb : jbase rs1 s1 = g !!! Regidx rs1).
    { unfold jbase. rewrite Hrv. reflexivity. }
    (* the Zicfilp probe at the execute state (agreement survives the
       nextPC tick -- nextPC is outside the decode read set) *)
    pose proof (exec_cE_zicfilp_false_u s1
                  (agree_u_set_nextPC σ (add_vec_int va 4) Hag)) as HZ.
    (* the execute writes nextPC := target, then rd := va + 4 *)
    iMod (reg_update _ nextPC _ (jalr_target (g !!! Regidx rs1) imm)
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int va 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int va 4)) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg s1 nextPC (jalr_target (g !!! Regidx rs1) imm))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int va 4))).
    iSplitR.
    { iPureIntro.
      pose proof (exec_execute_JALR_gpr imm rs1 rd s1 Hrd) as HE.
      rewrite Hjb in HE.
      specialize (HE HZ Hal0 Hal1).
      rewrite HnpcX in HE.
      change (execute (JALR (imm, Regidx rs1, Regidx rd)))
        with (execute_JALR imm (Regidx rs1) (Regidx rd)).
      exact HE. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg s1 nextPC (jalr_target (g !!! Regidx rs1) imm))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int va 4))).(sregs)
             = jalr_target (g !!! Regidx rs1) imm).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (jalr_target (g !!! Regidx rs1) imm),
            (<[Regidx rd := regval_into_reg (add_vec_int va 4)]> g), tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The GENERIC BRANCH retire cases (BEQ / BNE ...): the comparison [c]  *)
  (* on the two source values decides taken vs fall-through; neither arm  *)
  (* writes a register.  [rvv] is WpMemsetS's register-value reader.      *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_branch_fall (op : bop) (c : mword 64 -> mword 64 -> bool)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
       c (rvv rs1' s) (rvv rs2' s) = false ->
       exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
         = Some (RETIRE_SUCCESS, s)) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    (* the branch is NOT taken, in frame terms *)
    c (g !!! Regidx rs1) (g !!! Regidx rs2) = false ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_f Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hcmp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (BTYPE (imm, Regidx rs2, Regidx rs1, op))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (BTYPE (imm, Regidx rs2, Regidx rs1, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iModIntro.
    iExists s1.
    iSplitR.
    { iPureIntro.
      apply (Hexec_f imm rs2 rs1 s1).
      unfold rvv. rewrite Hrv1 Hrv2. exact Hcmp. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC s1.(sregs) = add_vec_int va 4).
    { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4), g, tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

  Lemma ustep_branch_taken (op : bop) (c : mword 64 -> mword 64 -> bool)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (imm : mword 13) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
       c (rvv rs1' s) (rvv rs2' s) = true ->
       eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                 (sign_extend' 64 imm')) 0) ('b"0") = true ->
       bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                 (sign_extend' 64 imm')) 1) = false ->
       exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
         = Some (RETIRE_SUCCESS,
                 set_reg s nextPC (add_vec (register_lookup PC s.(sregs))
                                     (sign_extend' 64 imm')))) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) ->
    (* the branch IS taken, in frame terms; target aligned (non-RVC form) *)
    c (g !!! Regidx rs1) (g !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
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
    (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hexec_t Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hcmp Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc [Hpcr Hnpc]
             [%Hdom Hfmap] Hupt #Hcode Hdata Hcfg Hcont".
    assert (Hnlpad : is_lpad_instruction (BTYPE (imm, Regidx rs2, Regidx rs1, op))
                       = false) by reflexivity.
    iApply (wp_instr_u_hit va vpn ie w (BTYPE (imm, Regidx rs2, Regidx rs1, op))
              ms_v tlbvec E Φ HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
              Hvpn_def Hpaal HnotRVC Hdec Hnlpad
              with "Hhw Hinv Hhs Hpriv Hms Htlbc Hpcr Hcode Hcfg").
    iIntros (σ Hpceq Hag) "[Hreg Hmem]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : g !! Regidx rs2 = Some (g !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s1 := set_reg σ nextPC (add_vec_int va 4)).
    assert (HpcX : register_lookup PC s1.(sregs) = va).
    { unfold s1, set_reg; cbn [sregs]. tmig. exact Hpceq. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) s1 with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (g !!! Regidx rs2) s1 with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    (* the taken execute writes nextPC := target *)
    iMod (reg_update _ nextPC _ (add_vec va (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro.
      pose proof (Hexec_t imm rs2 rs1 s1) as HE.
      rewrite HpcX in HE.
      apply HE; [ | exact Hal0 | exact Hal1 ].
      unfold rvv. rewrite Hrv1 Hrv2. exact Hcmp. }
    iSplitL "Hreg Hmem".
    { unfold s1, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpriv' Hms' Htlbc' Hpc' Hcfg'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s1 nextPC (add_vec va (sign_extend' 64 imm))).(sregs)
             = add_vec va (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iNext.
    iApply "Hcont".
    rewrite /user_frame.
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec va (sign_extend' 64 imm)), g, tlbvec.
    iFrame "Hhs' Hpriv' Hms' Hsc Hstv Hsepc Htlbc' Hupt Hcode Hdata Hcfg'".
    iSplitR; [iPureIntro; exact HSXL |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hpc' Hnpc"; [iFrame "Hpc' Hnpc" |].
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

  (* the four proven branch arms, as direct instantiations *)
  Definition ustep_bne_fall := fun va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_branch_fall BNE (fun v1 v2 => neq_vec v1 v2)
      va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun imm' rs2' rs1' s Hf => exec_execute_BTYPE_BNE_fall imm' rs2' rs1' s Hf).
  Definition ustep_beq_fall := fun va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_branch_fall BEQ (fun v1 v2 => eq_vec v1 v2)
      va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun imm' rs2' rs1' s Hf => exec_execute_BTYPE_BEQ_fall imm' rs2' rs1' s Hf).
  Definition ustep_bne_taken := fun va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_branch_taken BNE (fun v1 v2 => neq_vec v1 v2)
      va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun imm' rs2' rs1' s Ht H0 H1 => exec_execute_BTYPE_BNE_taken imm' rs2' rs1' s Ht H0 H1).
  Definition ustep_beq_taken := fun va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN =>
    ustep_branch_taken BEQ (fun v1 v2 => eq_vec v1 v2)
      va vpn ie w imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ HN
      (fun imm' rs2' rs1' s Ht H0 H1 => exec_execute_BTYPE_BEQ_taken imm' rs2' rs1' s Ht H0 H1).

End WpUserExec.
