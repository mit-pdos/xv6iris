(* WpIntrInv.v -- an ABSTRACT S-mode interrupt invariant.

   The invariant [intr_inv F handler] owns the sstatus (mstatus) and stvec
   registers and states the S-mode interrupt-safety discipline:

     EITHER  interrupts are disabled (sstatus.SIE = 0), so no trap can fire
             and there is nothing more to prove;

     OR      interrupts are enabled (sstatus.SIE = 1 -- together with the
             ambient MPRV/SXL/MXR/TSR facts of [acq_ms_facts]), stvec points
             at [handler], and we hold [intr_handler_spec handler F]: a
             persistent WP obligation saying that taking the interrupt --
             jumping to [handler] in the trapped mstatus -- runs the handler
             and returns IDEMPOTENTLY to the interrupted pc with the SIE=1
             facts (hence the invariant) re-established.  [F] is the frame of
             everything else the handler consumes and hands back unchanged.

   [intr_handler_spec] is a simplified, address-agnostic distillation of what
   kernelvec does (save 17 regs, kerneltrap, restore, SRET): it hides the
   17-slot geometry inside [F] and exposes only the round-trip contract that a
   client needs to close a Loeb loop across an interrupt.

   We prove
     - [intr_inv_establish]: the invariant can be created whenever stvec ->
       kernelvec and kernelvec satisfies the spec; and
     - [kernelvec_handler_spec]: kernelvec's WP ([wp_kernelvec_hit] + the
       [trap_ms]/[sret_ms5] round-trip lemmas) DOES satisfy the spec, for the
       concrete kernelvec frame [F_kv]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc WpGprAddi WpGprMret.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpKvInstr.
Require Import WpKernelvecNew.
Require Import WpIntrBits WpIntrCore WpIntrStep.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrInv.
  Context `{!riscvGS Sig}.
  Context `{!sieG Sig}.
  Context `{CID : CpuId}.

  (* The mstatus fact set carried across the round trip: SIE=1 (interrupts
     enabled), MPRV=0, SXL=2, MXR=0, TSR=0.  Reused from WpIntrStep. *)
  Notation ms_pre_facts := acq_ms_facts.

  (* --------------------------------------------------------------------- *)
  (* The concrete kernelvec frame: everything [wp_kernelvec_hit] consumes and
     returns beyond the mstatus / sepc / stvec / pc / privilege / hart_state
     that the handler spec threads explicitly.  The 17 caller-saved stack
     windows are existential over their CONTENTS (the round trip overwrites
     them with the restored register values), so [F_kv] is preserved as a
     whole.  hw_config / minstret_inv / kernel_text are persistent. *)
  Definition F_kv (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (menvcfg0 : mword 64)
      : iProp Sig :=
    (hw_config ∗ minstret_inv ∗ kernel_text ∗
     menvcfg ↦ᵣ menvcfg0 ∗
     tlb_inv root_ppn ∗
     gpr_file m ∗
     (∃ w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : bv 64,
        ((((kv_sp1 m)))) ↦₈ w1 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ w2 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ w3 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ w4 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ w5 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ w6 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ w7 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ w8 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ w9 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ w10 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ w11 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ w12 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ w13 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ w14 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ w15 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ w16 ∗
        (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ w17))%I.

  (* --------------------------------------------------------------------- *)
  (* The abstract handler contract.  Persistent (□), so it lives freely inside
     the invariant.  Reading: for any interrupted pc [pc0] (instruction-
     aligned, so [sret_tgt pc0 = pc0]) and any mstatus [ms] with the SIE=1
     fact set, if we are AT [handler] in the trapped mstatus [trap_ms elp_v ms]
     with sepc = pc0 and the frame [F], then the machine returns to pc0 with
     mstatus = [sret_ms5 (trap_ms elp_v ms)] (SIE restored to 1 by
     [roundtrip_SIE]) and [F] intact -- exactly what re-establishing the
     invariant and closing a Loeb loop needs. *)
  Definition intr_handler_spec (handler : mword 64) (F : iProp Sig) : iProp Sig :=
    (□ ∀ (elp_v : mword 1) (ms pc0 mie_v mdv0 : mword 64) E (Φ : mval -> iProp Sig),
        ⌜ ↑minstretN ⊆ E ⌝ -∗
        ⌜ ms_pre_facts ms ⌝ -∗
        ⌜ sret_tgt pc0 = pc0 ⌝ -∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        mstatus ↦ᵣ trap_ms elp_v ms -∗
        mie ↦ᵣ mie_v -∗
        mideleg ↦ᵣ mdv0 -∗
        sepc ↦ᵣ pc0 -∗
        stvec ↦ᵣ handler -∗
        pc_is handler -∗
        F -∗
        ( hart_state ↦ᵣ HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ Supervisor -∗
          mstatus ↦ᵣ sret_ms5 (trap_ms elp_v ms) -∗
          mie ↦ᵣ mie_v -∗
          mideleg ↦ᵣ mdv0 -∗
          (∃ v : mword 64, sepc ↦ᵣ v) -∗
          stvec ↦ᵣ handler -∗
          pc_is pc0 -∗
          F -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }} ) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }})%I.

  Global Instance intr_handler_spec_persistent handler F :
    Persistent (intr_handler_spec handler F).
  Proof. apply _. Qed.

  (* --------------------------------------------------------------------- *)
  (* THE INVARIANT: owns sstatus (mstatus) and stvec; either interrupts are
     off, or they are on and the handler spec holds at [handler]. *)
  Definition intr_inv (F : iProp Sig) (handler : mword 64) : iProp Sig :=
    (∃ ms : mword 64,
       mstatus ↦ᵣ ms ∗
       ( (⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗ (∃ v : mword 64, stvec ↦ᵣ v))
         ∨ (⌜ ms_pre_facts ms ⌝ ∗ stvec ↦ᵣ handler ∗ intr_handler_spec handler F) ))%I.

  (* ===================================================================== *)
  (* Establishing the invariant when stvec -> kernelvec.                    *)
  (* ===================================================================== *)
  Lemma intr_inv_establish (F : iProp Sig) (ms : mword 64) :
    ms_pre_facts ms ->
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64) F -∗
    mstatus ↦ᵣ ms -∗
    stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    intr_inv F (mword_of_int KernelSyms.kernelvec : mword 64).
  Proof.
    intros Hfacts. iIntros "#Hspec Hms Hstvec".
    iExists ms. iFrame "Hms". iRight. iFrame "Hstvec Hspec".
    iPureIntro. exact Hfacts.
  Qed.

  (* ===================================================================== *)
  (* kernelvec satisfies the handler spec.  This is [wp_kernelvec_hit] with
     the entering mstatus specialized to [trap_ms elp_v ms]: the six mstatus /
     SRET-privilege side conditions are DISCHARGED from [ms_pre_facts ms] via
     the WpIntrBits round-trip lemmas, and the returned pc [sret_tgt pc0]
     collapses to [pc0] under the instruction-alignment premise. *)
  Lemma kernelvec_handler_spec (root_ppn : mword 44) (svpn : mword 27)
      (m : gmap regidx (mword 64))
      (menvcfg0 : mword 64)
      :
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* the walk's PTE read *)
    (* PMP: TOR entry 0 grants X on the whole kernelvec text + R/W on the frame *)
    (* stack-page geometry (symbolic sp; svpn = its Sv39 VPN) *)
    (* SRET facts *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    ⊢ intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64)
        (F_kv root_ppn svpn m menvcfg0).
  Proof.
    intros HPBMTE Hmenvval0 Hpmm Hlpe0 HFIOM.
    iModIntro. iIntros (elp_v ms pc0 mie_v mdv0 E Φ) "%HN %Hfacts %Hpc0 %Hmm Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec Hpc HF Hcont".
    pose proof Hfacts as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "HF" as "(#Hhw & #Hinv & #Htext & Hmenv & Htlbinv & Hfile & Hwins)".
    iDestruct "Hwins" as (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17)
      "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17)".
    assert (Hleg_trap :
      WpGprCsrwCommon.legalize_sstatus_val (trap_ms elp_v ms)
        (WpGprCsrwCommon.sstatus_write_val (trap_ms elp_v ms) (mword_of_int 2))
      = trap_ms elp_v ms).
    { apply WpGprCsrwC.legalize_sie_clear_idem.
      - apply trap_ms_SIE.
      - rewrite trap_ms_XS; exact HXS.
      - rewrite trap_ms_FS; exact HFS.
      - rewrite trap_ms_VS; exact HVS.
      - rewrite trap_ms_SD; exact HSD.
      - rewrite trap_ms_MPP; exact HMPP. }
    iApply (wp_kernelvec root_ppn m (trap_ms elp_v ms) mie_v mdv0 menvcfg0 pc0
              w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 E Φ
              HN
              (trap_ms_SIE_false elp_v ms)
              (trap_ms_MPRV_false elp_v ms HMPRV0)
              (trap_ms_SXL_eq elp_v ms HSXL)
              Hmm HPBMTE Hmenvval0
              (trap_ms_MXR_true elp_v ms HMXR)
              Hpmm
              (trap_ms_TSR_false elp_v ms HTSR)
              (sret_newpriv_trap_ms elp_v ms)
              Hlpe0
              HFIOM
              Hleg_trap
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc
                    Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite Hpc0) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl [Hsepc] Hstvec Hpc [-]").
    { iExists pc0. iFrame "Hsepc". }
    iFrame "Hhw Hinv Htext Hmenv Htlbinv Hfile".
    iExists (m !!! Regidx (mword_of_int 1 : mword 5)), (m !!! Regidx (mword_of_int 3 : mword 5)), (m !!! Regidx (mword_of_int 5 : mword 5)), (m !!! Regidx (mword_of_int 6 : mword 5)), (m !!! Regidx (mword_of_int 7 : mword 5)), (m !!! Regidx (mword_of_int 10 : mword 5)), (m !!! Regidx (mword_of_int 11 : mword 5)), (m !!! Regidx (mword_of_int 12 : mword 5)), (m !!! Regidx (mword_of_int 13 : mword 5)), (m !!! Regidx (mword_of_int 14 : mword 5)), (m !!! Regidx (mword_of_int 15 : mword 5)), (m !!! Regidx (mword_of_int 16 : mword 5)), (m !!! Regidx (mword_of_int 17 : mword 5)), (m !!! Regidx (mword_of_int 28 : mword 5)), (m !!! Regidx (mword_of_int 29 : mword 5)), (m !!! Regidx (mword_of_int 30 : mword 5)), (m !!! Regidx (mword_of_int 31 : mword 5)).
    iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
  Qed.

  (* ===================================================================== *)
  (* §  The interrupt-aware single-step WRAPPER.                            *)
  (*                                                                        *)
  (* [wp_step_intr_inv] wraps the point just before an instruction at [pc0] *)
  (* under the interrupt invariant.  Opening [intr_inv F handler] it either *)
  (*   - finds interrupts disabled (SIE=0), so no interrupt can dispatch; or*)
  (*   - finds them enabled and, if an interrupt is pending, TAKES it: traps*)
  (*     to [handler] (a Direct-mode trap vector), runs the abstract handler*)
  (*     spec, returns idempotently to [pc0], re-establishes the invariant, *)
  (*     and loops (Loeb).                                                   *)
  (* Either way it eventually reaches a state with [s_dispatch = None] and   *)
  (* hands the OPENED invariant (mstatus + the SIE disjunction) plus all the *)
  (* register resources to the body, which then runs the instruction in an  *)
  (* interrupt-free context.  The kernelvec-specific 17-slot geometry lives  *)
  (* entirely inside [F] and the persistent handler spec -- this wrapper is  *)
  (* generic over [handler], [pc0] and [F]. *)
  (* ===================================================================== *)

  Lemma s_dispatch_None_of_SIE_false (mip_v : mword 64) (meip seip : mword 1)
      (mie_v mdv0 ms : mword 64) :
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
    s_dispatch mip_v meip seip mie_v mdv0 ms = None.
  Proof. intros H. unfold s_dispatch. rewrite H. reflexivity. Qed.

  Lemma wp_step_intr_inv (handler pc0 : mword 64) (F : iProp Sig)
      (mie_v mdv0 mip_v : mword 64) (meip seip : mword 1)
      E (Φ : mval -> iProp Sig) :
    ↑minstretN ⊆ E ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    sret_tgt pc0 = pc0 ->
    trapVectorMode_forwards (_get_Mtvec_Mode handler) = TV_Direct ->
    stvec_base handler = handler ->
    hw_config -∗
    minstret_inv -∗
    intr_inv F handler -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    mip ↦ᵣ mip_v -∗
    sig_meip ↦ᵣ meip -∗
    sig_seip ↦ᵣ seip -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    F -∗
    pc_is pc0 -∗
    (∀ ms : mword 64,
       ⌜ s_dispatch mip_v meip seip mie_v mdv0 ms = None ⌝ -∗
       mstatus ↦ᵣ ms -∗
       ( (⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗ (∃ v : mword 64, stvec ↦ᵣ v))
         ∨ (⌜ ms_pre_facts ms ⌝ ∗ stvec ↦ᵣ handler ∗ intr_handler_spec handler F) ) -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ Supervisor -∗
       mie ↦ᵣ mie_v -∗
       mideleg ↦ᵣ mdv0 -∗
       mip ↦ᵣ mip_v -∗
       sig_meip ↦ᵣ meip -∗
       sig_seip ↦ᵣ seip -∗
       (∃ v : mword 64, sepc ↦ᵣ v) -∗
       (∃ v : mword 64, scause ↦ᵣ v) -∗
       (∃ v : mword 64, stval ↦ᵣ v) -∗
       F -∗
       pc_is pc0 -∗
       WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmm Hpc0 Htvd Hsb.
    iIntros "#Hhw #Hinv Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iRevert "Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iLöb as "IH".
    iIntros "Hinvr Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip Hsepc Hscause Hstval HF Hpc Hbody".
    iDestruct "Hinvr" as (ms) "[Hms Hdisj]".
    iDestruct "Hdisj" as "[[%HSIEf Hstv] | (%Hmsf & Hstvec & #Hspec)]".
    - (* ---- interrupts disabled: dispatch is necessarily None ---- *)
      iApply ("Hbody" $! ms with "[%] Hms [Hstv] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                                   Hsepc Hscause Hstval HF Hpc").
      { exact (s_dispatch_None_of_SIE_false _ _ _ _ _ _ HSIEf). }
      iLeft. iFrame "Hstv". iPureIntro. exact HSIEf.
    - (* ---- interrupts enabled ---- *)
      destruct (s_dispatch mip_v meip seip mie_v mdv0 ms) as [[i p] |] eqn:Hdres.
      + (* an interrupt fires: trap -> handler spec -> loop *)
        pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
        iPoseProof "Hhw" as "#Hhwc".
        iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
          "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
            %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
        pose proof (elp_no_lp elp0 Help_np) as Help0.
        iDestruct "Hsepc" as (sepc_old) "Hsepc".
        iDestruct "Hscause" as (scause_old) "Hscause".
        iDestruct "Hstval" as (stval_old) "Hstval".
        iDestruct "Hpc" as "[Hpcr Hnpc]".
        iApply (wp_exec_step_interrupt_inv E Φ HN with "Hinv Hhs").
        iIntros (σ) "Hsi".
        iDestruct (dispatch_S_from_regs σ misa0 mip_v mie_v mdv0 ms meip seip
                     HmisaS Hmm
                     with "Hsi Hmisa Hmip Hmeip Hseip Hmie Hmdl Hms") as %Hdisp0.
        rewrite Hdres in Hdisp0.
        iDestruct "Hsi" as "[Hreg Hmem]".
        iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
        iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
        iDestruct (reg_valid with "Hreg Hms") as %Lms.
        iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
        iDestruct (reg_valid with "Hreg Hstvec") as %Lstvec.
        iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
        iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
        assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
          by (rewrite Lmisa; exact HmisaS).
        pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
        pose proof (exec_handle_interrupt_S σ i pc0 ms scause_old handler elp0
                      Lpriv Lms Lsc Lstvec Lelp HmisaS' Htvd Lpc) as Hhi.
        match type of Hhi with _ = Some (_, ?T) => set (s_trap := T) in Hhi end.
        pose (ms_e := update_subrange_vec_dec ms 23 23 elp0).
        pose (c1v := update_subrange_vec_dec scause_old (64 - 1) (64 - 1)
                       (bool_to_bit (trapCause_is_interrupt (Interrupt i)))).
        pose (c2v := update_subrange_vec_dec c1v (64 - 2) 0
                       (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i)))).
        pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
        pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
        pose (ms_c := update_subrange_vec_dec ms_b 8 8 ('b"1")).
        iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
        assert (Hlkelp : register_lookup elp (register_set mstatus ms_e σ.(sregs))
                         = landing_pad_bits_backwards NO_LP_EXPECTED).
        { rewrite irrelevant_register_set; [ rewrite Lelp; exact Help0 | vm_compute; reflexivity ]. }
        iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
        iMod (reg_update _ scause _ c1v with "Hreg Hscause") as "[Hreg Hscause]".
        iMod (reg_update _ scause _ c2v with "Hreg Hscause") as "[Hreg Hscause]".
        iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
        iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
        iMod (reg_update _ mstatus _ ms_c with "Hreg Hms") as "[Hreg Hms]".
        iMod (reg_update _ stval _ (zeros' 64) with "Hreg Hstval") as "[Hreg Hstval]".
        iMod (reg_update _ sepc _ pc0 with "Hreg Hsepc") as "[Hreg Hsepc]".
        iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
        iMod (reg_update _ nextPC _ (stvec_base handler)
                with "Hreg Hnpc") as "[Hreg Hnpc]".
        iModIntro.
        iExists i, Supervisor, s_trap.
        iSplitR; [iPureIntro; exact Hha |].
        iSplitR; [iPureIntro; exact Hhi |].
        assert (LpcT : register_lookup PC s_trap.(sregs) = pc0).
        { unfold s_trap. lk. exact Lpc. }
        rewrite LpcT.
        iSplitL "Hpcr"; [iExact "Hpcr" |].
        iSplitL "Hreg Hmem".
        { unfold s_trap, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
        iNext.
        iIntros "Hhs Hpcr".
        assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base handler).
        { unfold s_trap. lk. reflexivity. }
        iEval (rewrite LnT Hsb) in "Hpcr".
        iEval (rewrite Hsb) in "Hnpc".
        assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
        iEval (rewrite Htm) in "Hms".
        (* ---- the ABSTRACT handler spec discharges the whole handler ---- *)
        iApply ("Hspec" $! elp0 ms pc0 mie_v mdv0 E Φ
                  with "[%] [%] [%] [%] Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec
                        [$Hpcr $Hnpc] HF [Hscause Hstval Hmip Hmeip Hseip Hbody]").
        { exact HN. }
        { exact Hmsf. }
        { exact Hpc0. }
        { exact Hmm. }
        (* the handler's return-continuation: re-establish the invariant + Loeb *)
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hsepc Hstvec Hpc HF".
        iApply ("IH" with "[Hms Hstvec] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                           Hsepc [Hscause] [Hstval] HF Hpc Hbody").
        { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms". iRight.
          iFrame "Hstvec Hspec". iPureIntro. exact (acq_ms_facts_roundtrip elp0 ms Hmsf). }
        { iExists c2v. iFrame "Hscause". }
        { iExists (zeros' 64). iFrame "Hstval". }
      + (* no interrupt pending: hand the opened invariant to the body *)
        iApply ("Hbody" $! ms with "[%] Hms [Hstvec Hspec] Hhs Hpriv Hmie Hmdl Hmip Hmeip Hseip
                                     Hsepc Hscause Hstval HF Hpc").
        { exact Hdres. }
        iRight. iFrame "Hstvec Hspec". iPureIntro. exact Hmsf.
  Qed.

End WpIntrInv.
