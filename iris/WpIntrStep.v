(* WpIntrStep.v -- THE INTERRUPT-SAFETY CAPSTONE.

   [wp_acquire1_intr]: executing acquire's first instruction
   (c.addi sp,-32 = 0x1101 @ 0x80000c04, RVC, 4-aligned) in S-mode with
   INTERRUPTS ENABLED (sstatus.SIE = 1) and stvec -> kernelvec (0x800053e0,
   direct mode).  The machine step either
     - retires the instruction (dispatchInterrupt = None), or
     - takes the pending S-level interrupt: traps to kernelvec, runs the
       COMPLETE handler (wp_kernelvec_hit: 17 saves, kerneltrap, 17
       restores, SRET) and returns to the SAME pc with SIE RE-ENABLED --
       where the theorem applies its own Loeb induction hypothesis.
   The single outcome is therefore "the instruction executed"; the
   precondition is a ROUND-TRIP INVARIANT [acq_frame] re-established by
   every interrupt round trip:
     - mstatus is EXISTENTIAL with the fact set [acq_ms_facts] (SIE=1,
       MPRV=0, SXL=2, MXR=0, TSR=0), preserved by the trap+SRET tower
       (the SIE=1 restoration is WpIntrBits.roundtrip_SIE);
     - sepc / scause / stval and the 17 stack windows are existential
       (the round trip rewrites them);
     - the TLB is in the steady HIT state (slots 5, tlb_hash svpn, and the
       acquire page's slot 0 all hold the identity superpage entry), so the
       handler is the no-fill [wp_kernelvec_hit] and the TLB is invariant.
   Only [kerneltrap_returns] + the model's platform externs are assumed. *)
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
Require Import WpIntrBits WpIntrCore.
(* legalize_sie_clear_idem + have_nom_val: kept QUALIFIED (no Import) so the
   WpGprCsrwCommon/C namespaces don't shadow anything here. *)
Require WpGprCsrwCommon WpGprCsrwC.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrStep.
  Context `{!riscvGS Sig}.
  Context `{!sieG Sig}.
  Context `{CID : CpuId}.

  (* the mstatus fact set carried through the round trip *)
  Definition acq_ms_facts (ms : mword 64) : Prop :=
    eq_vec (_get_Mstatus_SIE ms) ('b"1") = true /\
    eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
    _get_Mstatus_SXL ms = 'b"10" /\
    eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
    eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
    (* ext-state / dirty / MPP well-formedness -- carried so the steady-state
       [wp_kernelvec] can discharge [legalize_sie_clear_idem (trap_ms elp ms)];
       trap_ms/sret_ms5 leave these bits intact (see WpIntrBits roundtrip lemmas). *)
    _get_Mstatus_XS ms = extStatus_map_forwards Off /\
    _get_Mstatus_FS ms = extStatus_map_forwards Off /\
    _get_Mstatus_VS ms = extStatus_map_forwards Off /\
    _get_Mstatus_SD ms = 'b"0" /\
    WpGprCsrwCommon.have_nom_val (_get_Mstatus_MPP ms) = true.

  (* the round trip preserves the fact set (SIE=1 is RESTORED -- the
     headline [roundtrip_SIE]; MPRV is cleared by SRET; SXL/MXR/TSR live in
     untouched bits). *)
  Lemma acq_ms_facts_roundtrip (elp_v : mword 1) (ms : mword 64) :
    acq_ms_facts ms -> acq_ms_facts (sret_ms5 (trap_ms elp_v ms)).
  Proof.
    intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [exact (roundtrip_SIE_true elp_v ms H1) |].
    split; [exact (roundtrip_MPRV_false elp_v ms) |].
    split; [exact (roundtrip_SXL_eq elp_v ms H3) |].
    split; [exact (roundtrip_MXR_true elp_v ms H4) |].
    split; [exact (roundtrip_TSR_false elp_v ms H5) |].
    split; [rewrite roundtrip_XS; exact H6 |].
    split; [rewrite roundtrip_FS; exact H7 |].
    split; [rewrite roundtrip_VS; exact H8 |].
    split; [rewrite roundtrip_SD; exact H9 |].
    rewrite roundtrip_MPP; exact H10.
  Qed.

  (* THE ROUND-TRIP INVARIANT (all resources except pc_is / gpr_file,
     which change across the executed instruction and are threaded
     separately). *)
  Definition acq_frame (root_ppn : mword 44) (m : gmap regidx (mword 64))
      (mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1) : iProp Sig :=
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ Supervisor ∗
     (∃ ms : mword 64, mstatus ↦ᵣ ms ∗ ⌜ acq_ms_facts ms ⌝) ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0 ∗
     mip ↦ᵣ mip_v ∗
     sig_meip ↦ᵣ meip ∗
     sig_seip ↦ᵣ seip ∗
     stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) ∗
     (∃ v : mword 64, sepc ↦ᵣ v) ∗
     (∃ v : mword 64, scause ↦ᵣ v) ∗
     (∃ v : mword 64, stval ↦ᵣ v) ∗
     tlb_inv root_ppn ∗
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

  (* the executed instruction's register-file effect: sp -= 32 *)
  Definition acq_m1 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
    <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 acq_i1)))]> m.

  Lemma wp_acquire1_intr (root_ppn : mword 44)
      (m : gmap regidx (mword 64))
      (mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      
      E (Phi : mval -> iProp Sig) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* PMP: kernelvec text + frame + the acquire pc *)
    (* stack-page geometry *)
    (* SRET *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    kernel_text -∗
    acq_frame root_ppn m mie_v mdv0 menvcfg0 mip_v meip seip -∗
    pc_is acq_pc1 -∗
    gpr_file m -∗
    ( acq_frame root_ppn m mie_v mdv0 menvcfg0 mip_v meip seip -∗
      pc_is (mword_of_int (KernelSyms.acquire + 0x2) : mword 64) -∗
      gpr_file (acq_m1 m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN Hmm HPBMTE Hmenvval0 Hpmm Hlpe0 HFIOM.
    iIntros "#Hhw #Hinv #Htext HP Hpc Hfile Hcont".
    iRevert "HP Hpc Hfile Hcont".
    iLöb as "IH".
    iIntros "HP Hpc Hfile Hcont".
    iDestruct "HP" as "(Hhs & Hpriv & Hmsx & Hmie & Hmdl & Hmenv & Hmip & Hmeip & Hseip
                       & Hstvec & Hsepcx & Hscausex & Hstvalx & Htlbinv & Hwins)".
    iDestruct "Hmsx" as (ms) "[Hms %Hmsf]".
    pose proof Hmsf as Hmsf'. destruct Hmsf' as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hsepcx" as (sepc_old) "Hsepc".
    iDestruct "Hscausex" as (scause_old) "Hscause".
    iDestruct "Hstvalx" as (stval_old) "Hstval".
    iDestruct "Hwins" as (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17)".
    destruct (s_dispatch mip_v meip seip mie_v mdv0 ms) as [[i p] |] eqn:Hdres.
    - (* ---- the interrupt fires: trap -> kernelvec -> SRET -> Löb ---- *)
      pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
      pose proof (elp_no_lp elp0 Help_np) as Help0.
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iApply (wp_exec_step_interrupt_inv E Phi HN with "Hinv Hhs").
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
      assert (Htvd : trapVectorMode_forwards
                       (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct)
        by (vm_compute; reflexivity).
      pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
      pose proof (exec_handle_interrupt_S σ i acq_pc1 ms scause_old
                    (mword_of_int KernelSyms.kernelvec) elp0
                    Lpriv Lms Lsc Lstvec Lelp HmisaS' Htvd Lpc) as Hhi.
      match type of Hhi with _ = Some (_, ?T) => set (s_trap := T) in Hhi end.
      (* thread the trap's writes through the ghost cells, in tower order *)
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
      iMod (reg_update _ sepc _ acq_pc1 with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base (mword_of_int KernelSyms.kernelvec : mword 64))
              with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists i, Supervisor, s_trap.
      iSplitR; [iPureIntro; exact Hha |].
      iSplitR; [iPureIntro; exact Hhi |].
      assert (LpcT : register_lookup PC s_trap.(sregs) = acq_pc1).
      { unfold s_trap. lk. exact Lpc. }
      rewrite LpcT.
      iSplitL "Hpcr"; [iExact "Hpcr" |].
      iSplitL "Hreg Hmem".
      { unfold s_trap, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iNext.
      iIntros "Hhs Hpcr".
      assert (LnT : register_lookup nextPC s_trap.(sregs)
                    = stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)).
      { unfold s_trap. lk. reflexivity. }
      assert (Hsb : stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
                    = (mword_of_int KernelSyms.kernelvec : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite LnT Hsb) in "Hpcr".
      iEval (rewrite Hsb) in "Hnpc".
      assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
      iEval (rewrite Htm) in "Hms".
      assert (Hst : sret_tgt acq_pc1 = acq_pc1) by (apply bv_eq; vm_compute; reflexivity).
      (* clearing SIE on the trap-time mstatus is idempotent under legalization
         (the ext-state/dirty/MPP well-formedness rides in via acq_ms_facts). *)
      assert (Hleg_trap :
        WpGprCsrwCommon.legalize_sstatus_val (trap_ms elp0 ms)
          (WpGprCsrwCommon.sstatus_write_val (trap_ms elp0 ms) (mword_of_int 2))
        = trap_ms elp0 ms).
      { apply WpGprCsrwC.legalize_sie_clear_idem.
        - apply trap_ms_SIE.
        - rewrite trap_ms_XS; exact HXS.
        - rewrite trap_ms_FS; exact HFS.
        - rewrite trap_ms_VS; exact HVS.
        - rewrite trap_ms_SD; exact HSD.
        - rewrite trap_ms_MPP; exact HMPP. }
      (* ---- the whole kernelvec handler (steady-state, TLB hits) ---- *)
      iApply (wp_kernelvec root_ppn m (trap_ms elp0 ms) mie_v mdv0 menvcfg0
                acq_pc1 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 E Phi
                HN
                (trap_ms_SIE_false elp0 ms)
                (trap_ms_MPRV_false elp0 ms HMPRV0)
                (trap_ms_SXL_eq elp0 ms HSXL)
                Hmm HPBMTE Hmenvval0
                (trap_ms_MXR_true elp0 ms HMXR)
                Hpmm
                (trap_ms_TSR_false elp0 ms HTSR)
                (sret_newpriv_trap_ms elp0 ms)
                Hlpe0
                HFIOM
                Hleg_trap
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc
                      [$Hpcr $Hnpc] Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc2 Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
      iEval (rewrite Hst) in "Hpc2".
      (* ---- re-establish the invariant and apply the Löb IH ---- *)
      iApply ("IH" with "[Hhs Hpriv Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hsepc
                          Hscause Hstval Htlbinv Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] Hpc2 Hfile Hcont").
      iFrame "Hhs Hpriv Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Htlbinv".
      iSplitL "Hms".
      { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms".
        iPureIntro. exact (acq_ms_facts_roundtrip elp0 ms Hmsf). }
      iSplitL "Hsepc". { iExists acq_pc1. iFrame "Hsepc". }
      iSplitL "Hscause". { iExists c2v. iFrame "Hscause". }
      iSplitL "Hstval". { iExists (zeros' 64). iFrame "Hstval". }
      iExists (m !!! Regidx (mword_of_int 1 : mword 5)), (m !!! Regidx (mword_of_int 3 : mword 5)), (m !!! Regidx (mword_of_int 5 : mword 5)), (m !!! Regidx (mword_of_int 6 : mword 5)), (m !!! Regidx (mword_of_int 7 : mword 5)), (m !!! Regidx (mword_of_int 10 : mword 5)), (m !!! Regidx (mword_of_int 11 : mword 5)), (m !!! Regidx (mword_of_int 12 : mword 5)), (m !!! Regidx (mword_of_int 13 : mword 5)), (m !!! Regidx (mword_of_int 14 : mword 5)), (m !!! Regidx (mword_of_int 15 : mword 5)), (m !!! Regidx (mword_of_int 16 : mword 5)), (m !!! Regidx (mword_of_int 17 : mword 5)), (m !!! Regidx (mword_of_int 28 : mword 5)), (m !!! Regidx (mword_of_int 29 : mword 5)), (m !!! Regidx (mword_of_int 30 : mword 5)), (m !!! Regidx (mword_of_int 31 : mword 5)).
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    - (* ---- no interrupt: the instruction executes ---- *)
      iApply (wp_acq_caddi_intr root_ppn E Phi m ms mie_v mdv0 menvcfg0 mip_v meip seip
                HN HSXL Hmm Hdres HPBMTE Hmenvval0
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip
                      Htlbinv Hpc Hfile Htext").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Htlbinv Hpc Hfile".
      iApply ("Hcont" with "[Hhs Hpriv Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Hsepc
                             Hscause Hstval Htlbinv Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] Hpc [Hfile]").
      2:{ unfold acq_m1. iExact "Hfile". }
      iFrame "Hhs Hpriv Hmie Hmdl Hmenv Hmip Hmeip Hseip Hstvec Htlbinv".
      iSplitL "Hms".
      { iExists ms. iFrame "Hms". iPureIntro. exact Hmsf. }
      iSplitL "Hsepc". { iExists sepc_old. iFrame "Hsepc". }
      iSplitL "Hscause". { iExists scause_old. iFrame "Hscause". }
      iSplitL "Hstval". { iExists stval_old. iFrame "Hstval". }
      iExists w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
  Qed.

End WpIntrStep.
