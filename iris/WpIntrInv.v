(* WpIntrInv.v -- the GENERAL S-mode interrupt invariant and the
   interrupt-absorbing step engine (the tick-aware redesign of the old
   pinned-cell interrupt capstone).

   THE DESIGN.  The SIE ghost variable [γ] (the same [γ] that is the argument
   of [smode_config]) is split into THREE pieces:

     - 1/2 rides with the mstatus cell, tied to the LIVE [mstatus.SIE] bit
       (this is the half [smode_config] bundles; in the interrupts-ENABLED
       regime the client holds it inside [intr_config], the SIE=1 mirror of
       [smode_config]);
     - 1/4 is the KERNEL-CODE token: client code keeps it to reason about
       whether interrupts are currently enabled or disabled (push_off /
       pop_off bookkeeping);
     - 1/4 lives in the interrupt INVARIANT [intr_inv] below, together with
       the [stvec] register and -- keyed on the ghost value being 1 -- a
       persistent WP for running the interrupt handler ([intr_handler_spec]).

   Changing SIE therefore requires ALL THREE pieces (1/2 + 1/4 + 1/4 = 1,
   [sie_ghost_flip]); the flipping instruction opens [intr_inv] across its
   own step to borrow the invariant quarter.

   THE ENGINE.  [wp_exec_step_intr] slots into the clock_inv / minstret_inv
   reduction machinery: it is a Löb loop over the joint step rule
   [wp_exec_step_retire_or_intr] (built on [wp_exec_step_minstret], so the
   clock tick is already absorbed one layer down).  At each step it reads the
   dispatch inputs mip / sig_meip / sig_seip DIRECTLY OFF the machine state σ
   (they live in [clock_inv] / [wire_inv] and can never be pinned by cells --
   a tick may rewrite MTIP/STIP at every step, the PLIC wire step may flip
   sig_seip at any time), and cases on the outcome:

     - PENDING: it takes the interrupt -- borrows [stvec] and the handler WP
       from [intr_inv] for the trap step, drives the trap tower
       ([exec_handle_interrupt_S]), runs the handler via the invariant's
       [intr_handler_spec] (which returns idempotently to the interrupted
       pc with SIE re-enabled and the frame [intr_frame] intact), and re-enters
       itself by Löb induction -- so an ARBITRARY number of back-to-back
       interrupts is absorbed;
     - NONE: it hands the caller's σ-callback the PURE fact
       [exec (dispatchInterrupt Supervisor) σ = Some (None, σ)] -- no
       interrupt needs to be taken -- so the higher-level per-instruction
       logic runs the instruction WITHOUT owning mip or the wire pins, and
       without fupd-style specs passing an interrupt-pending cell around.

   The per-trap frame is the CONCRETE [intr_frame]: [stack_own] of depth AT
   LEAST [kv_frame_slots] below the interrupted sp -- the kernel must
   maintain that much free stack at every interrupts-enabled instruction --
   plus menvcfg and tlb_inv_pt.  [kernelvec_handler_spec] proves the real
   kernelvec ([wp_kernelvec], WpKernelvecNew.v) satisfies the contract. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr RegFile.
Require Import SmodeCore WpSmodeSret.
Require Import WpIntrBits WpIntrCore.
Require Export IntrDefs.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrInv.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* §6 The dispatch outcome read straight off σ.  mip lives in            *)
  (* [clock_inv] and the wire pins in [wire_inv], so no cell can name      *)
  (* their values; but [dispatchInterrupt] is a FUNCTION of σ, so the      *)
  (* outcome is [s_dispatch] of σ's OWN lookups -- no ownership needed     *)
  (* beyond the client's misa/mie/mideleg/mstatus pins.                    *)
  (* =================================================================== *)
  Lemma dispatch_S_transient (σ : mstate) (misa0 mie_v mdv0 ms : mword 64)
      {dqm dqi dqd dqs : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    mstate_interp σ -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv0 -∗
    mstatus ↦ᵣ{ dqs } ms -∗
    ⌜ exec (dispatchInterrupt Supervisor) σ
        = Some (s_dispatch (register_lookup mip σ.(sregs))
                           (register_lookup sig_meip σ.(sregs))
                           (register_lookup sig_seip σ.(sregs))
                           mie_v mdv0 ms, σ) ⌝.
  Proof.
    iIntros (HmisaS Hmm) "[Hreg Hmem] Hmisa Hmie Hmdl Hms".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iPureIntro.
    apply exec_dispatchInterrupt_S_reduce;
      [ | reflexivity | reflexivity | reflexivity
        | exact Lmie | exact Lmdl | exact Lms | exact Hmm ].
    rewrite exec_currentlyEnabled_S Lmisa HmisaS. reflexivity.
  Qed.

  (* =================================================================== *)
  (* §7 The joint step rule: ONE machine step that either RETIRES an       *)
  (* instruction or TAKES a pending interrupt -- the σ-callback chooses    *)
  (* the branch AFTER seeing σ (the dispatch inputs are functions of σ,    *)
  (* unknowable outside the step).  Merge of [wp_exec_step_hart_active_inv]*)
  (* (MinstretInv.v) and [wp_exec_step_interrupt_inv] (WpIntrCore.v),      *)
  (* directly over [wp_exec_step_minstret]: retire bumps minstret, an      *)
  (* interrupt does not; both continuations come back under the step's ▷.  *)
  (* =================================================================== *)
  Lemma wp_exec_step_retire_or_intr Φ {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ( (* the instruction retires *)
         ∃ (retval : mword 32) (s_exec : mstate),
           ⌜ exec (run_hart_active 0) σ
               = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
           PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
           mstate_interp s_exec ∗
           (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
            ▷ WP (Loop : expr riscv_lang) {{ Φ }}) )
       ∨
       ( (* a pending interrupt is taken (no fetch, no retire, no bump) *)
         ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
           ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
           ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
           PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
           mstate_interp s_trap ∗
           ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
              PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
              WP (Loop : expr riscv_lang) {{ Φ }}) )) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) Φ with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as "[Hret | Hintr]".
    { rewrite /mstate_interp. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    - (* ---- retire: verbatim wp_exec_step_hart_active_inv continuation ---- *)
      iDestruct "Hret" as (retval s_exec) "(%Hha & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_exec.
      iDestruct (reg_valid with "Hreg Hmi") as %Hmi_exec.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iDestruct (reg_valid with "Hreg Hmst") as %Lmst_e.
      iMod (reg_update _ PC _ (register_lookup nextPC s_exec.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      assert (Hmst_tick :
        register_lookup minstret
          (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs) = mst).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lmst_e | reflexivity]. }
      iDestruct ("Hcont" with "Hhs Hpc") as "HWP".
      destruct b.
      + iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
          as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR.
        { iPureIntro.
          exact (exec_riscv_step_hart_active σ s_exec retval true
                   Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
        iNext.
        iModIntro. rewrite /mstate_interp. cbn [sregs mem]. rewrite Hmst_tick.
        unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists (add_vec_int mst 1), true. iFrame. }
        iExact "HWP".
      + iModIntro. iExists _. iSplitR.
        { iPureIntro.
          exact (exec_riscv_step_hart_active σ s_exec retval false
                   Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
        iNext.
        iModIntro. rewrite /mstate_interp. unfold set_reg; cbn [sregs mem].
        iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists mst, false. iFrame. }
        iExact "HWP".
    - (* ---- interrupt: verbatim wp_exec_step_interrupt_inv continuation ---- *)
      iDestruct "Hintr" as (i p s_trap) "(%Hha & %Hhi & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_interrupt σ s_trap i p b
                 Hsi Hhart_a Hha Hhi Hhart_trap). }
      iNext.
      iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, b. iFrame. }
      iApply ("Hcont" with "Hhs Hpc").
  Qed.

  (* =================================================================== *)
  (* §8 THE ENGINE: run the point just before an instruction at [pc0]     *)
  (* with interrupts ENABLED, under the interrupt invariant.  Takes an    *)
  (* arbitrary number of pending interrupts (Löb induction over the       *)
  (* trap + handler round trip), then hands the caller's σ-callback the   *)
  (* pure no-pending fact and lets the instruction execute.  Every        *)
  (* threaded resource comes back to the callback UNCHANGED; the          *)
  (* callback's obligation is [wp_exec_step_hart_active_inv]'s.           *)
  (* =================================================================== *)
  Lemma wp_exec_step_intr (γ : gname) (handler pc0 : mword 64)
      (root_ppn : mword 44) (menvcfg0 : mword 64)
      (m : regfile)
      (Φ : mval -> iProp Σ) :
    sret_tgt pc0 = pc0 ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc0 -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    (∀ σ,
       ⌜ exec (dispatchInterrupt Supervisor) σ = Some (None, σ) ⌝ -∗
       intr_config γ -∗
       pc_is pc0 -∗
       gpr_file m -∗
       intr_frame root_ppn menvcfg0 m -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (retval : mword 32) (s_exec : mstate),
         ⌜ exec (run_hart_active 0) σ
             = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hpc0.
    iIntros "#Hintr Hhs Hcfg Hpc Hfile HF Hbody".
    iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
    iRevert "Hhs Hcfg Hpc Hfile HF Hbody".
    iLöb as "IH".
    iIntros "Hhs Hcfg Hpc Hfile HF Hbody".
    iDestruct "Hcfg" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hsepcx & Hscausex & Hstvalx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hsie & %Hmsf)".
    iDestruct "Hmiex" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iApply (wp_exec_step_retire_or_intr Φ with "Hminv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (dispatch_S_transient σ misa0 mie_v mdv0 ms HmisaS Hmm
                 with "Hsi Hmisa Hmie Hmdl Hms") as %Hdisp0.
    match type of Hdisp0 with _ = Some (?D, _) =>
      destruct D as [[i p] |] eqn:Hdres end.
    - (* ---- an interrupt is pending: take it, run the handler, Löb ---- *)
      pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst p.
      (* the destruct folded [Hdres] into [Hdisp0]:
         Hdisp0 : exec (dispatchInterrupt Supervisor) σ = Some (Some (i, Supervisor), σ) *)
      (* borrow the invariant for this step: stvec (read by the trap), the
         invariant quarter (agreement pins b = SIE ms = 1), the handler WP *)
      iInv "Hinv_i" as (b) "(>Hq & >Hstv & #Hspec)" "Hclose".
      iDestruct (ghost_var_agree with "Hsie Hq") as %Hbv.
      assert (Hb1 : b = ('b"1" : mword 1)).
      { rewrite <- Hbv. apply eq_vec_true_iff. exact HSIE1. }
      iDestruct "Hsepcx" as (sepc_old) "Hsepc".
      iDestruct "Hscausex" as (scause_old) "Hscause".
      iDestruct "Hstvalx" as (stval_old) "Hstval".
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iDestruct "Hsi" as "[Hreg Hmem]".
      iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
      iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
      iDestruct (reg_valid with "Hreg Hms") as %Lms.
      iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
      iDestruct (reg_valid with "Hreg Hstv") as %Lstvec.
      iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
      iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
      assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaS).
      pose proof (exec_run_hart_active_pending σ i Supervisor Lpriv Hdisp0) as Hha.
      pose proof (exec_handle_interrupt_S σ i pc0 ms scause_old handler elp0
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
      iMod (reg_update _ sepc _ pc0 with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base handler) with "Hreg Hnpc") as "[Hreg Hnpc]".
      (* re-seal the invariant (same ghost value; the spec is persistent) *)
      iMod ("Hclose" with "[Hq Hstv]") as "_".
      { iNext. iExists b. iFrame "Hq Hstv". iExact "Hspec". }
      iModIntro. iRight.
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
      (* ---- the invariant's handler WP discharges the whole handler ---- *)
      iAssert (intr_handler_spec handler root_ppn menvcfg0) with "[]" as "#Hsp".
      { iApply "Hspec". iPureIntro. exact Hb1. }
      iApply ("Hsp" $! elp0 ms pc0 mie_v mdv0 m Φ
                with "[%] [%] [%] Hhs Hpriv Hms Hmie Hmdl Hsepc [$Hpcr $Hnpc] Hfile HF").
      { exact Hmsf. }
      { exact Hpc0. }
      { exact Hmm. }
      (* the handler's return continuation: re-establish the frame + Löb *)
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hsepcx Hpc Hfile HF".
      assert (Hs1 : _get_Mstatus_SIE (sret_ms5 (trap_ms elp0 ms)) = ('b"1" : mword 1))
        by (apply eq_vec_true_iff; exact (roundtrip_SIE_true elp0 ms HSIE1)).
      assert (Hs2 : _get_Mstatus_SIE ms = ('b"1" : mword 1))
        by (apply eq_vec_true_iff; exact HSIE1).
      iEval (rewrite Hs2 -Hs1) in "Hsie".
      iApply ("IH" with "Hhs [Hpriv Hms Hsie Hmie Hmdl Hsepcx Hscause Hstval] Hpc Hfile HF Hbody").
      iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hsie".
      { iExists (sret_ms5 (trap_ms elp0 ms)). iFrame "Hms Hsie".
        iPureIntro. exact (intr_ms_facts_roundtrip elp0 ms Hmsf). }
      iSplitL "Hmie Hmdl".
      { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iFrame "Hsepcx".
      iSplitL "Hscause". { iExists c2v. iFrame "Hscause". }
      iExists (zeros' 64). iFrame "Hstval".
    - (* ---- nothing pending: the caller's instruction executes ----
         (the destruct folded [Hdres] into [Hdisp0]:
          Hdisp0 : exec (dispatchInterrupt Supervisor) σ = Some (None, σ)) *)
      iSpecialize ("Hbody" $! σ with "[%]"); [exact Hdisp0 |].
      iMod ("Hbody" with "[Hpriv Hms Hsie Hmie Hmdl Hsepcx Hscausex Hstvalx] Hpc Hfile HF Hsi")
        as (retval s_exec) "(%Hha & Hpc' & Hsi' & Hcont)".
      { iFrame "Hhw Hminv Hpriv".
        iSplitL "Hms Hsie".
        { iExists ms. iFrame "Hms Hsie". iPureIntro. exact Hmsf. }
        iSplitL "Hmie Hmdl".
        { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
        iFrame "Hsepcx Hscausex Hstvalx". }
      iModIntro. iLeft.
      iExists retval, s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      iFrame "Hpc' Hsi'". iExact "Hcont".
  Qed.

End WpIntrInv.
