(* WpIntrInv.v -- the GENERAL S-mode interrupt invariant and the
   interrupt-absorbing step engine (the tick-aware redesign of the old
   pinned-cell interrupt capstone).

   THE DESIGN.  The SIE ghost variable is CANONICAL per hart --
   [IntrDefs.sie_gname] = [sie_name cpu_id], exactly like [reg_name] /
   [strans_name] -- so nothing in this tier carries a ghost argument: the
   ambient [CpuId] determines the ghost.  It is split into THREE pieces:

     - 1/2 rides with the mstatus cell, tied to the LIVE [mstatus.SIE] bit
       (this is the half [smode_config] bundles; in the interrupts-ENABLED
       regime the client holds it inside [intr_config], the SIE=1 mirror of
       [smode_config]);
     - 1/4 is the KERNEL-CODE token: client code keeps it to reason about
       whether interrupts are currently enabled or disabled (push_off /
       pop_off bookkeeping);
     - 1/4 rides inside [IntrDefs.intr_res], together with the [stvec]
       register and -- keyed on the ghost value being 1 -- a WP for running
       the interrupt handler ([intr_handler_spec], under a [▷]).

   Changing SIE therefore requires ALL THREE pieces (1/2 + 1/4 + 1/4 = 1,
   [sie_ghost_flip]), so interrupts cannot be enabled without the installed
   handler resource in hand.  [intr_res] WAS AN IRIS INVARIANT [intr_inv]
   until 2026-08-11, and the flipping instruction used to open it across its
   own step to borrow the quarter; it is now plain ownership riding inside
   [trap_csrs], and the flip leaves take it as an ordinary resource.  See
   [IntrDefs.v] §5 for why (the short version: an invariant pins the trap
   VECTOR forever, which user mode cannot live with, and the persistence it
   bought was per-hart and therefore useless after a park).

   THE ENGINE.  [wp_exec_step_intr] slots into the clock_inv / minstret_inv
   reduction machinery: it is a Löb loop over the joint step rule
   [wp_exec_step_retire_or_intr] (built on [wp_exec_step_minstret], so the
   clock tick is already absorbed one layer down).  At each step it reads the
   dispatch inputs mip / sig_meip / sig_seip DIRECTLY OFF the machine state σ
   (they live in [clock_inv] / [wire_inv] and can never be pinned by cells --
   a tick may rewrite MTIP/STIP at every step, the PLIC wire step may flip
   sig_seip at any time), and cases on the outcome:

     - PENDING: it takes the interrupt -- reads [stvec] and the handler WP
       out of [intr_res] for the trap step, drives the trap tower
       ([exec_handle_interrupt_S]), runs the handler via that
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
   kernelvec ([wp_kernelvec], ProofKernelvec.v) satisfies the contract;
   [SpecKernelvec.v] is the interface, [LinkKernelvec.v] the instantiation. *)
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
Require Import WpGpr RegFile HartTp.
Require Import SmodeCore.
Require Import MstatusBits WpIntrCore.
Require Export IntrDefs.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrInv.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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
  Lemma wp_exec_step_retire_or_intr {dq : dfrac} :
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
            ▷ WP (Loop : expr riscv_lang)) )
       ∨
       ( (* a pending interrupt is taken (no fetch, no retire, no bump) *)
         ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
           ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
           ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
           PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
           mstate_interp s_trap ∗
           ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
              PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
              WP (Loop : expr riscv_lang)) )) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as "[Hret | Hintr]".
    { rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    - (* ---- retire: verbatim wp_exec_step_hart_active_inv ---- *)
      iDestruct "Hret" as (retval s_exec) "(%Hha & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_exec.
      iDestruct (reg_valid with "Hreg Hmi") as %Hmi_exec.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iDestruct (reg_valid with "Hreg Hmst") as %Lmst_e.
      iMod (reg_update _ PC _ (register_lookup nextPC s_exec.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      assert (Hmst_tick :
        register_lookup minstret
          (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs) = mst).
      { rewrite ?sregs_set_reg.
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
        rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists (add_vec_int mst 1), true. iFrame. }
        iExact "HWP".
      + iModIntro. iExists _. iSplitR.
        { iPureIntro.
          exact (exec_riscv_step_hart_active σ s_exec retval false
                   Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
        iNext.
        iModIntro. rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg.
        iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi".
        { iExists mst, false. iFrame. }
        iExact "HWP".
    - (* ---- interrupt: verbatim wp_exec_step_interrupt_inv ---- *)
      iDestruct "Hintr" as (i p s_trap) "(%Hha & %Hhi & Hpc & [Hreg Hmem] & Hcont)".
      iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
      assert (Hhart_a :
        register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
          = HART_ACTIVE tt).
      { rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
      iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_interrupt σ s_trap i p b
                 Hsi Hhart_a Hha Hhi Hhart_trap). }
      iNext.
      iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
        as "[Hreg Hpc]".
      iModIntro. rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, b. iFrame. }
      iApply ("Hcont" with "Hhs Hpc").
  Qed.

End WpIntrInv.

(* ===================================================================== *)
(* §8 THE ENGINE: run the point just before an instruction at [pc0] with   *)
(* interrupts ENABLED.  Takes an arbitrary number of pending interrupts    *)
(* (Löb induction over the trap + handler round trip), then hands the      *)
(* caller's σ-callback the pure no-pending fact and lets the instruction   *)
(* execute.                                                               *)
(*                                                                        *)
(* IT TAKES THE FOLDED BUNDLE AND ITS CALLBACK IS HART-GENERIC, and those  *)
(* two facts are the same fact.  A trap can park the interrupted thread    *)
(* (kerneltrap yields on a timer tick when this cpu has a current proc),   *)
(* so the instruction after the absorbing loop executes on the hart the    *)
(* LAST trap returned to -- hence the callback sits inside                 *)
(* [WpNext.wp_next true p].  Everything the loop threads is therefore      *)
(* per-hart and has to CROSS rather than be framed: the mstatus cell and   *)
(* its tied SIE half, the trap CSRs, the [sret_bits] travelling half, the  *)
(* per-cpu bookkeeping, the translation slot, the register file.  The one  *)
(* vehicle that crosses is [sie_cap_gpr], which is exactly why the handler *)
(* contract's pre and post are the bundle: THE CONTRACT'S POSTCONDITION IS *)
(* THIS LEMMA'S OWN PRECONDITION, at whatever hart resumed.                *)
(*                                                                        *)
(* OUTSIDE THE SECTION, and it has to be: the Löb is taken over a          *)
(* statement that QUANTIFIES the hart ([iLöb as "IH" forall (CID0)]), so   *)
(* the binder must be dischargeable -- a section variable is not.  That    *)
(* also means every hart-indexed term written fresh in the proof below     *)
(* means [CID0], the hart the loop is currently on, which is what the      *)
(* re-entry at [c'] has to be careful about.                              *)
(*                                                                        *)
(* NO [handler], NO [root_ppn], NO [intr_config]/[intr_frame] PARAMETERS.  *)
(* The installed vector is existential inside [intr_res], the kernel root  *)
(* inside [strans_inv]'s KPT arm, menvcfg and mie inside [sconf]; the      *)
(* engine reads each out per trap.  [intr_config] / [intr_frame] and the   *)
(* funnel's assemble/disassemble dance around them are gone with it.       *)
(* ===================================================================== *)
Lemma wp_exec_step_intr `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID0 : CpuId}
    (pc0 : mword 64) (m : regfile) (av : nat) (p : mword 64) :
  ret_pc pc0 = pc0 ->
  sie_cap_gpr m av true p -∗
  pc_is pc0 -∗
  wp_next true p (fun CID =>
    ∀ σ,
      ⌜ exec (dispatchInterrupt Supervisor) σ = Some (None, σ) ⌝ -∗
      sconf -∗
      sie_cap m av true p -∗
      gpr_file (tp_pin m) -∗
      pc_is pc0 -∗
      mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
      ∃ (retval : mword 32) (s_exec : mstate),
        ⌜ exec (run_hart_active 0) σ
            = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
        PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
        mstate_interp s_exec ∗
        (hart_state ↦ᵣ HART_ACTIVE tt -∗
         PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
         ▷ WP (Loop : expr riscv_lang))) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros Hpc0.
  iIntros "Hcg Hpc Hbody".
  (* the whole state crosses, so the Löb generalises the HART as well as the
     resources: after a trap that parked the thread, the loop re-enters on
     the hart the handler came back on. *)
  iRevert "Hcg Hpc Hbody".
  iLöb as "IH" forall (CID0).
  iIntros "Hcg Hpc Hbody".
  (* ---- open the bundle: this is where [intr_config_of_v2] used to be, and
         the funnel's copy of it is gone with the two [intr_config] lemmas. ---- *)
  iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  (* [Hrcpt] is the enabled arm's KPT RECEIPT (IntrDefs §6b).  The engine
     neither reads nor moves it -- a trap cannot change which table is
     installed -- it just hands it to the handler, which owes the arm back. *)
  iDestruct "Harm" as "(Hq1 & Hires & Hrcpt & Hsepcx & Hscausex & Hstvalx & Hsppc & Hclm & Hcpu)".
  (* Bare ∧ SIE = '1' is impossible: the arm's [intr_res] OWNS stvec and the
     Bare slot owns the same cell.  Two owned cells conflict directly -- this
     used to need an [iInv] under an [fupd_wp] to reach the invariant's copy. *)
  iDestruct "Htr" as "[(Hbit0 & Hbare & Hbstv) | (Hbit1 & Hkpt)]".
  { iEval (rewrite /intr_res) in "Hires".
    iDestruct "Hires" as (h0 vb0) "(_ & _ & _ & Hstv & _)".
    iDestruct "Hbstv" as (v0) "Hbstv".
    iDestruct (reg_pointsto_conflict stvec (DfracOwn 1) with "Hstv Hbstv") as %[]. }
  iDestruct "Hkpt" as (root_ppn) "Htlb".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Htie & %Hmsf)".
  (* THE LIVE SIE BIT IS THE ARM INDEX: the tied half and the arm's eighth
     are fragments of one ghost, so agreement reads it off with no case
     split.  This is the fact [intr_ms_facts] used to carry as a premise. *)
  iDestruct (ghost_var_agree with "Hhalf Hq1") as %HSIE1.
  iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
  subst menvcfg0.
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  pose proof (elp_no_lp elp0 Help_np) as Help0.
  iApply (wp_exec_step_retire_or_intr with "Hminv Hhs").
  iIntros (σ) "Hsi".
  iDestruct (dispatch_S_transient σ misa0 MIE_S mdv0 ms HmisaS Hmm
               with "Hsi Hmisa Hmie Hmdl Hms") as %Hdisp0.
  match type of Hdisp0 with _ = Some (?D, _) =>
    destruct D as [[i pr] |] eqn:Hdres end.
  - (* ---- an interrupt is pending: take it, run the handler, Löb ---- *)
    pose proof (s_dispatch_Some_S _ _ _ _ _ _ _ _ Hdres); subst pr.
    (* open [intr_res] for this step: stvec (read by the trap), the vector's
       two pure facts, the ghost quarter (spent by the flip below), and the
       handler contract.  The contract arrives UNDER ITS LATER -- the [▷] that
       replaced [inv]'s guard, and the fixpoint's -- and the trap step's own
       [iNext] strips it, so the guard is paid for by a step that exists
       anyway. *)
    iEval (rewrite /intr_res) in "Hires".
    iDestruct "Hires" as (handler vb) "(%Htvd & %Hsb & Hq4 & Hstv & #Hsp)".
    iDestruct "Hsepcx" as (sepc_old) "Hsepc".
    iDestruct "Hscausex" as (scause_old) "Hscause".
    iDestruct "Hstvalx" as (stval_old) "Hstval".
    iDestruct "Hsppc" as (vca vcb) "Hsppc".
    iDestruct "Hcpu" as "(Hcells & Hcnt)".
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
    (* the scause word IS [IntrDefs.trap_scause], which is what lets the
       cause layer ([s_cause_ok_of_dispatch]) speak about it -- one spelling
       of the tower, not two kept in step by hand. *)
    assert (Hc2 : c2v = trap_scause scause_old i) by reflexivity.
    pose proof (s_cause_ok_of_dispatch (register_lookup mip σ.(sregs)) mdv0 ms
                  scause_old (register_lookup sig_meip σ.(sregs))
                  (register_lookup sig_seip σ.(sregs)) i Supervisor Hdres) as Hcause.
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
    (* ---- THE GHOST FLIP '1' -> '0', with all four fractions in hand.  This
           is the move the trap makes and the [sret] undoes, and it is why the
           arm has to be OPEN here: the tied half (1/2), the arm's eighth, the
           count's eighth and [intr_res]'s quarter are exactly the four, and
           each of the four goes to a DIFFERENT conjunct of what the handler
           is handed ([sconf], [sie_arm_of _ false], [cpu_hart 0 false],
           [intr_res]). ---- *)
    iEval (rewrite /intr_count) in "Hcnt".
    iMod (sie_ghost_flip_off sie_gname (_get_Mstatus_SIE ms) ('b"1") ('b"1") vb
            with "Hhalf Hq1 Hcnt Hq4") as "(Hhalf & Hq1 & Hcnt & Hq4)".
    (* ---- and the SPP/SPIE mirror MOVES with it, which no SIE flip does:
           the trap writes SPP := 1 and SPIE := old SIE = 1, so BOTH halves
           are updated together -- possible only because the enabled arm was
           holding the travelling one. ---- *)
    iEval (rewrite /sret_tie) in "Htie".
    iMod (sret_bits_update _ _ vca vcb ('b"1" : mword 1) ('b"1" : mword 1)
            with "Htie Hsppc") as "[Htie Hsppc]".
    iModIntro. iRight.
    iExists i, Supervisor, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hhi |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = pc0).
    { unfold s_trap. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem".
    { unfold s_trap; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base handler).
    { unfold s_trap. lk. reflexivity. }
    iEval (rewrite LnT Hsb) in "Hpcr".
    iEval (rewrite Hsb) in "Hnpc".
    assert (Htm : ms_c = trap_ms elp0 ms) by reflexivity.
    iEval (rewrite Htm) in "Hms".
    (* ---- ASSEMBLE THE HANDLER'S ENTRY PACKAGE.  Nothing here is invented:
           every conjunct is a piece the enabled arm was carrying, at the
           value the trap just wrote.  The stack carve is not even touched --
           [trap_res true + av] is the index at both arms. ---- *)
    assert (Htie_eq : sret_tie (trap_ms elp0 ms)
                      = sret_bits ('b"1" : mword 1) ('b"1" : mword 1)).
    { rewrite /sret_tie trap_ms_SPP trap_ms_SPIE HSIE1. reflexivity. }
    iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]" as "Hsc".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf Htie".
      { iExists (trap_ms elp0 ms). iFrame "Hms".
        rewrite Htie_eq. iFrame "Htie".
        rewrite trap_ms_SIE. iFrame "Hhalf".
        iPureIntro. exact (sconf_ms_facts_trap elp0 ms Hmsf). }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
      repeat split; try assumption; reflexivity. }
    iAssert (intr_res) with "[Hq4 Hstv]" as "Hires".
    { iApply (intr_res_intro handler ('b"0" : mword 1) Htvd Hsb with "Hq4 Hstv").
      iNext. iExact "Hsp". }
    iAssert (ihs_entry_of (ires_of ihs) m av p pc0 (trap_scause scause_old i)
               (zeros' 64) handler)
      with "[Hhs Hsc Hstk Hbit1 Htlb Hq1 Hfile Hsppc Hsepc Hscause Hstval
             Hcells Hcnt Hclm Hires Hrcpt Hpcr Hnpc]" as "Hentry".
    { rewrite /ihs_entry_of /sie_cap_gpr_of /sie_cap_of /sie_arm_of.
      rewrite Hc2.
      iFrame "Hhs Hsc Hstk Hfile Hsppc Hsepc Hscause Hstval Hclm Hrcpt".
      iSplitL "Hbit1 Htlb Hq1".
      { iSplitL "Hbit1 Htlb".
        - iApply (strans_inv_intro root_ppn with "Hbit1 Htlb").
        - iExact "Hq1". }
      iSplitL "Hcells Hcnt".
      { rewrite /cpu_hart /intr_count. iFrame "Hcells Hcnt". }
      iSplitL "Hires".
      { iEval (rewrite intr_res_of_eq) in "Hires". iExact "Hires". }
      iFrame "Hpcr Hnpc". }
    (* ---- run the handler, and re-enter the Löb ON THE HART IT RETURNED TO ---- *)
    iApply (intr_handler_spec_apply handler m av p pc0 (trap_scause scause_old i)
              (zeros' 64) Hpc0 Hcause with "Hsp Hentry").
    iIntros (c' Hs').
    rewrite /ihs_post_of. iIntros "Hcg Hpc".
    (* the caller's own obligation is anchored at the hart we STARTED on;
       [wp_next_retarget] moves it, and [Hs'] -- the guard the contract's
       [wp_next] carries -- is exactly its premise.  This is where [wp_next]'s
       second escape hatch pays for itself: at [p = zero_reg] the handler
       promises it came back here. *)
    iDestruct (wp_next_retarget CID0 c' true p _ Hs' with "Hbody") as "Hbody".
    iApply ("IH" $! c' with "Hcg Hpc Hbody").
  - (* ---- nothing pending: the caller's instruction executes ---- *)
    iDestruct (wp_next_at true p _ CID0 (fun _ => eq_refl) with "Hbody") as "Hbody".
    iSpecialize ("Hbody" $! σ with "[%]"); [exact Hdisp0 |].
    iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]" as "Hsc".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf Htie".
      { iExists ms. iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
      repeat split; try assumption; reflexivity. }
    iMod ("Hbody" with "Hsc [Hstk Hbit1 Htlb Hq1 Hires Hrcpt Hsepcx Hscausex Hstvalx Hsppc Hclm Hcpu] Hfile Hpc Hsi")
      as (retval s_exec) "(%Hha & Hpc' & Hsi' & Hcont)".
    { rewrite /sie_cap /sie_arm. iFrame "Hstk".
      iSplitL "Hbit1 Htlb".
      { iApply (strans_inv_intro root_ppn with "Hbit1 Htlb"). }
      iFrame "Hq1 Hires Hrcpt Hsepcx Hscausex Hstvalx Hsppc Hclm Hcpu". }
    iModIntro. iLeft.
    iExists retval, s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    iFrame "Hpc' Hsi'". iExact "Hcont".
Qed.
