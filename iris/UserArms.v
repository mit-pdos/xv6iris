(* UserArms.v -- the payload-form RETIRE and EXECUTE-TRAP arms of the user
   step classification.

   [UserStepFull.v]'s unified step wrapper opens the wire invariant, decides
   the dispatch, and -- when no interrupt is pending -- hands the whole step
   to the classification [active_class], which must produce the
   [wp_exec_step_minstret] payload: ONE [riscv_step] reduction plus the
   re-established interp.  The classification's per-family case analysis
   always ends in one of a small set of STEP SHAPES; this file provides
   them:

     [retire_branch]        run_hart_active retires ([Retire_Success]) --
                            compute, control flow, fences, nops.  The
                            classification discharges the abstract
                            [retire_obligation] (UserCompute.v) for the
                            family; this arm does the try_step bookkeeping
                            (tick + conditional minstret bump) and
                            re-establishes [user_inv].
     [execute_trap_branch]  run_hart_active returns an execute-produced
                            sync trap (ecall / ebreak / illegal / memory
                            page fault) -- the arm runs the delegated trap
                            tower to stvec and produces [user_trap_frame].
                            The classification discharges
                            [execute_trap_obligation] (below).
     [fetch_fault_branch]   run_hart_active returns a FAILED FETCH
                            (misaligned / non-canonical / unmapped /
                            denied / needs-update pc) -- same tower, same
                            frame; the fetch never reaches execute, so the
                            gpr file and nextPC are untouched and stay with
                            the arm ([fetch_fault_obligation] hands over
                            only interp + [upt_inv], the TLB may fill on a
                            partially-successful split fetch).
     [illegal_branch]       run_hart_active returns [Illegal_Instruction]
                            (every privileged instruction at User --
                            mret / sret / wfi / the sfence and sinval
                            families; see UserExecFacts.v): try_step's
                            dedicated arm delivers E_Illegal_Instr with
                            the INSTRUCTION BITS as tval; the gpr file is
                            untouched, but nextPC moved (the pre-execute
                            write), so [illegal_obligation] hands it over.

     [enter_wait_branch]    run_hart_active returns [Enter_Wait] (a user
                            WRS): hart_state := WAITING, NO pc tick, NO
                            bump -- PC stays at the WRS, nextPC after it
                            (the decoupled WAITING shape [user_inv]
                            binds); re-enters [user_inv].

   All arms are WIRE-FREE: the dispatch decision reaches them as a pure
   fact at the post-minstret-increment states (∀ over the written bit), so
   no arm ever owns the wire cells.  Each does its own minstret prelude
   (the write is the first thing [try_step] does, so it belongs to the
   step shape, not to the classification).  The step-shape arm set is
   COMPLETE: retire / interrupt (inlined in the wrapper) / execute-trap /
   fetch-fault / illegal / enter-wait.                                     *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpLeafCommon WpIntrBits WpIntrCore.
Require Import UserPt UserExec UserStep UserTrap UserCompute.
Local Open Scope Z_scope.
Import Defs.

Section UserArms.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  (* ------------------------------------------------------------------- *)
  (* The RETIRE arm.  The caller supplies the per-family                   *)
  (* [retire_obligation] at the post-increment state (∀ over the written   *)
  (* bit -- the reductions never read minstret_increment, so the           *)
  (* classification discharges it uniformly); the arm does the minstret    *)
  (* prelude, runs the obligation, ticks PC to the retired pc, bumps       *)
  (* minstret when due, and re-enters [user_inv].                          *)
  (* ------------------------------------------------------------------- *)
  Lemma retire_branch (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64)) (mst : mword 64) (mi : bool) :
    user_mstatus_ok ms_v ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup PC σ.(sregs) = va ->
    (forall b : bool,
       exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
         = Some (None, set_reg σ (R_bool minstret_increment) b)) ->
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    (∀ b : bool,
       retire_obligation C pt Ei (set_reg σ (R_bool minstret_increment) b) va g) -∗
    ▷ (user_inv C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude: minstret_increment := should_inc *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (T hart_state _ Lhs0 eq_refl).
    assert (HprivA : register_lookup cur_privilege s_a.(sregs) = User)
      by exact (T cur_privilege _ Lpriv eq_refl).
    assert (HpcA : register_lookup PC s_a.(sregs) = va)
      by exact (T PC _ Lpc eq_refl).
    assert (HmsokA : user_mstatus_ok (register_lookup mstatus s_a.(sregs))).
    { rewrite (T mstatus _ Lms eq_refl). exact Hmsok. }
    (* the per-family obligation, at the post-increment state *)
    iMod ("Hob" $! b (Hdisp b) HprivA HpcA HmsokA
            with "[Hreg Hmd] Hgpr Hnpc Hupt Hcfg")
      as (ib s_x g' va')
         "(%Hha & %Hhart_x & %Hmi_x & %Lnpc_x & [Hreg Hmd] & Hgpr & Hnpc & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* the whole-step reduction: try_step epilogue (tick + conditional bump) *)
    assert (Hmi_x' : register_lookup (R_bool minstret_increment) s_x.(sregs) = b).
    { rewrite Hmi_x. unfold s_a, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    pose proof (exec_riscv_step_hart_active σ s_x ib b
                  Hsi Hhart_a Hha Hhart_x Hmi_x') as Hstep.
    rewrite Lnpc_x in Hstep.
    set (s_tick := set_reg s_x PC va') in *.
    iDestruct (reg_valid_dq with "Hreg Hmst") as %Lmst_x.
    assert (Lmst_t : register_lookup minstret s_tick.(sregs) = mst).
    { unfold s_tick, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmst_x | reflexivity]. }
    rewrite Lmst_t in Hstep.
    (* GHOST: tick PC := va', then the conditional bump *)
    iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. iExists (set_reg s_tick minstret (add_vec_int mst 1)).
      iSplitR. { iPureIntro. exact Hstep. }
      iNext.
      unfold s_tick, set_reg; cbn [sregs mem mdev].
      iFrame "Hreg Hmd".
      iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
      iApply ("Hcont" with "[-]").
      iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va', va', g'.
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
      iPureIntro. split; [exact Hmsok | intros u _; reflexivity].
    - iModIntro. iExists s_tick.
      iSplitR. { iPureIntro. exact Hstep. }
      iNext.
      unfold s_tick, set_reg; cbn [sregs mem mdev].
      iFrame "Hreg Hmd".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "[-]").
      iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va', va', g'.
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
      iPureIntro. split; [exact Hmsok | intros u _; reflexivity].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The EXECUTE-TRAP obligation: the per-family fact the classification   *)
  (* discharges when execute produces a synchronous trap (ecall / ebreak / *)
  (* illegal / memory page fault).  Same ownership discipline as            *)
  (* [retire_obligation]: it owns what fetch+execute mutate (interp, gpr    *)
  (* file, nextPC, [upt_inv]; [user_cfg] borrowed for the decode reads)     *)
  (* and returns them at the post-execute state [s_x], with the run         *)
  (* reduction ending in [Trap] at User with a DELEGATED user exception.    *)
  (* The post-execute nextPC [va'] is whatever execute left there (the      *)
  (* trap tower overwrites it with the handler base).                       *)
  (* ------------------------------------------------------------------- *)
  Definition execute_trap_obligation (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (⌜exec (dispatchInterrupt User) σ = Some (None, σ)⌝ -∗
     ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
     ⌜register_lookup PC σ.(sregs) = va⌝ -∗
     ⌜user_mstatus_ok (register_lookup mstatus σ.(sregs))⌝ -∗
     mstate_interp σ -∗
     gpr_file g -∗
     nextPC ↦ᵣ va -∗
     upt_inv pt -∗
     user_cfg C -∗
     |={E}=>
       ∃ (ib : mword 32) (s_x : mstate) (g' : gmap regidx (mword 64))
         (e : ExceptionType) (xv pcx va' : mword 64),
         ⌜exec (run_hart_active 0) σ
            = Some (Step_Execute
                      (rv64d_types.Trap (User, make_sync_exception e xv, pcx), ib),
                    s_x)⌝ ∗
         ⌜user_exc e = true⌝ ∗
         ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
            = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
         ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
         mstate_interp s_x ∗
         gpr_file g' ∗
         nextPC ↦ᵣ va' ∗
         upt_inv pt ∗
         user_cfg C)%I.

  (* ------------------------------------------------------------------- *)
  (* The EXECUTE-TRAP arm: run the delegated trap tower at the             *)
  (* post-execute state, tick PC to the handler base (no minstret bump --  *)
  (* the step does not retire), and produce [user_trap_frame].             *)
  (* ------------------------------------------------------------------- *)
  Lemma execute_trap_branch (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64)) (mst : mword 64) (mi : bool) :
    user_mstatus_ok ms_v ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup PC σ.(sregs) = va ->
    (forall b : bool,
       exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
         = Some (None, set_reg σ (R_bool minstret_increment) b)) ->
    hw_config -∗
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    (∀ b : bool,
       execute_trap_obligation Ei (set_reg σ (R_bool minstret_increment) b) va g) -∗
    ▷ (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "#Hhw [Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (T hart_state _ Lhs0 eq_refl).
    assert (HprivA : register_lookup cur_privilege s_a.(sregs) = User)
      by exact (T cur_privilege _ Lpriv eq_refl).
    assert (HpcA : register_lookup PC s_a.(sregs) = va)
      by exact (T PC _ Lpc eq_refl).
    assert (HmsokA : user_mstatus_ok (register_lookup mstatus s_a.(sregs))).
    { rewrite (T mstatus _ Lms eq_refl). exact Hmsok. }
    (* the per-family obligation, at the post-increment state *)
    iMod ("Hob" $! b (Hdisp b) HprivA HpcA HmsokA
            with "[Hreg Hmd] Hgpr Hnpc Hupt Hcfg")
      as (ib s_x g' e xv pcx va')
         "(%Hha & %He & %Hhart_x & %Hmi_x & %Lnpc_x & [Hreg Hmd] & Hgpr & Hnpc & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* read everything the trap tower needs at the post-execute state s_x *)
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv_x.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms_x.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc_x.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa_x.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp_x.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec_x.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl_x.
    assert (HmisaS_x : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_x; exact HmisaS).
    assert (Hdel_x : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards e))) = true)
      by (rewrite Lmedl_x; exact (uc_del C e He)).
    (* the trap tower at s_x, then set_next_pc *)
    pose proof (exec_exception_handler_U s_x (rv64d_types.Exception e)
                  (xtval_exception_value e xv) pcx ms_v sc_v (uc_stvec C) elp0
                  Lpriv_x Lms_x Lsc_x Lstvec_x Lelp_x HmisaS_x (uc_tvd C)
                  e xv eq_refl eq_refl Hdel_x) as Heh.
    set (s9x := set_reg _ cur_privilege Supervisor) in Heh.
    set (s_trap := set_reg s9x nextPC (stvec_base (uc_stvec C))).
    assert (Hxh : exec (Defs.bind
                    (exception_handler User (make_sync_exception e xv) pcx)
                    set_next_pc) s_x
                  = Some (tt, s_trap)).
    { rewrite (exec_bind_Some _ _ _ _ _ Heh). unfold s_trap. apply exec_set_next_pc. }
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, s9x, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Hhart_x. }
    (* the whole-step reduction: tick PC := nextPC = handler base, NO bump *)
    assert (Hstep : exec (riscv_step false) σ
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_execute_trap;
        [ exact Hsi | exact Hhart_a | exact Hha | exact Hxh | exact Lhs_trap ]. }
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
    { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    (* GHOST: mirror every physical write of the tower in order *)
    pose (ms_e := update_subrange_vec_dec ms_v 23 23 elp0).
    pose (c1 := update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                  (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception e)))).
    pose (c2 := update_subrange_vec_dec c1 (64 - 2) 0
                  (zero_extend' (64 - 1)
                     (trapCause_bits_forwards (rv64d_types.Exception e)))).
    pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
    pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
    iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp_x Help0. reflexivity. }
    iMod (reg_update _ scause _ c1 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ c2 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_b 8 8 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval (xtval_exception_value e xv))
            with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ pcx with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base (uc_stvec C)) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    unfold s_trap, s9x, set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    assert (Hmc : update_subrange_vec_dec ms_b 8 8 ('b"0") = utrap_ms elp0 ms_v)
      by (unfold utrap_ms, ms_b, ms_a, ms_e; reflexivity).
    iExists (update_subrange_vec_dec ms_b 8 8 ('b"0")), c2,
            (tval (xtval_exception_value e xv)), pcx, g'.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hupt".
    iSplitR.
    { iPureIntro. rewrite Hmc.
      destruct Hmsok as (HSXL & HMPRV & HMXR).
      split; [ rewrite utrap_ms_SXL; exact HSXL | ].
      split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
      split; [ rewrite utrap_ms_MXR; exact HMXR | ].
      split; [ rewrite utrap_ms_SPP; reflexivity | ].
      rewrite utrap_ms_SIE; reflexivity. }
    iSplitL "Hpc Hnpc". { iFrame "Hpc Hnpc". }
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The FETCH-FAULT obligation: the fetch fails before reaching execute   *)
  (* (misaligned / non-canonical / unmapped / denied / needs-update pc),   *)
  (* with a DELEGATED user exception.  The fetch writes neither the gpr    *)
  (* file nor nextPC, so only the interp (a split fetch may fill the TLB   *)
  (* on its successful half) and [upt_inv] change hands; [user_cfg] is     *)
  (* borrowed for the reads.  The ADUE-sensitive flavor corollaries        *)
  (* (UserFetch.v) are what discharge this; the arm below is cause-generic.*)
  (* ------------------------------------------------------------------- *)
  Definition fetch_fault_obligation (E : coPset) (σ : mstate) (va : mword 64)
      : iProp Σ :=
    (⌜exec (dispatchInterrupt User) σ = Some (None, σ)⌝ -∗
     ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
     ⌜register_lookup PC σ.(sregs) = va⌝ -∗
     ⌜user_mstatus_ok (register_lookup mstatus σ.(sregs))⌝ -∗
     mstate_interp σ -∗
     upt_inv pt -∗
     user_cfg C -∗
     |={E}=>
       ∃ (s_f : mstate) (e : ExceptionType) (xv : mword 64),
         ⌜exec (run_hart_active 0) σ
            = Some (Step_Fetch_Failure (Virtaddr xv, e), s_f)⌝ ∗
         ⌜user_exc e = true⌝ ∗
         ⌜register_lookup hart_state s_f.(sregs) = HART_ACTIVE tt⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) s_f.(sregs)
            = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
         mstate_interp s_f ∗
         upt_inv pt ∗
         user_cfg C)%I.

  (* ------------------------------------------------------------------- *)
  (* The FETCH-FAULT arm: [handle_exception] runs the same delegated trap  *)
  (* tower at the post-fetch state (sepc := the faulting pc, read from     *)
  (* PC; stval := the faulting address), PC ticks to the handler base, no  *)
  (* minstret bump -- and the machine is [user_trap_frame].                *)
  (* ------------------------------------------------------------------- *)
  Lemma fetch_fault_branch (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64)) (mst : mword 64) (mi : bool) :
    user_mstatus_ok ms_v ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup PC σ.(sregs) = va ->
    (forall b : bool,
       exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
         = Some (None, set_reg σ (R_bool minstret_increment) b)) ->
    hw_config -∗
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    (∀ b : bool,
       fetch_fault_obligation Ei (set_reg σ (R_bool minstret_increment) b) va) -∗
    ▷ (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "#Hhw [Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (T hart_state _ Lhs0 eq_refl).
    assert (HprivA : register_lookup cur_privilege s_a.(sregs) = User)
      by exact (T cur_privilege _ Lpriv eq_refl).
    assert (HpcA : register_lookup PC s_a.(sregs) = va)
      by exact (T PC _ Lpc eq_refl).
    assert (HmsokA : user_mstatus_ok (register_lookup mstatus s_a.(sregs))).
    { rewrite (T mstatus _ Lms eq_refl). exact Hmsok. }
    (* the per-flavor obligation, at the post-increment state *)
    iMod ("Hob" $! b (Hdisp b) HprivA HpcA HmsokA
            with "[Hreg Hmd] Hupt Hcfg")
      as (s_f e xv)
         "(%Hha & %He & %Hhart_f & %Hmi_f & [Hreg Hmd] & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* read everything the trap tower needs at the post-fetch state s_f *)
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv_f.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms_f.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc_f.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa_f.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp_f.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc_f.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec_f.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl_f.
    assert (HmisaS_f : eq_vec (_get_Misa_S (register_lookup misa s_f.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_f; exact HmisaS).
    assert (Hdel_f : bit_to_bool (access_vec_dec (register_lookup medeleg s_f.(sregs))
                       (uint (exceptionType_bits_forwards e))) = true)
      by (rewrite Lmedl_f; exact (uc_del C e He)).
    (* the trap tower at s_f: handle_exception reads PC (= va) into sepc *)
    pose proof (exec_handle_exception_U s_f (rv64d_types.Exception e)
                  (xtval_exception_value e xv) va ms_v sc_v (uc_stvec C) elp0
                  Lpriv_f Lms_f Lsc_f Lstvec_f Lelp_f HmisaS_f (uc_tvd C) Lpc_f
                  e xv eq_refl eq_refl Hdel_f) as Hhe.
    set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhe.
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Hhart_f. }
    (* the whole-step reduction: tick PC := nextPC = handler base, NO bump *)
    assert (Hstep : exec (riscv_step false) σ
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_fetch_failure;
        [ exact Hsi | exact Hhart_a | exact Hha | exact Hhe | exact Lhs_trap ]. }
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
    { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    (* GHOST: mirror every physical write of the tower in order *)
    pose (ms_e := update_subrange_vec_dec ms_v 23 23 elp0).
    pose (c1 := update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                  (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception e)))).
    pose (c2 := update_subrange_vec_dec c1 (64 - 2) 0
                  (zero_extend' (64 - 1)
                     (trapCause_bits_forwards (rv64d_types.Exception e)))).
    pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
    pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
    iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp_f Help0. reflexivity. }
    iMod (reg_update _ scause _ c1 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ c2 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_b 8 8 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval (xtval_exception_value e xv))
            with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base (uc_stvec C)) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    unfold s_trap, set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    assert (Hmc : update_subrange_vec_dec ms_b 8 8 ('b"0") = utrap_ms elp0 ms_v)
      by (unfold utrap_ms, ms_b, ms_a, ms_e; reflexivity).
    iExists (update_subrange_vec_dec ms_b 8 8 ('b"0")), c2,
            (tval (xtval_exception_value e xv)), va, g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hupt".
    iSplitR.
    { iPureIntro. rewrite Hmc.
      destruct Hmsok as (HSXL & HMPRV & HMXR).
      split; [ rewrite utrap_ms_SXL; exact HSXL | ].
      split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
      split; [ rewrite utrap_ms_MXR; exact HMXR | ].
      split; [ rewrite utrap_ms_SPP; reflexivity | ].
      rewrite utrap_ms_SIE; reflexivity. }
    iSplitL "Hpc Hnpc". { iFrame "Hpc Hnpc". }
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The ILLEGAL obligation: execute found the instruction ILLEGAL         *)
  (* (privileged instruction at User).  The gpr file is untouched; nextPC  *)
  (* moved (the pre-execute write) and the fetch may have filled the TLB,  *)
  (* so interp + the nextPC cell + [upt_inv] change hands.  The cause is   *)
  (* FIXED (E_Illegal_Instr, delegated by [uc_del]); the tval is the       *)
  (* instruction bits, supplied by try_step's dedicated arm.               *)
  (* ------------------------------------------------------------------- *)
  Definition illegal_obligation (E : coPset) (σ : mstate) (va : mword 64)
      : iProp Σ :=
    (⌜exec (dispatchInterrupt User) σ = Some (None, σ)⌝ -∗
     ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
     ⌜register_lookup PC σ.(sregs) = va⌝ -∗
     ⌜user_mstatus_ok (register_lookup mstatus σ.(sregs))⌝ -∗
     mstate_interp σ -∗
     nextPC ↦ᵣ va -∗
     upt_inv pt -∗
     user_cfg C -∗
     |={E}=>
       ∃ (ib : mword 32) (s_x : mstate) (va' : mword 64),
         ⌜exec (run_hart_active 0) σ
            = Some (Step_Execute (Illegal_Instruction tt, ib), s_x)⌝ ∗
         ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
            = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
         ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
         mstate_interp s_x ∗
         nextPC ↦ᵣ va' ∗
         upt_inv pt ∗
         user_cfg C)%I.

  (* ------------------------------------------------------------------- *)
  (* The ILLEGAL arm: try_step's Illegal_Instruction arm runs the          *)
  (* delegated tower at the post-execute state with tval = the             *)
  (* INSTRUCTION BITS and sepc := the faulting pc (read from PC); PC       *)
  (* ticks to the handler base, no bump -- [user_trap_frame].              *)
  (* ------------------------------------------------------------------- *)
  Lemma illegal_branch (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64)) (mst : mword 64) (mi : bool) :
    user_mstatus_ok ms_v ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup PC σ.(sregs) = va ->
    (forall b : bool,
       exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
         = Some (None, set_reg σ (R_bool minstret_increment) b)) ->
    hw_config -∗
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    (∀ b : bool,
       illegal_obligation Ei (set_reg σ (R_bool minstret_increment) b) va) -∗
    ▷ (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "#Hhw [Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (T hart_state _ Lhs0 eq_refl).
    assert (HprivA : register_lookup cur_privilege s_a.(sregs) = User)
      by exact (T cur_privilege _ Lpriv eq_refl).
    assert (HpcA : register_lookup PC s_a.(sregs) = va)
      by exact (T PC _ Lpc eq_refl).
    assert (HmsokA : user_mstatus_ok (register_lookup mstatus s_a.(sregs))).
    { rewrite (T mstatus _ Lms eq_refl). exact Hmsok. }
    (* the per-family obligation, at the post-increment state *)
    iMod ("Hob" $! b (Hdisp b) HprivA HpcA HmsokA
            with "[Hreg Hmd] Hnpc Hupt Hcfg")
      as (ib s_x va')
         "(%Hha & %Hhart_x & %Hmi_x & %Lnpc_x & [Hreg Hmd] & Hnpc & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* read everything the trap tower needs at the post-execute state s_x *)
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv_x.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms_x.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc_x.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa_x.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp_x.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc_x.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec_x.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl_x.
    assert (HmisaS_x : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_x; exact HmisaS).
    assert (Hdel_x : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true)
      by (rewrite Lmedl_x; exact (uc_del C (E_Illegal_Instr tt) eq_refl)).
    (* the trap tower at s_x: tval = the instruction bits, sepc := PC = va *)
    pose proof (exec_handle_exception_U s_x (rv64d_types.Exception (E_Illegal_Instr tt))
                  (xtval_exception_value (E_Illegal_Instr tt) (zero_extend' 64 ib))
                  va ms_v sc_v (uc_stvec C) elp0
                  Lpriv_x Lms_x Lsc_x Lstvec_x Lelp_x HmisaS_x (uc_tvd C) Lpc_x
                  (E_Illegal_Instr tt) (zero_extend' 64 ib) eq_refl eq_refl Hdel_x) as Hhe.
    set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhe.
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Hhart_x. }
    (* the whole-step reduction: tick PC := nextPC = handler base, NO bump *)
    assert (Hstep : exec (riscv_step false) σ
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_execute_illegal;
        [ exact Hsi | exact Hhart_a | exact Hha | exact Hhe | exact Lhs_trap ]. }
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
    { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    (* GHOST: mirror every physical write of the tower in order *)
    pose (ms_e := update_subrange_vec_dec ms_v 23 23 elp0).
    pose (c1 := update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                  (bool_to_bit (trapCause_is_interrupt
                     (rv64d_types.Exception (E_Illegal_Instr tt))))).
    pose (c2 := update_subrange_vec_dec c1 (64 - 2) 0
                  (zero_extend' (64 - 1)
                     (trapCause_bits_forwards
                        (rv64d_types.Exception (E_Illegal_Instr tt))))).
    pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
    pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
    iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp_x Help0. reflexivity. }
    iMod (reg_update _ scause _ c1 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ c2 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_b 8 8 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval (xtval_exception_value (E_Illegal_Instr tt)
            (zero_extend' 64 ib))) with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base (uc_stvec C)) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    unfold s_trap, set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    assert (Hmc : update_subrange_vec_dec ms_b 8 8 ('b"0") = utrap_ms elp0 ms_v)
      by (unfold utrap_ms, ms_b, ms_a, ms_e; reflexivity).
    iExists (update_subrange_vec_dec ms_b 8 8 ('b"0")), c2,
            (tval (xtval_exception_value (E_Illegal_Instr tt) (zero_extend' 64 ib))),
            va, g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hupt".
    iSplitR.
    { iPureIntro. rewrite Hmc.
      destruct Hmsok as (HSXL & HMPRV & HMXR).
      split; [ rewrite utrap_ms_SXL; exact HSXL | ].
      split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
      split; [ rewrite utrap_ms_MXR; exact HMXR | ].
      split; [ rewrite utrap_ms_SPP; reflexivity | ].
      rewrite utrap_ms_SIE; reflexivity. }
    iSplitL "Hpc Hnpc". { iFrame "Hpc Hnpc". }
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The ENTER-WAIT obligation: execute returned [Enter_Wait] (a user WRS  *)
  (* -- the reason is pinned to the two user-reachable ones, which is      *)
  (* exactly [user_hart_ok] for the WAITING re-entry).  Like the illegal   *)
  (* shape, the gpr file is untouched but nextPC moved (the pre-execute    *)
  (* write) and the fetch may have filled the TLB.                         *)
  (* ------------------------------------------------------------------- *)
  Definition enter_wait_obligation (E : coPset) (σ : mstate) (va : mword 64)
      : iProp Σ :=
    (⌜exec (dispatchInterrupt User) σ = Some (None, σ)⌝ -∗
     ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
     ⌜register_lookup PC σ.(sregs) = va⌝ -∗
     ⌜user_mstatus_ok (register_lookup mstatus σ.(sregs))⌝ -∗
     mstate_interp σ -∗
     nextPC ↦ᵣ va -∗
     upt_inv pt -∗
     user_cfg C -∗
     |={E}=>
       ∃ (wr : WaitReason) (ib : mword 32) (s_x : mstate) (va' : mword 64),
         ⌜exec (run_hart_active 0) σ
            = Some (Step_Execute (Enter_Wait wr, ib), s_x)⌝ ∗
         ⌜wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO⌝ ∗
         mstate_interp s_x ∗
         nextPC ↦ᵣ va' ∗
         upt_inv pt ∗
         user_cfg C)%I.

  (* ------------------------------------------------------------------- *)
  (* The ENTER-WAIT arm: hart_state := HART_WAITING (wr, ib); NO pc tick,  *)
  (* NO bump -- PC stays at the WRS and nextPC after it, the decoupled     *)
  (* WAITING shape [user_inv] binds ([wp_user_step_waiting] later wakes    *)
  (* or stays from there).                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma enter_wait_branch (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64)) (mst : mword 64) (mi : bool) :
    user_mstatus_ok ms_v ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup PC σ.(sregs) = va ->
    (forall b : bool,
       exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
         = Some (None, set_reg σ (R_bool minstret_increment) b)) ->
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    (∀ b : bool,
       enter_wait_obligation Ei (set_reg σ (R_bool minstret_increment) b) va) -∗
    ▷ (user_inv C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (T hart_state _ Lhs0 eq_refl).
    assert (HprivA : register_lookup cur_privilege s_a.(sregs) = User)
      by exact (T cur_privilege _ Lpriv eq_refl).
    assert (HpcA : register_lookup PC s_a.(sregs) = va)
      by exact (T PC _ Lpc eq_refl).
    assert (HmsokA : user_mstatus_ok (register_lookup mstatus s_a.(sregs))).
    { rewrite (T mstatus _ Lms eq_refl). exact Hmsok. }
    (* the obligation, at the post-increment state *)
    iMod ("Hob" $! b (Hdisp b) HprivA HpcA HmsokA
            with "[Hreg Hmd] Hnpc Hupt Hcfg")
      as (wr ib s_x va')
         "(%Hha & %Hwr & [Hreg Hmd] & Hnpc & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    assert (Hnop : wait_is_nop wr = false)
      by (destruct Hwr as [-> | ->]; reflexivity).
    (* the whole-step reduction: hart_state := WAITING, no tick, no bump *)
    pose proof (exec_riscv_step_enter_wait σ s_x wr ib b
                  Hsi Hhart_a Hha Hnop) as Hstep.
    (* GHOST: the one write *)
    iMod (reg_update _ hart_state _ (HART_WAITING (wr, ib)) with "Hreg Hhs")
      as "[Hreg Hhs]".
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    unfold set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    iExists (HART_WAITING (wr, ib)), ms_v, sc_v, stval_v, sepc_v, va, va', g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
    iPureIntro.
    split; [exact Hwr | split; [exact Hmsok | intros u Hu; discriminate Hu]].
  Qed.

End UserArms.
