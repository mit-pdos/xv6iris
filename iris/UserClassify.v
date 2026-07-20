From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv WpGpr.
Require Import WpLeafCommon WpIntrCore.
Require Import UserPtTree UserExec UserStep UserTrap.
Local Open Scope Z_scope.
Import Defs.

Section UserClassify.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* The full execute-result outcome space at U-mode: retire, delegated
     user-trap, illegal, or enter-wait (WRS).  This REPLACES the 2-way
     [exec_step_result_ok] -- the earlier spec that could not classify the
     illegal / enter-wait families and so made the totalities unprovable. *)
  Definition u_result_ok (r : ExecutionResult) : Prop :=
    r = Retire_Success tt
    \/ (exists e xv pcx, r = rv64d_types.Trap (User, make_sync_exception e xv, pcx)
                         /\ user_exc e = true)
    \/ r = Illegal_Instruction tt
    \/ (exists wr, r = Enter_Wait wr /\ (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO)).

  (* The full run_hart_active outcome for an active hart: an executed result
     (any of the four above) or a fetch failure. *)
  Definition u_step_outcome (st : Step) : Prop :=
    (exists (r : ExecutionResult) (ib : mword 32), st = Step_Execute (r, ib) /\ u_result_ok r)
    \/ (exists (e : ExceptionType) (xv : mword 64),
          st = Step_Fetch_Failure (Virtaddr xv, e) /\ user_exc e = true).

  (* ONE obligation for the whole active step: run_hart_active produces a
     classified outcome, invariants + gpr + nextPC re-established. *)
  Definition active_step_obligation (E : coPset) (σ : mstate) (va : mword 64)
      (g : gmap regidx (mword 64)) : iProp Σ :=
    (⌜u_step_pre σ va⌝ -∗
     mstate_interp σ -∗ gpr_file g -∗ nextPC ↦ᵣ va -∗ user_pt_inv pt -∗ user_cfg C -∗
     |={E}=>
       ∃ (st : Step) (s_x : mstate) (g' : gmap regidx (mword 64)) (va' : mword 64),
         ⌜exec (run_hart_active 0) σ = Some (st, s_x)⌝ ∗
         ⌜u_step_outcome st⌝ ∗
         ⌜register_lookup hart_state s_x.(sregs) = HART_ACTIVE tt⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
            = register_lookup (R_bool minstret_increment) σ.(sregs)⌝ ∗
         ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
         mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C)%I.

  (* SHARED trap-delivery tail: given the whole-step reduction lands in the
     canonical [utrap_state], run the ghost update + assemble the frame.
     Reused by the trap / illegal / fetch-fault outcome cases. *)
  Lemma deliver_user_trap (Ei : coPset) (Φ : mval -> iProp Σ)
      (σ s_x : mstate) (c : TrapCause) (info : option (mword 64))
      (pcx ms_v sc_v stval_v sepc_v va va' : mword 64)
      (elp0 : mword 1) (mst : mword 64) (b : bool) (g : gmap regidx (mword 64)) :
    user_mstatus_ok ms_v ->
    register_lookup elp s_x.(sregs) = elp0 ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec (riscv_step false) σ
      = Some (tt, utrap_state s_x c info pcx ms_v sc_v elp0 (uc_stvec C)) ->
    mstate_interp s_x -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ b) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va' -∗
    gpr_file g -∗ user_pt_inv pt -∗ user_cfg C -∗
    ▷ (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗ WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    intros Hmsok Lelp_x Help_ne Hstep.
    iIntros "Hint Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hcont".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iMod (utrap_ghost s_x c info pcx ms_v sc_v stval_v sepc_v va va' elp0
            (uc_stvec C) Lelp_x Help_ne
            with "Hint Hms Hsc Hstval Hsepc Hpriv Hnpc Hpc")
      as "(Hint & Hms & Hsc & Hstval & Hsepc & Hpriv & Hnpc & Hpc)".
    iModIntro. iExists (utrap_state s_x c info pcx ms_v sc_v elp0 (uc_stvec C)).
    iSplitR. { iPureIntro. exact Hstep. }
    iNext. iFrame "Hint".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    iApply (user_trap_frame_intro C pt _ _ _ _ _ (utrap_ms_ok elp0 ms_v Hmsok)
             with "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt
                   [Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest]").
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

  (* Non-consuming: read the two config regs the trap tower needs. *)
  Lemma user_cfg_facts (s : mstate) :
    reg_interp s.(sregs) -∗ user_cfg C -∗
    ⌜register_lookup stvec s.(sregs) = uc_stvec C
     /\ register_lookup medeleg s.(sregs) = uc_medeleg C⌝.
  Proof.
    iIntros "Hreg Hcfg".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hrest)".
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %L1.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %L2.
    iPureIntro. split; assumption.
  Qed.

  (* THE UNIFIED ACTIVE-STEP ARM: run the obligation, dispatch on the
     outcome (retire / trap / illegal / enter-wait / fetch-fault).  The three
     trap-family outcomes share [deliver_user_trap]. *)
  Lemma active_step_branch (Ei : coPset) (Φ : mval -> iProp Σ)
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
    gpr_file g -∗ user_pt_inv pt -∗ user_cfg C -∗
    (∀ b : bool, active_step_obligation Ei (set_reg σ (R_bool minstret_increment) b) va g) -∗
    ▷ ((user_inv C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }}) ∧
       (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗ WP (Loop : expr riscv_lang) {{ Φ }}).
  Proof.
    iIntros (Hmsok Lpriv Lms Lpc Hdisp)
      "#Hhw [Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hob Hcont".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by exact (lookup_set_mi σ b hart_state _ Lhs0 eq_refl).
    assert (Hpre : u_step_pre s_a va)
      by exact (u_step_pre_intro σ va ms_v b Hmsok Lpriv Lms Lpc (Hdisp b)).
    iMod ("Hob" $! b Hpre with "[Hreg Hmd] Hgpr Hnpc Hupt Hcfg")
      as (st s_x g' va')
         "(%Hha & %Hout & %Hhart_x & %Hmi_x & %Lnpc_x & [Hreg Hmd] & Hgpr & Hnpc & Hupt & Hcfg)".
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* facts the trap tower needs at s_x (all reads are non-consuming) *)
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv_x.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms_x.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc_x.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc_x.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa_x.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp_x.
    iDestruct (user_cfg_facts s_x with "Hreg Hcfg") as %(Lstvec_x & Lmedl_x).
    assert (HmisaS_x : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true)
      by (rewrite Lmisa_x; exact HmisaS).
    destruct Hout as [(r & ib & -> & Hr) | (e & xv & -> & He)].
    - (* Step_Execute (r, ib) *)
      destruct Hr as [-> | [(e & xv & pcx & -> & He) | [-> | (wr & -> & Hwr)]]].
      + (* RETIRE *)
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
        iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
        iDestruct "Hcont" as "[Hcont _]".
        destruct b.
        * iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
          iModIntro. iExists (set_reg s_tick minstret (add_vec_int mst 1)).
          iSplitR. { iPureIntro. exact Hstep. }
          iNext. unfold s_tick, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd".
          iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
          iApply ("Hcont" with "[-]").
          iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va', va', g'.
          iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
          iPureIntro. split; [exact Hmsok | intros u _; reflexivity].
        * iModIntro. iExists s_tick.
          iSplitR. { iPureIntro. exact Hstep. }
          iNext. unfold s_tick, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd".
          iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
          iApply ("Hcont" with "[-]").
          iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va', va', g'.
          iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
          iPureIntro. split; [exact Hmsok | intros u _; reflexivity].
      + (* EXECUTE-TRAP *)
        assert (Hdel_x : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                           (uint (exceptionType_bits_forwards e))) = true)
          by (rewrite Lmedl_x; exact (uc_del C e He)).
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
        assert (Hstep : exec (riscv_step false) σ
                  = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
        { eapply exec_riscv_step_execute_trap;
            [ exact Hsi | exact Hhart_a | exact Hha | exact Hxh | exact Lhs_trap ]. }
        assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
        { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
        rewrite Lnpc_trap in Hstep.
        assert (Hs' : set_reg s_trap PC (stvec_base (uc_stvec C))
                    = utrap_state s_x (rv64d_types.Exception e)
                        (xtval_exception_value e xv) pcx ms_v sc_v elp0 (uc_stvec C))
          by (unfold s_trap, s9x; reflexivity).
        rewrite Hs' in Hstep.
        iDestruct "Hcont" as "[_ Hcont]".
        iApply (deliver_user_trap Ei Φ σ s_x (rv64d_types.Exception e)
                  (xtval_exception_value e xv) pcx ms_v sc_v stval_v sepc_v va va' elp0 mst b g'
                  Hmsok Lelp_x Help_ne Hstep
                  with "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hcont").
        iFrame "Hreg Hmd".
      + (* ILLEGAL *)
        assert (Hdel_x : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                           (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true)
          by (rewrite Lmedl_x; exact (uc_del C (E_Illegal_Instr tt) eq_refl)).
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
        assert (Hstep : exec (riscv_step false) σ
                  = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
        { eapply exec_riscv_step_execute_illegal;
            [ exact Hsi | exact Hhart_a | exact Hha | exact Hhe | exact Lhs_trap ]. }
        assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
        { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
        rewrite Lnpc_trap in Hstep.
        assert (Hs' : set_reg s_trap PC (stvec_base (uc_stvec C))
                    = utrap_state s_x (rv64d_types.Exception (E_Illegal_Instr tt))
                        (xtval_exception_value (E_Illegal_Instr tt) (zero_extend' 64 ib)) va ms_v sc_v elp0 (uc_stvec C))
          by (unfold s_trap; reflexivity).
        rewrite Hs' in Hstep.
        iDestruct "Hcont" as "[_ Hcont]".
        iApply (deliver_user_trap Ei Φ σ s_x (rv64d_types.Exception (E_Illegal_Instr tt))
                  (xtval_exception_value (E_Illegal_Instr tt) (zero_extend' 64 ib)) va ms_v sc_v stval_v sepc_v va va' elp0 mst b g'
                  Hmsok Lelp_x Help_ne Hstep
                  with "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hcont").
        iFrame "Hreg Hmd".
      + (* ENTER-WAIT *)
        assert (Hnop : wait_is_nop wr = false)
          by (destruct Hwr as [-> | ->]; reflexivity).
        pose proof (exec_riscv_step_enter_wait σ s_x wr ib b
                      Hsi Hhart_a Hha Hnop) as Hstep.
        iMod (reg_update _ hart_state _ (HART_WAITING (wr, ib)) with "Hreg Hhs")
          as "[Hreg Hhs]".
        iDestruct "Hcont" as "[Hcont _]".
        iModIntro. iExists _.
        iSplitR. { iPureIntro. exact Hstep. }
        iNext. unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd".
        iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
        iApply ("Hcont" with "[-]").
        iExists (HART_WAITING (wr, ib)), ms_v, sc_v, stval_v, sepc_v, va, va', g'.
        iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg".
        iPureIntro.
        split; [exact Hwr | split; [exact Hmsok | intros u Hu; discriminate Hu]].
    - (* Step_Fetch_Failure (Virtaddr xv, e) *)
      assert (Hdel_x : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                         (uint (exceptionType_bits_forwards e))) = true)
        by (rewrite Lmedl_x; exact (uc_del C e He)).
      pose proof (exec_handle_exception_U s_x (rv64d_types.Exception e)
                    (xtval_exception_value e xv) va ms_v sc_v (uc_stvec C) elp0
                    Lpriv_x Lms_x Lsc_x Lstvec_x Lelp_x HmisaS_x (uc_tvd C) Lpc_x
                    e xv eq_refl eq_refl Hdel_x) as Hhe.
      set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhe.
      assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
      { unfold s_trap, set_reg; cbn [sregs].
        repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
        exact Hhart_x. }
      assert (Hstep : exec (riscv_step false) σ
                = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
      { eapply exec_riscv_step_fetch_failure;
          [ exact Hsi | exact Hhart_a | exact Hha | exact Hhe | exact Lhs_trap ]. }
      assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
      { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
      rewrite Lnpc_trap in Hstep.
      assert (Hs' : set_reg s_trap PC (stvec_base (uc_stvec C))
                  = utrap_state s_x (rv64d_types.Exception e)
                      (xtval_exception_value e xv) va ms_v sc_v elp0 (uc_stvec C))
        by (unfold s_trap; reflexivity).
      rewrite Hs' in Hstep.
      iDestruct "Hcont" as "[_ Hcont]".
      iApply (deliver_user_trap Ei Φ σ s_x (rv64d_types.Exception e)
                (xtval_exception_value e xv) va ms_v sc_v stval_v sepc_v va va' elp0 mst b g'
                Hmsok Lelp_x Help_ne Hstep
                with "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hcont").
      iFrame "Hreg Hmd".
  Qed.

End UserClassify.
