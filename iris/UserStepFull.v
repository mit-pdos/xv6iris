(* UserStepFull.v -- the UNIFIED STEP WRAPPER: the single point where the
   external-interrupt wires are borrowed (from the device-shared invariant,
   via [wires_acc]) and the dispatch decision is made.

   Every user step is ONE atomic machine step.  Within it we borrow the
   wires, read their current values, decide [u_dispatch], and branch:
     - a pending delegated interrupt -> the interrupt trap to stvec
       ([interrupt_branch], produces [user_trap_frame]);
     - none -> the fetch/decode/execute classification [active_class] (the
       remaining work), which retires ([user_inv]) or traps.
   Because the borrow, the decision and the step are ONE atomic instant,
   the branches are payload producers sharing this wrapper's single step,
   NOT separate WP lemmas -- and no arm ever OWNS the wire cells.

   [wp_user_step_active] reduces [user_step_obligation_active] to
   [active_class]: the interrupt case is discharged, so all that is LEFT of
   the whole user-execution theorem is the no-interrupt classification. *)
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
Require Import WpDecode WpLeafCommon WpGprCsrwB WpIntrBits WpIntrCore.
Require Import UserPt UserExec UserStep UserTrap.
Local Open Scope Z_scope.
Import Defs.

Section UserStepFull.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  (* ------------------------------------------------------------------- *)
  (* The interrupt branch: a pending delegated interrupt traps to stvec.  *)
  (* Wire-free -- takes the wire VALUES + their lookup facts at σ.         *)
  (* Produces the [wp_exec_step_minstret] payload (inlining the minstret   *)
  (* prelude + exec_riscv_step_interrupt + the trap tower + PC tick).      *)
  (* ------------------------------------------------------------------- *)
  Lemma interrupt_branch (E Ei : coPset) (Φ : mval -> iProp Σ)
      (σ : mstate) (i : InterruptType)
      (ms_v sc_v stval_v sepc_v va : mword 64) (g : gmap regidx (mword 64))
      (mst : mword 64) (mi : bool) (misa0 : type_of_register misa) (elpv : mword 1)
      (meip seip : mword 1) :
    user_mstatus_ok ms_v ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec elpv (landing_pad_bits_backwards LP_EXPECTED) = false ->
    register_lookup cur_privilege σ.(sregs) = User ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup scause σ.(sregs) = sc_v ->
    register_lookup stvec σ.(sregs) = uc_stvec C ->
    register_lookup elp σ.(sregs) = elpv ->
    register_lookup misa σ.(sregs) = misa0 ->
    register_lookup PC σ.(sregs) = va ->
    register_lookup mip σ.(sregs) = uc_mip C ->
    register_lookup sig_meip σ.(sregs) = meip ->
    register_lookup sig_seip σ.(sregs) = seip ->
    register_lookup mie σ.(sregs) = uc_mie C ->
    register_lookup mideleg σ.(sregs) = uc_mideleg C ->
    u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C) = Some (i, Supervisor) ->
    mstate_interp σ -∗
    (minstret ↦ᵣ mst) -∗ (R_bool minstret_increment ↦ᵣ mi) -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗ sepc ↦ᵣ sepc_v -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va -∗
    gpr_file g -∗ upt_inv pt -∗ user_cfg C -∗
    ▷ (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    |={Ei}=> ∃ s' : mstate,
      ⌜exec riscv_step σ = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang) @ E {{ Φ }}).
  Proof.
    iIntros (Hmsok HmisaS Help_ne Lpriv Lms Lsc Lstvec Lelp Lmisa Lpc
             Lmip Lmeip Lseip Lmie Lmdl Hd)
      "[Hreg Hmd] Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg Hcont".
    pose proof (elp_no_lp elpv Help_ne) as Help0.
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs0.
    (* minstret prelude: minstret_increment := should_inc *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    (* facts about the post-increment state, obtained by transport (all
       reads are of registers ≠ minstret_increment) *)
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg σ (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    assert (Hdisp_a : exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
                      = Some (Some (i, Supervisor), set_reg σ (R_bool minstret_increment) b)).
    { rewrite (exec_dispatchInterrupt_U_reduce (set_reg σ (R_bool minstret_increment) b)
                 (uc_mip C) (uc_mie C) (uc_mideleg C) meip seip
                 ltac:(rewrite exec_currentlyEnabled_S; rewrite (T misa _ Lmisa eq_refl);
                       rewrite HmisaS; reflexivity)
                 (T mip _ Lmip eq_refl) (T sig_meip _ Lmeip eq_refl)
                 (T sig_seip _ Lseip eq_refl) (T mie _ Lmie eq_refl)
                 (T mideleg _ Lmdl eq_refl) (uc_mm C)).
      rewrite Hd. reflexivity. }
    pose proof (exec_run_hart_active_pending_U (set_reg σ (R_bool minstret_increment) b)
                  i Supervisor (T cur_privilege _ Lpriv eq_refl) Hdisp_a) as Hha.
    pose proof (exec_handle_interrupt_U (set_reg σ (R_bool minstret_increment) b)
                  (Interrupt i) None va ms_v sc_v (uc_stvec C) elpv
                  (T cur_privilege _ Lpriv eq_refl) (T mstatus _ Lms eq_refl)
                  (T scause _ Lsc eq_refl) (T stvec _ Lstvec eq_refl)
                  (T elp _ Lelp eq_refl)
                  ltac:(rewrite (T misa _ Lmisa eq_refl); exact HmisaS)
                  (uc_tvd C) (T PC _ Lpc eq_refl) i eq_refl eq_refl) as Hhi.
    set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhi.
    assert (Lhs_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Lhs0. }
    (* the pure whole-step reduction (σ pre-increment; the lemma does the
       minstret_increment write itself, giving s_tick = tick over s_trap) *)
    assert (Hstep : exec riscv_step σ
              = Some (tt, set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)))).
    { eapply exec_riscv_step_interrupt;
        [ exact Hsi | exact Lhs | exact Hha | exact Hhi | exact Lhs_trap ]. }
    (* GHOST: build interp s_tick from interp σ, matching every write.
       s_tick = set_reg s_trap PC (nextPC s_trap); nextPC s_trap = stvec_base *)
    assert (Lnpc_trap : register_lookup nextPC s_trap.(sregs) = stvec_base (uc_stvec C)).
    { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Lnpc_trap in Hstep.
    (* the exact tower values from UTrapReduce, so iFrame matches s'
       (whose tower is fixed by exec_riscv_step_interrupt) with no evars *)
    pose (ms_e := update_subrange_vec_dec ms_v 23 23 elpv).
    pose (c1 := update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                  (bool_to_bit (trapCause_is_interrupt (Interrupt i)))).
    pose (c2 := update_subrange_vec_dec c1 (64 - 2) 0
                  (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i)))).
    pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
    pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
    (* the trap tower, values spelled to match the fixed s' tower (the
       minstret_increment ghost write already happened in the prelude) *)
    iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp Help0. reflexivity. }
    iMod (reg_update _ scause _ c1 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ c2 with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_b 8 8 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval None) with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base (uc_stvec C)) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro. iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext.
    unfold set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "[-]").
    assert (Hmc : update_subrange_vec_dec ms_b 8 8 ('b"0") = utrap_ms elpv ms_v)
      by (unfold utrap_ms, ms_b, ms_a, ms_e; reflexivity).
    iExists (update_subrange_vec_dec ms_b 8 8 ('b"0")), c2, (tval None), va, g.
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
    iFrame "Hcfg".
  Qed.

  (* u_dispatch always delivers to Supervisor (uc_mm rules out M-destined). *)
  Lemma u_dispatch_Supervisor (mip_v mie_v mdv : mword 64) (meip seip : mword 1)
      (i : InterruptType) (p : Privilege) :
    u_dispatch mip_v meip seip mie_v mdv = Some (i, p) -> p = Supervisor.
  Proof.
    unfold u_dispatch.
    destruct (neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64));
      [ destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv)) | ];
      intro H; try discriminate H. injection H as -> ->. reflexivity.
  Qed.

  (* The no-interrupt CLASSIFICATION (the remaining work): from a step
     state [σ] with [u_dispatch = None] and the user machine, the
     fetch/decode/execute produces one whole [riscv_step] that either
     retires (re-establishing [user_inv]) or traps (producing
     [user_trap_frame]).  It owns [interp σ] + [minstret_inv_body] + the
     unpacked mutable frame + [upt_inv] + [user_cfg] + the Löb continuation,
     and returns the [wp_exec_step_minstret] payload at the inner mask. *)
  Definition active_class (E Ei : coPset) (Φ : mval -> iProp Σ) : iProp Σ :=
    (□ (∀ (σ : mstate) (ms_v sc_v stval_v sepc_v va : mword 64)
          (g : gmap regidx (mword 64)),
        ⌜user_mstatus_ok ms_v⌝ -∗
        ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
        ⌜register_lookup PC σ.(sregs) = va⌝ -∗
        ⌜exec (dispatchInterrupt User) σ = Some (None, σ)⌝ -∗
        user_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
        upt_inv pt -∗ user_cfg C -∗
        mstate_interp σ -∗ minstret_inv_body -∗
        ▷ ((user_inv C pt -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
           (user_trap_frame C pt -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
        |={Ei}=> ∃ s' : mstate,
          ⌜exec riscv_step σ = Some (tt, s')⌝ ∗
          ▷ (mstate_interp s' ∗ minstret_inv_body ∗
             WP (Loop : expr riscv_lang) @ E {{ Φ }})))%I.

  (* ------------------------------------------------------------------- *)
  (* THE UNIFIED STEP WRAPPER: borrow the wires once, decide dispatch,     *)
  (* branch.  Reduces [user_step_obligation_active] to [active_class]      *)
  (* (the no-interrupt fetch/execute classification -- the remaining       *)
  (* work); the interrupt case is discharged here.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_user_step_active E Φ (wN : namespace) :
    ↑minstretN ⊆ E ->
    ↑wN ⊆ E ->
    minstretN ## wN ->
    hw_config -∗
    minstret_inv -∗
    wires_acc wN -∗
    active_class E (E ∖ ↑minstretN ∖ ↑wN) Φ -∗
    user_step_obligation_active C pt E Φ.
  Proof.
    iIntros (HN HwE Hdisj) "#Hhw #Hmin #Hwires #Hclass".
    iIntros "!>" (ms_v sc_v stval_v sepc_v va g) "%Hmsok Hregs Hupt Hcfg Hk".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN ∖ ↑wN) Φ HN with "Hmin").
    iIntros (σ) "Hint Hbody".
    (* borrow the wires: E∖minstretN -> E∖minstretN∖wN *)
    iMod ("Hwires" $! (E ∖ ↑minstretN) with "[%]") as (meip seip) "(Hmeip & Hseip & Hclosew)".
    { assert (↑wN ⊆ E ∖ ↑minstretN) by solve_ndisj. done. }
    iDestruct "Hint" as "[Hreg [Hmem Hdev]]".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hnpc & Hgpr)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ & %Help_ne & _)".
    (* read all the values the dispatch decision / branches need *)
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc.
    assert (Hdisp : exec (dispatchInterrupt User) σ
              = Some (u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C), σ)).
    { apply (exec_dispatchInterrupt_U_reduce σ (uc_mip C) (uc_mie C) (uc_mideleg C) meip seip);
        try assumption.
      - rewrite exec_currentlyEnabled_S; rewrite Lmisa; rewrite HmisaS; reflexivity.
      - exact (uc_mm C). }
    (* re-bundle interp + cfg for the branches *)
    iAssert (mstate_interp σ) with "[Hreg Hmem Hdev]" as "Hint".
    { iFrame "Hreg Hmem Hdev". }
    iAssert (user_cfg C) with "[Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest". }
    destruct (u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C)) as [[i p]|] eqn:Hd.
    - (* pending interrupt: trap to stvec *)
      pose proof (u_dispatch_Supervisor _ _ _ _ _ _ _ Hd) as ->.
      iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
      iMod (interrupt_branch E (E ∖ ↑minstretN ∖ ↑wN) Φ σ i
              ms_v sc_v stval_v sepc_v va g mst mi misa0 elp0 meip seip
              Hmsok HmisaS Help_ne Lpriv Lms Lsc Lstvec Lelp Lmisa Lpc
              Lmip Lmeip Lseip Lmie Lmdl Hd
              with "Hint Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt Hcfg [Hk]")
        as (s') "[%Hexec Hrest]".
      { iNext. iDestruct "Hk" as "[_ $]". }
      iModIntro. iExists s'. iSplitR. { iPureIntro. exact Hexec. }
      iNext. iDestruct "Hrest" as "(Hint & Hbody & HWP)".
      iMod ("Hclosew" with "[$Hmeip $Hseip]") as "_".
      iModIntro. iFrame "Hint Hbody HWP".
    - (* no interrupt: the classification *)
      iMod ("Hclass" $! σ ms_v sc_v stval_v sepc_v va g Hmsok Lpriv Lpc Hdisp
              with "[Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr] Hupt Hcfg Hint Hbody Hk")
        as (s') "[%Hexec Hrest]".
      { iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr". }
      iModIntro. iExists s'. iSplitR. { iPureIntro. exact Hexec. }
      iNext. iDestruct "Hrest" as "(Hint & Hbody & HWP)".
      iMod ("Hclosew" with "[$Hmeip $Hseip]") as "_".
      iModIntro. iFrame "Hint Hbody HWP".
  Qed.

End UserStepFull.
