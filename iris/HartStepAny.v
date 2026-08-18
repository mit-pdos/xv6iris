(* HartStepAny.v -- THE CYCLE RULE THAT DOES NOT PICK THE ARM.

   [HartMCycle.swp_try_step_gen] covers one arm of [try_step]: the one where
   [dispatchInterrupt] returns None and the instruction retires.  A caller
   cannot always promise that arm, and the reason is not a gap in the proof
   but the semantics: [dispatchInterrupt] reads the PLIC WIRES ([read_mip
   IncludePlatformInterrupts] ORs [sig_meip] / [sig_seip] into mip), those
   cells live in [WireInv.wire_inv] rather than in any frame, and under
   per-node stepping another hart may move them BETWEEN the dispatch's nodes.
   Whether this cycle retires an instruction or takes a trap is the machine's
   choice, not the caller's.

   So the rule here offers BOTH arms and lets the body say what holds in each
   one the machine may reach: the body's postcondition MATCHES on the step,
   and the post-FILE is a PREDICATE [Q] rather than a parameter, since the
   arms land on different files.  Two consequences worth knowing:

   - The two tails differ only in [retired] -- true for a retire, false for a
     trap -- so the trap arm skips the minstret bump (and never even reads
     [minstret_increment], since [and_boolM (returnM false) _]
     short-circuits).  Both still land in [∃ mi, wrap_post rs2 mi], because
     taking [mi] to be the value minstret already holds makes that set an
     identity ([HartMCycle.reg_set_id_agree_local]).  That is what lets
     [wp_loop_cycle] and [swp_tick_wrap] be reused verbatim.

   - [handle_interrupt] runs AFTER [run_hart_active] returned, in [try_step]'s
     own match, so it cannot ride inside the dispatch's [swp].  It sits in the
     dispatch's POSTCONDITION instead of beside it as a ∀-quantified premise,
     which is what threads the frames without a second binder.

   The predicate post-file is also exactly what [csrw stimecmp] needs, for an
   unrelated reason: [clint_dispatch] refreshes mip and the leaf cannot name
   the value it lands on.

   [swp_try_step_gen] and [swp_exec_step_decode_execute] are the instances
   where [Q] is a singleton and only the retire arm is offered; they should
   BECOME instances at the fold-back.  Not yet covered: the [Enter_Wait] arm
   ([WpSmodeWfi]) and the exception arms, which the [| _ => False] branch
   refuses -- adding one is a branch here plus its tail's [retired] value.

   The rule is PRIVILEGE-AGNOSTIC, and has to be: the only client that needs
   both arms is the S-mode kernel taking a trap, so a rule pinned to Machine
   would have no caller at all.  What the prelude does with the privilege is
   read it and hand it to [should_inc_minstret], so [wrap_pre] reads it off
   the file and [minstret_inc_flag] takes it as an argument; nothing here
   mentions a mode.  (The strong tick variants in [HartMCycle] --
   [mcycle_inc_flag], [swp_tick_clock] -- are still Machine-pinned; the cycle
   rule does not use them.)

   THIS FILE IS ADDITIVE TO [HartMCycle] AND BELONGS IN IT.  It is separate
   only so that iterating does not rebuild the ~1000-file cone of a
   bottom-of-tree file; fold it back at a milestone. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartMCycle.
Require Import RiscvTryStep RiscvExtras.
Local Open Scope Z_scope.

(* the two spine reducers this file needs, same whitelists HartMCycle uses *)
Local Ltac i_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi
     get_config_print_instr].

Local Ltac i_peel :=
  repeat first
    [ rewrite register_lookup_set
    | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ].

Section stepany.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ==================================================================== *)
  (* BOTH ARMS AT ONCE, and why one rule has to serve them.                *)
  (*                                                                      *)
  (* [dispatchInterrupt] reads the PLIC WIRES ([read_mip                   *)
  (* IncludePlatformInterrupts] ORs [sig_meip] / [sig_seip] into mip), and  *)
  (* those cells live in [WireInv.wire_inv] -- no frame holds them, and     *)
  (* under per-node stepping another hart may change them BETWEEN the       *)
  (* dispatch's nodes.  So a caller CANNOT know, before the step, whether    *)
  (* this cycle retires an instruction or takes a trap.  A one-armed rule    *)
  (* would be unusable: the machine chooses.                               *)
  (*                                                                      *)
  (* Hence the body's postcondition MATCHES on the step it reached, and the  *)
  (* post-file is a PREDICATE [Q] rather than a parameter, since the two     *)
  (* arms land on different files.  The two tails differ only in [retired]  *)
  (* -- true for a retire, false for a trap -- so the trap arm skips the     *)
  (* minstret bump, and both land in the same [∃ mi, wrap_post rs2 mi]       *)
  (* shape because taking [mi] to be the value minstret already holds makes  *)
  (* that set an identity.                                                 *)
  (*                                                                      *)
  (* [HartMCycle.swp_try_step_gen] is the instance where [Q] is a singleton  *)
  (* and only the retire arm is offered; [swp_try_step_intr] above is the    *)
  (* instance where only the trap arm is.  Both should BECOME instances of   *)
  (* this at the fold-back.                                                 *)
  (* ==================================================================== *)
  Lemma swp_try_step_any (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Q : regstate -> Prop) (R : iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    (* every post-file the body may choose keeps the hart active and carries
       the flag the prelude wrote *)
    (forall rs2, Q rs2 -> register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall rs2, Q rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
           (register_lookup (R_bitvector_64 minstretcfg) rs)
           (register_lookup cur_privilege rs)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame (wrap_pre rs) Drw -∗ hreg_frame_ro Df (wrap_pre rs) Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R)
            | _ => False
            end)) -∗
    swp (try_step 0 false)
      (fun _ => ∃ (rs2 : regstate) (mi : SailStdpp.Values.mword 64),
                  ⌜Q rs2⌝ ∗ hreg_frame (wrap_post rs2 mi) Drw ∗
                  hreg_frame_ro Df (wrap_post rs2 mi) Dro ∗ R)%I.
  Proof.
    intros Hdisj HDpriv HDhart HDmc HDcfg HWmi HDmi HWms HDms
      HWpc HDpc HDnpc Hhart HQhart HQmi.
    iIntros "#Hcert Hrw Hro Hbody".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (should_inc_minstret (register_lookup cur_privilege rs))
              _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_should_inc_minstret Drw Dro Df rs _ Hdisj HDmc HDcfg
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use
                (Defs.write_reg (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)
                      (register_lookup cur_privilege rs)))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HWmi
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    i_peel. rewrite Hhart.
    (* THE STEP.  The machine chooses the arm; the body says what holds in
       each one it may choose. *)
    iApply (swp_bind_use (run_hart_active 0) _ _ _
              with "[Hrw Hro Hbody] [-]").
    { iApply ("Hbody" with "Hrw Hro"). }
    iIntros (st) "H". iDestruct "H" as (rs2) "[%HQ Harm]".
    pose proof (HQhart rs2 HQ) as Hhart2.
    pose proof (HQmi rs2 HQ) as Hmi2.
    destruct st as [ [i p] | e | [va e] | [er ib] | wr ];
      [ | iDestruct "Harm" as %[] | iDestruct "Harm" as %[] | | iDestruct "Harm" as %[] ].
    - (* ---- Step_Pending_Interrupt: the trap, then the no-bump tail ---- *)
      i_glue.
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                          hreg_frame_ro Df rs2 Dro ∗ R)%I _
                with "[Harm] [-]").
      { iApply (swp_bind0_use (handle_interrupt i p) _
                  (fun _ => (hreg_frame rs2 Drw ∗
                             hreg_frame_ro Df rs2 Dro ∗ R)%I)
                  _ with "Harm [-]").
        iIntros (u) "(Hrw & Hro & HR)".
        iApply (swp_mono with "[HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
        iSplitR; [done|]. iFrame. }
      iIntros (v) "(-> & Hrw & Hro & HR)". i_glue.
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      rewrite !mbind0_ret.
      iApply swp_ret. iExists rs2.
      iExists (register_lookup (R_bitvector_64 minstret)
                 (register_set (R_bitvector_64 PC)
                    (register_lookup (R_bitvector_64 nextPC) rs2) rs2)).
      iSplitR; [done|]. unfold wrap_post.
      rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
      rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
      iFrame.
    - (* ---- Step_Execute: only the retiring result is offered ---- *)
      destruct er as [ [] | ins | wr' | [] | [] | [[pr exc] epc] | [] | ce | de | [] ];
        [ | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] ].
      iDestruct "Harm" as "(Hrw & Hro & HR)". i_glue.
      (* the hart_state assert, then the tail WITH the bump *)
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                          hreg_frame_ro Df rs2 Dro ∗ R)%I _
                with "[Hrw Hro HR] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame rs2 Drw ∗
                             hreg_frame_ro Df rs2 Dro ∗ R)%I) _
                  with "[Hrw Hro HR] [-]").
        { iApply (swp_bind_use (Defs.read_reg hart_state) _ _ _
                    with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                      with "Hcert Hrw Hro"). }
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
          cbn beta iota zeta delta [hart_is_active Defs.assert_exp].
          iApply swp_ret. iFrame. }
        iIntros (u) "(Hrw & Hro & HR)".
        iApply (swp_mono with "[HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
        iSplitR; [done|]. iFrame. }
      iIntros (v) "(-> & Hrw & Hro & HR)". i_glue.
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      iApply (swp_bind_use (Defs.read_reg (R_bool minstret_increment))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDmi
                  with "Hcert Hrw Hro"). }
      iIntros (w) "(-> & Hrw & Hro)". i_peel. rewrite Hmi2. i_glue.
      destruct (minstret_inc_flag
                  (register_lookup (R_bitvector_32 mcountinhibit) rs)
                  (register_lookup (R_bitvector_64 minstretcfg) rs)
                  (register_lookup cur_privilege rs)) eqn:Hmi.
      + iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind0_use _ _
                    (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                    with "[Hrw Hro] [-]").
          { iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 minstret))
                      _ _ _ with "[Hrw Hro] [-]").
            { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDms
                        with "Hcert Hrw Hro"). }
            iIntros (v0) "(-> & Hrw & Hro)".
            iApply (swp_write_reg_owned Drw Dro Df _ _ _ Hdisj HWms
                      with "Hcert Hrw Hro"). }
          iIntros (u0) "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
        iIntros (u1) "[Hrw Hro]".
        iApply swp_ret. iExists rs2, _. iSplitR; [done|].
        unfold wrap_post. iFrame.
      + iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind0_use _ _
                    (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                    with "[Hrw Hro] [-]").
          { iApply swp_ret. iFrame. }
          iIntros (u2') "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
        iIntros (u3) "[Hrw Hro]".
        iApply swp_ret. iExists rs2.
        iExists (register_lookup (R_bitvector_64 minstret)
                   (register_set (R_bitvector_64 PC)
                      (register_lookup (R_bitvector_64 nextPC) rs2) rs2)).
        iSplitR; [done|]. unfold wrap_post.
        rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
        rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
        iFrame.
  Qed.

  (* ==================================================================== *)
  (* THE BOUNDARY RULE, BOTH ARMS, POST-FILE A PREDICATE.                  *)
  (*                                                                      *)
  (* This is the rule the two remaining engines want, and the one           *)
  (* [swp_exec_step_decode_execute] should become an instance of:           *)
  (*                                                                      *)
  (* - the INTERRUPT engine needs both arms, because the PLIC wires are not  *)
  (*   in any frame and may move between the dispatch's nodes (see the note  *)
  (*   on [swp_try_step_any]);                                             *)
  (* - [csrw stimecmp] needs the post-file to be a PREDICATE, because        *)
  (*   [clint_dispatch] refreshes mip and the leaf cannot name the value it  *)
  (*   lands on -- mip ∈ [tk_clock3], so the continuation never constrained  *)
  (*   it anyway.                                                           *)
  (*                                                                      *)
  (* Same three layers underneath as the retire rule ([wp_loop_cycle] over   *)
  (* [swp_tick_wrap] over the try_step body), and the same continuation      *)
  (* shape -- agreement off the clock cells -- with [Q] threaded through.    *)
  (* ==================================================================== *)
  Lemma swp_exec_step_any (Drw Dro : gset register)
      (Df : register -> dfrac) (rs1 rsA : regstate)
      (Q : regstate -> Prop) (Psi : iProp Σ) :
    Drw ## Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    register_lookup hart_state rs1 = HART_ACTIVE tt ->
    (forall rs2, Q rs2 -> register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall rs2, Q rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
           (register_lookup (R_bitvector_64 minstretcfg) rs1)
           (register_lookup cur_privilege rs1)) ->
    reg_agree_on (Drw ∪ Dro) (wrap_pre rs1) rsA ->
    gen_cert -∗
    (* the reservation mirror (design §3a): in at whatever the last
       instruction left, handed to the body at [None]; the body returns it
       inside [Psi] if the caller wants it back *)
    resv_any cpu_id -∗
    hreg_frame rs1 Drw -∗
    hreg_frame_ro Df rs1 Dro -∗
    (resv_frag cpu_id None -∗
     hreg_frame rsA Drw -∗ hreg_frame_ro Df rsA Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Psi
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi)
            | _ => False
            end)) -∗
    ▷ (∀ rs3 : regstate,
         ⌜∃ (rs2 : regstate) (mi : SailStdpp.Values.mword 64),
            Q rs2 /\
            reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs3
              (wrap_post rs2 mi)⌝ -∗
         hreg_frame rs3 Drw -∗ hreg_frame_ro Df rs3 Dro -∗ Psi -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hdisj HWcy HWti HWip HDpriv HDhart HDmc HDcfg HWmi HDmi HWms HDms
      HWpc HDpc HDnpc Hhart HQhart HQmi Hpre.
    iIntros "#Hcert Hfrag Hrw Hro Hbody Hcont".
    iApply (wp_loop_cycle Drw Dro Df
              (fun rsx => exists (rs2 : regstate)
                            (mi : SailStdpp.Values.mword 64),
                 Q rs2 /\ rsx = wrap_post rs2 mi)
              Psi Hdisj HWcy HWti HWip with "Hcert Hfrag [Hrw Hro Hbody] [Hcont]").
    2:{ iNext. iIntros (rs3) "%Hag Hrw Hro HPsi".
        destruct Hag as (rsP & (rs2 & mi & HQ & ->) & Hag).
        iApply ("Hcont" with "[%] Hrw Hro HPsi").
        exists rs2, mi. split; [exact HQ | exact Hag]. }
    iNext. iIntros "Hfrag".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_try_step_any Drw Dro Df rs1 Q Psi Hdisj HDpriv
                   HDhart HDmc HDcfg HWmi HDmi HWms HDms HWpc HDpc HDnpc
                   Hhart HQhart HQmi with "Hcert Hrw Hro [Hbody Hfrag]") ].
    { iIntros (u). iDestruct 1 as (rs2 mi) "(%HQ & Hrw & Hro & HPsi)".
      iExists _. iSplitR; [iPureIntro; by exists rs2, mi|]. iFrame. }
    iIntros "Hrw Hro".
    rewrite (hreg_frame_ext _ rsA Drw (reg_agree_l _ _ _ _ Hpre)).
    rewrite (hreg_frame_ro_ext Df _ rsA Dro (reg_agree_r _ _ _ _ Hpre)).
    iApply ("Hbody" with "Hfrag Hrw Hro").
  Qed.

  (* the INDEXED-RIDER twins: [Psi] keyed on the body's post-file, for a
     body whose landing file is existential (an S-mode fetch that may fill
     the TLB) and whose rider is keyed on it -- see [HartMCycle.wp_loop_cycle_ex] *)
  Lemma swp_try_step_any_ex (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Q : regstate -> Prop) (R : regstate -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    (* every post-file the body may choose keeps the hart active and carries
       the flag the prelude wrote *)
    (forall rs2, Q rs2 -> register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall rs2, Q rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
           (register_lookup (R_bitvector_64 minstretcfg) rs)
           (register_lookup cur_privilege rs)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame (wrap_pre rs) Drw -∗ hreg_frame_ro Df (wrap_pre rs) Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R rs2
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)
            | _ => False
            end)) -∗
    swp (try_step 0 false)
      (fun _ => ∃ (rs2 : regstate) (mi : SailStdpp.Values.mword 64),
                  ⌜Q rs2⌝ ∗ hreg_frame (wrap_post rs2 mi) Drw ∗
                  hreg_frame_ro Df (wrap_post rs2 mi) Dro ∗ R rs2)%I.
  Proof.
    intros Hdisj HDpriv HDhart HDmc HDcfg HWmi HDmi HWms HDms
      HWpc HDpc HDnpc Hhart HQhart HQmi.
    iIntros "#Hcert Hrw Hro Hbody".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (should_inc_minstret (register_lookup cur_privilege rs))
              _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_should_inc_minstret Drw Dro Df rs _ Hdisj HDmc HDcfg
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use
                (Defs.write_reg (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)
                      (register_lookup cur_privilege rs)))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HWmi
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    i_peel. rewrite Hhart.
    (* THE STEP.  The machine chooses the arm; the body says what holds in
       each one it may choose. *)
    iApply (swp_bind_use (run_hart_active 0) _ _ _
              with "[Hrw Hro Hbody] [-]").
    { iApply ("Hbody" with "Hrw Hro"). }
    iIntros (st) "H". iDestruct "H" as (rs2) "[%HQ Harm]".
    pose proof (HQhart rs2 HQ) as Hhart2.
    pose proof (HQmi rs2 HQ) as Hmi2.
    destruct st as [ [i p] | e | [va e] | [er ib] | wr ];
      [ | iDestruct "Harm" as %[] | iDestruct "Harm" as %[] | | iDestruct "Harm" as %[] ].
    - (* ---- Step_Pending_Interrupt: the trap, then the no-bump tail ---- *)
      i_glue.
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                          hreg_frame_ro Df rs2 Dro ∗ R rs2)%I _
                with "[Harm] [-]").
      { iApply (swp_bind0_use (handle_interrupt i p) _
                  (fun _ => (hreg_frame rs2 Drw ∗
                             hreg_frame_ro Df rs2 Dro ∗ R rs2)%I)
                  _ with "Harm [-]").
        iIntros (u) "(Hrw & Hro & HR)".
        iApply (swp_mono with "[HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
        iSplitR; [done|]. iFrame. }
      iIntros (v) "(-> & Hrw & Hro & HR)". i_glue.
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      rewrite !mbind0_ret.
      iApply swp_ret. iExists rs2.
      iExists (register_lookup (R_bitvector_64 minstret)
                 (register_set (R_bitvector_64 PC)
                    (register_lookup (R_bitvector_64 nextPC) rs2) rs2)).
      iSplitR; [done|]. unfold wrap_post.
      rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
      rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
      iFrame.
    - (* ---- Step_Execute: only the retiring result is offered ---- *)
      destruct er as [ [] | ins | wr' | [] | [] | [[pr exc] epc] | [] | ce | de | [] ];
        [ | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] ].
      iDestruct "Harm" as "(Hrw & Hro & HR)". i_glue.
      (* the hart_state assert, then the tail WITH the bump *)
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                          hreg_frame_ro Df rs2 Dro ∗ R rs2)%I _
                with "[Hrw Hro HR] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame rs2 Drw ∗
                             hreg_frame_ro Df rs2 Dro ∗ R rs2)%I) _
                  with "[Hrw Hro HR] [-]").
        { iApply (swp_bind_use (Defs.read_reg hart_state) _ _ _
                    with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                      with "Hcert Hrw Hro"). }
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
          cbn beta iota zeta delta [hart_is_active Defs.assert_exp].
          iApply swp_ret. iFrame. }
        iIntros (u) "(Hrw & Hro & HR)".
        iApply (swp_mono with "[HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
        iSplitR; [done|]. iFrame. }
      iIntros (v) "(-> & Hrw & Hro & HR)". i_glue.
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      iApply (swp_bind_use (Defs.read_reg (R_bool minstret_increment))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDmi
                  with "Hcert Hrw Hro"). }
      iIntros (w) "(-> & Hrw & Hro)". i_peel. rewrite Hmi2. i_glue.
      destruct (minstret_inc_flag
                  (register_lookup (R_bitvector_32 mcountinhibit) rs)
                  (register_lookup (R_bitvector_64 minstretcfg) rs)
                  (register_lookup cur_privilege rs)) eqn:Hmi.
      + iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind0_use _ _
                    (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                    with "[Hrw Hro] [-]").
          { iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 minstret))
                      _ _ _ with "[Hrw Hro] [-]").
            { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDms
                        with "Hcert Hrw Hro"). }
            iIntros (v0) "(-> & Hrw & Hro)".
            iApply (swp_write_reg_owned Drw Dro Df _ _ _ Hdisj HWms
                      with "Hcert Hrw Hro"). }
          iIntros (u0) "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
        iIntros (u1) "[Hrw Hro]".
        iApply swp_ret. iExists rs2, _. iSplitR; [done|].
        unfold wrap_post. iFrame.
      + iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind0_use _ _
                    (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                    with "[Hrw Hro] [-]").
          { iApply swp_ret. iFrame. }
          iIntros (u2') "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
        iIntros (u3) "[Hrw Hro]".
        iApply swp_ret. iExists rs2.
        iExists (register_lookup (R_bitvector_64 minstret)
                   (register_set (R_bitvector_64 PC)
                      (register_lookup (R_bitvector_64 nextPC) rs2) rs2)).
        iSplitR; [done|]. unfold wrap_post.
        rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
        rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
        iFrame.
  Qed.

  Lemma swp_exec_step_any_ex (Drw Dro : gset register)
      (Df : register -> dfrac) (rs1 rsA : regstate)
      (Q : regstate -> Prop) (Psi : regstate -> iProp Σ) :
    Drw ## Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (R_bool minstret_increment : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstret : register) ∈ Drw ->
    (R_bitvector_64 minstret : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    register_lookup hart_state rs1 = HART_ACTIVE tt ->
    (forall rs2, Q rs2 -> register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall rs2, Q rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
           (register_lookup (R_bitvector_64 minstretcfg) rs1)
           (register_lookup cur_privilege rs1)) ->
    reg_agree_on (Drw ∪ Dro) (wrap_pre rs1) rsA ->
    gen_cert -∗
    (* the reservation mirror (design §3a): in at whatever the last
       instruction left, handed to the body at [None]; the body returns it
       inside [Psi] if the caller wants it back *)
    resv_any cpu_id -∗
    hreg_frame rs1 Drw -∗
    hreg_frame_ro Df rs1 Dro -∗
    (resv_frag cpu_id None -∗
     hreg_frame rsA Drw -∗ hreg_frame_ro Df rsA Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Psi rs2
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi rs2)
            | _ => False
            end)) -∗
    ▷ (∀ (rs3 rs2 : regstate) (mi : SailStdpp.Values.mword 64),
         ⌜Q rs2 /\
          reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs3 (wrap_post rs2 mi)⌝ -∗
         hreg_frame rs3 Drw -∗ hreg_frame_ro Df rs3 Dro -∗ Psi rs2 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hdisj HWcy HWti HWip HDpriv HDhart HDmc HDcfg HWmi HDmi HWms HDms
      HWpc HDpc HDnpc Hhart HQhart HQmi Hpre.
    iIntros "#Hcert Hfrag Hrw Hro Hbody Hcont".
    iApply (wp_loop_cycle_ex Drw Dro Df
              (fun rsx => exists (rs2 : regstate)
                            (mi : SailStdpp.Values.mword 64),
                 Q rs2 /\ rsx = wrap_post rs2 mi)
              (fun rsx => ∃ (rs2 : regstate) (mi : SailStdpp.Values.mword 64),
                 ⌜Q rs2 /\ rsx = wrap_post rs2 mi⌝ ∗ Psi rs2)%I
              Hdisj HWcy HWti HWip with "Hcert Hfrag [Hrw Hro Hbody] [Hcont]").
    2:{ iNext. iIntros (rs3 rsP) "%Hag Hrw Hro HPsi".
        destruct Hag as (_ & Hag).
        iDestruct "HPsi" as (rs2 mi) "[%HQe HPsi]".
        destruct HQe as [HQ ->].
        iApply ("Hcont" with "[%] Hrw Hro HPsi").
        split; [exact HQ | exact Hag]. }
    iNext. iIntros "Hfrag".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_try_step_any_ex Drw Dro Df rs1 Q Psi Hdisj HDpriv
                   HDhart HDmc HDcfg HWmi HDmi HWms HDms HWpc HDpc HDnpc
                   Hhart HQhart HQmi with "Hcert Hrw Hro [Hbody Hfrag]") ].
    { iIntros (u). iDestruct 1 as (rs2 mi) "(%HQ & Hrw & Hro & HPsi)".
      iExists (wrap_post rs2 mi). iSplitR; [iPureIntro; by exists rs2, mi|].
      iFrame "Hrw Hro". iExists rs2, mi. iFrame "HPsi". iPureIntro. by split. }
    iIntros "Hrw Hro".
    rewrite (hreg_frame_ext _ rsA Drw (reg_agree_l _ _ _ _ Hpre)).
    rewrite (hreg_frame_ro_ext Df _ rsA Dro (reg_agree_r _ _ _ _ Hpre)).
    iApply ("Hbody" with "Hfrag Hrw Hro").
  Qed.

End stepany.
