(* HartStepFull.v -- THE CYCLE RULE WITH ALL SIX ARMS, AND THE WAITING HART.

   [HartStepAny.swp_try_step_any] offers two of [try_step]'s arms
   ([Step_Execute (Retire_Success tt, _)] and [Step_Pending_Interrupt]) and
   refuses the rest with [| _ => False].  The user tier needs four more --
   the two execute-produced faults ([Illegal_Instruction], [Trap]), the
   failed fetch ([Step_Fetch_Failure]) and the wait entry
   ([Step_Execute (Enter_Wait wr, ib)]) -- plus the step a hart that is
   ALREADY waiting takes.  This file is those two rules.

   THREE THINGS THE MODEL SAYS THAT THE ARMS HAVE TO MIRROR (read off
   [rv64d.try_step], and cross-checked against the proved [exec] facts
   [UserTrap.exec_riscv_step_fetch_failure] / [_execute_illegal] /
   [_execute_trap] and [UserStep.exec_riscv_step_enter_wait] /
   [_wait_stay] / [_wait_wake]):

   - THE FOUR TRAP-ISH ARMS ARE [retired = false].  [Illegal_Instruction],
     [Trap] and [Step_Fetch_Failure] each run their handler, then the
     epilogue's [read_reg hart_state] (still ACTIVE), then [tick_pc], then
     [and_boolM (returnM false) (read_reg minstret_increment)] -- which
     SHORT-CIRCUITS, so [minstret_increment] is not even read and minstret
     is not bumped.  Their tails are therefore literally the
     [Step_Pending_Interrupt] tail, and all four land in
     [∃ mi, wrap_post rs2 mi] by [HartMCycle.reg_set_id_agree_local].

   - THE ENTER-WAIT ARM IS DIFFERENT IN KIND, AND IT IS THE REASON THE
     POST-FILE OF THIS RULE IS NOT [wrap_post].  With [wait_is_nop wr =
     false] the arm WRITES [hart_state := HART_WAITING (wr, instbits)]
     itself (nothing else), the epilogue's [read_reg hart_state] then sees
     a WAITING hart and returns [true] -- so there is NO [tick_pc] and NO
     minstret bump, and the file the cycle lands on is
     [register_set hart_state (HART_WAITING (wr, ib)) rs2].  That is why
     [tsf_post] below MATCHES on the step: the plan's suggestion to relax
     [swp_try_step_any]'s [HQhart] premise is not what is needed --
     [run_hart_active] returns [Enter_Wait] with the hart still ACTIVE, so
     [HQhart] stays TRUE and uniform; it is the CONCLUSION's post-file that
     has to admit a second shape.

   - [Q] IS INDEXED BY THE STEP, not just by the file.  A caller whose
     invariant constrains the wait reason ([UserExec]'s WAITING case is
     [wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO]) cannot re-establish it from
     [∃ wr ib, rs3 = register_set hart_state (HART_WAITING (wr, ib)) rs2]:
     the machine picks the arm, so the only place the caller can say
     anything about [wr] is a premise about the step the body reached.
     [Q : Step -> regstate -> Prop] costs nothing (the arms that ignore the
     step instantiate it constantly) and it is also what lets a caller tell
     a retire from a trap without decoding the post-file.

   The rider is INDEXED on the body's post-file ([R rs2] / [Psi rs2]),
   per the [_ex] convention of [HartMCycle.wp_loop_cycle_ex] /
   [HartStepAny.swp_try_step_any_ex]; the plain rider is the instance
   [R := fun _ => R0].  The WAITING rules keep a plain rider: they have no
   body obligation, so their rider is a resource the caller hands in BEFORE
   the step and there is no post-file for it to be keyed on.

   The waiting rule [swp_try_step_waiting] has no body obligation at all:
   [run_hart_waiting] is a register-only stretch over mip / mie /
   hart_state, all owned, so it is ONE [HartMemRun.swp_hmrun_of_exec] at
   [mm := ∅] -- the "goodmb at the empty map IS the register-writing
   analogue of [hval_of_goodb]" move of the port plan.  Its conclusion is a
   DISJUNCTION because the machine chooses: the wake test reads mip, which
   [wp_loop_cycle]'s continuation does not carry across a cycle (mip is in
   [tk_clock3]), and [valid_reservation] is an opaque platform predicate
   ([xv6iris_extras.resv_is_valid]; see ResvAxioms.v's header for why the
   reservation's CONTENT stays assumed while its two effectful hooks do not).

   The three [exec_run_hart_waiting_*] facts and their [goodmb] twins are
   proved HERE rather than imported from [UserStep.v]: they are facts about
   the model, with no user-tier content, and this file sits below the tier.
   [UserStep.v]'s copies become redundant when the tier lands -- and its
   [_stay] is stated too strongly: at [exit_wait = false] the only reachable
   wake patterns are [(WAIT_WRS_STO|WAIT_WRS_NTO, false, _)], so a
   [WAIT_WFI] hart stays waiting whatever [valid_reservation] answers.  The
   version here takes the disjunction, which is what makes the case split in
   [swp_try_step_waiting] EXHAUSTIVE.

   TWO THINGS THAT COST TIME AND WILL COST IT AGAIN:
   - [bytes_own ∅] is [emp], hence PERSISTENT: [iAssert … as "H"] files it
     in the intuitionistic context, where it is never consumed, and the next
     [iDestruct] that wants the name fails with "not fresh".  Introduce it as
     [#Hemp] and never re-use the name.
   - the shared tail of the four non-retiring arms is written out four times
     on purpose.  An [Ltac] abbreviation does NOT work here: a tactic
     notation's [constr] argument inside an [Ltac] body is elaborated at
     DEFINITION time, so [iApply (… Drw …)] fails with "The reference Drw was
     not found" before the proof is ever run.

   THIS FILE IS ADDITIVE TO [HartStepAny] AND BELONGS IN IT (which in turn
   belongs in [HartMCycle]); it is separate only so that iterating does not
   rebuild a bottom-of-tree cone.  Fold all three back at a milestone. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.xv6iris_extras Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartMemRun HartMCycle HartStepAny.
Local Open Scope Z_scope.

(* the two spine reducers, same whitelists [HartStepAny] uses *)
Local Ltac i_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq get_config_rvfi
     get_config_print_instr].

Local Ltac i_peel :=
  repeat first
    [ rewrite register_lookup_set
    | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ].

(* ====================================================================== *)
(* 1. THE TWO POST-FILE PREDICATES.                                        *)
(* ====================================================================== *)

(* What one cycle of an ACTIVE hart lands on.  Five of the six arms end
   ACTIVE and take the tick, so their file is [wrap_post rs2 mi] (the [mi]
   existential absorbs both the bumped and the un-bumped tail, exactly as
   in [swp_try_step_any]); the enter-wait arm ends WAITING and takes
   neither the tick nor the bump. *)
Definition tsf_post (Q : Step -> regstate -> Prop) (rs2 rs3 : regstate)
    : Prop :=
  exists st : Step,
    Q st rs2 /\
    match st with
    | Step_Execute (Enter_Wait wr, ib) =>
        wait_is_nop wr = false /\
        rs3 = register_set hart_state (HART_WAITING (wr, ib)) rs2
    | _ => exists mi : SailStdpp.Values.mword 64, rs3 = wrap_post rs2 mi
    end.

(* What one cycle of a WAITING hart lands on.  STAY: the whole cycle is the
   prelude's [minstret_increment] write, so the file is [wrap_pre rs] -- up
   to agreement on the footprint, which is all [swp_hmrun_of_exec] gives
   back.  WAKE (an interrupt is pending, or the reservation went invalid):
   [hart_state := HART_ACTIVE], then the ordinary retiring tail. *)
Definition wait_post (D : gset register) (rs : regstate) (rs3 : regstate)
    : Prop :=
  reg_agree_on D rs3 (wrap_pre rs)
  \/ (exists (rs' : regstate) (mi : SailStdpp.Values.mword 64),
        reg_agree_on D rs'
          (register_set hart_state (HART_ACTIVE tt) (wrap_pre rs))
        /\ rs3 = wrap_post rs' mi).

(* ====================================================================== *)
(* 2. [run_hart_waiting] AT [exit_wait = false]: THE PURE FACTS.           *)
(*                                                                        *)
(* The three outcomes and the three footprint certificates for them.       *)
(* [valid_reservation] is an opaque platform predicate returning a [bool]   *)
(* ([xv6iris_extras.resv_is_valid]), so the reservation branch is taken by  *)
(* DESTRUCTING it -- both values step.                                      *)
(* ====================================================================== *)

Lemma exec_shouldWakeForInterrupt (s : mstate) :
  exec (shouldWakeForInterrupt tt) s
    = Some (neq_vec (and_vec (register_lookup mip s.(sregs))
                             (register_lookup mie s.(sregs))) (zeros' 64), s).
Proof.
  unfold shouldWakeForInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)). cbn beta.
  apply exec_returnm.
Qed.

Lemma exec_run_hart_waiting_wake (wr : WaitReason) (ib : SailStdpp.Values.mword 32)
    (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = true ->
  exec (run_hart_waiting 0 wr ib false) s
    = Some (Step_Execute (Retire_Success tt, ib),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hw.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  change (get_config_print_instr tt) with false. cbn match.
  erewrite exec_bind0_Some. 2: apply exec_returnm.
  apply exec_returnm.
Qed.

Lemma exec_run_hart_waiting_wake_resv (wr : WaitReason) (ib : SailStdpp.Values.mword 32)
    (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = false ->
  valid_reservation tt = false ->
  wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO ->
  exec (run_hart_waiting 0 wr ib false) s
    = Some (Step_Execute (Retire_Success tt, ib),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hw Hvr Hwr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  rewrite Hvr.
  destruct Hwr as [-> | ->]; cbn match;
    (change (get_config_print_instr tt) with false; cbn match;
     erewrite exec_bind0_Some; [| apply exec_returnm];
     apply exec_returnm).
Qed.

(* STAY.  Note the disjunction: at [exit_wait = false] the match's only
   reachable wake patterns are [(WAIT_WRS_STO|WAIT_WRS_NTO, false, _)], so a
   [WAIT_WFI] hart stays waiting whatever [valid_reservation] answers --
   [UserStep.exec_run_hart_waiting_stay]'s [valid_reservation tt = true]
   premise is stronger than the model needs, and the case split in
   [swp_try_step_waiting] needs the weaker one to be exhaustive. *)
Lemma exec_run_hart_waiting_stay (wr : WaitReason) (ib : SailStdpp.Values.mword 32)
    (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = false ->
  valid_reservation tt = true \/ wr = WAIT_WFI ->
  exec (run_hart_waiting 0 wr ib false) s = Some (Step_Waiting wr, s).
Proof.
  intros Hw Hvr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  destruct Hvr as [Hvr | ->]; [rewrite Hvr; destruct wr
                              | destruct (valid_reservation tt)];
    cbn match;
    (change (get_config_print_instr tt) with false; cbn match;
     erewrite exec_bind0_Some; [| apply exec_returnm];
     apply exec_returnm).
Qed.

(* -------- the footprint certificates, [goodmb] at any owned map -------- *)

Lemma goodmb_shouldWakeForInterrupt (Dr Dw : register -> bool) (s : mstate)
    (mm : gmap Arch.pa (bv 8)) :
  Dr (R_bitvector_64 mip : register) = true ->
  Dr (R_bitvector_64 mie : register) = true ->
  goodmb Dr Dw (shouldWakeForInterrupt tt) s mm = true.
Proof.
  intros Hip Hie. unfold shouldWakeForInterrupt.
  cbn beta iota zeta delta
    [Defs.bind Interface.iMon_bind Defs.read_reg returnM Defs.returnm goodmb].
  by rewrite Hip Hie.
Qed.

Lemma mm_after_shouldWakeForInterrupt (s : mstate)
    (mm : gmap Arch.pa (bv 8)) :
  mm_after (shouldWakeForInterrupt tt) s mm = mm.
Proof.
  unfold shouldWakeForInterrupt.
  cbn beta iota zeta delta
    [Defs.bind Interface.iMon_bind Defs.read_reg returnM Defs.returnm mm_after].
  reflexivity.
Qed.

Lemma goodmb_run_hart_waiting (Dr Dw : register -> bool) (wr : WaitReason)
    (ib : SailStdpp.Values.mword 32) (s : mstate) (mm : gmap Arch.pa (bv 8)) :
  Dr (R_bitvector_64 mip : register) = true ->
  Dr (R_bitvector_64 mie : register) = true ->
  Dw (hart_state : register) = true ->
  goodmb Dr Dw (run_hart_waiting 0 wr ib false) s mm = true.
Proof.
  intros Hip Hie Hhs.
  unfold run_hart_waiting.
  rewrite (goodmb_bind Dr Dw (shouldWakeForInterrupt tt) _ s s mm _
             (goodmb_shouldWakeForInterrupt Dr Dw s mm Hip Hie)
             (exec_shouldWakeForInterrupt s)).
  rewrite mm_after_shouldWakeForInterrupt.
  destruct (neq_vec (and_vec (register_lookup mip s.(sregs))
                             (register_lookup mie s.(sregs))) (zeros' 64));
    cbn match.
  - change (get_config_print_instr tt) with false. cbn match.
    cbn beta iota zeta delta
      [Defs.bind0 Defs.bind Interface.iMon_bind Defs.write_reg returnM
       Defs.returnm goodmb].
    by rewrite Hhs.
  - destruct (valid_reservation tt); destruct wr; cbn match;
      (change (get_config_print_instr tt) with false; cbn match;
       cbn beta iota zeta delta
         [Defs.bind0 Defs.bind Interface.iMon_bind Defs.write_reg returnM
          Defs.returnm goodmb];
       try reflexivity; by rewrite Hhs).
Qed.

Section stepfull.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ================================================================== *)
  (* 3. THE SIX-ARMED CYCLE RULE.                                        *)
  (* ================================================================== *)
  Lemma swp_try_step_full (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (Q : Step -> regstate -> Prop)
      (R : regstate -> iProp Σ) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ->
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
    (* [run_hart_active] RETURNS with the hart still ACTIVE in every one of
       the six arms -- the enter-wait arm's [hart_state] write happens in
       [try_step]'s own match, below -- so this premise stays uniform *)
    (forall st rs2, Q st rs2 ->
       register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (* consumed only by the retiring arm: it is the one arm that reads
       [minstret_increment] ([and_boolM (returnM false) _] short-circuits in
       the other four, and the enter-wait arm never reaches the tick) *)
    (forall st rs2, Q st rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
           (register_lookup (R_bitvector_64 minstretcfg) rs)
           (register_lookup cur_privilege rs)) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame (wrap_pre rs) Drw -∗ hreg_frame_ro Df (wrap_pre rs) Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q st rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R rs2
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)
            | Step_Execute (Illegal_Instruction tt, ib) =>
                swp (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt))
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)
            | Step_Execute (rv64d_types.Trap (p, exc, pcx), _) =>
                swp (Defs.bind (exception_handler p exc pcx) set_next_pc)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)
            | Step_Fetch_Failure (Virtaddr xv, e) =>
                swp (handle_exception xv e)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)
            | Step_Execute (Enter_Wait wr, ib) =>
                ⌜wait_is_nop wr = false⌝ ∗
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ R rs2
            | _ => False
            end)) -∗
    swp (try_step 0 false)
      (fun _ => ∃ rs3 rs2 : regstate, ⌜tsf_post Q rs2 rs3⌝ ∗
                  hreg_frame rs3 Drw ∗ hreg_frame_ro Df rs3 Dro ∗ R rs2)%I.
  Proof.
    intros Hdisj HDpriv HWhart HDhart HDmc HDcfg HWmi HDmi HWms HDms
      HWpc HDpc HDnpc Hhart HQhart HQmi.
    iIntros "#Hcert Hrw Hro Hbody".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    (* ---- the prelude, verbatim from [swp_try_step_any] ---- *)
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
    (* ---- THE STEP.  The machine chooses among SIX arms. ---- *)
    iApply (swp_bind_use (run_hart_active 0) _ _ _
              with "[Hrw Hro Hbody] [-]").
    { iApply ("Hbody" with "Hrw Hro"). }
    iIntros (st) "H". iDestruct "H" as (rs2) "[%HQ Harm]".
    pose proof (HQhart _ rs2 HQ) as Hhart2.
    pose proof (HQmi _ rs2 HQ) as Hmi2.
    destruct st as [ [i p] | e | [[xv] ex] | [er ib] | wr ];
      [ | iDestruct "Harm" as %[] | | | iDestruct "Harm" as %[] ].
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
      iIntros (v0) "(-> & Hrw & Hro & HR)". i_glue.
      (* the tick, then [and_boolM (returnM false) _] SHORT-CIRCUITING past the
         [minstret_increment] read: this arm does not retire *)
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      rewrite !mbind0_ret.
      iApply swp_ret.
      iExists (wrap_post rs2 (register_lookup (R_bitvector_64 minstret)
                 (register_set (R_bitvector_64 PC)
                    (register_lookup (R_bitvector_64 nextPC) rs2) rs2))), rs2.
      iSplitR.
      { iPureIntro. unfold tsf_post. exists (Step_Pending_Interrupt (i, p)).
        split; [exact HQ|]. eexists. reflexivity. }
      unfold wrap_post.
      rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
      rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
      iFrame.
    - (* ---- Step_Fetch_Failure: deliver the fault, then the no-bump tail ---- *)
      cbn beta iota zeta delta [bits_of_virtaddr]. i_glue.
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                          hreg_frame_ro Df rs2 Dro ∗ R rs2)%I _
                with "[Harm] [-]").
      { iApply (swp_bind0_use (handle_exception xv ex) _
                  (fun _ => (hreg_frame rs2 Drw ∗
                             hreg_frame_ro Df rs2 Dro ∗ R rs2)%I)
                  _ with "Harm [-]").
        iIntros (u) "(Hrw & Hro & HR)".
        iApply (swp_mono with "[HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
        iSplitR; [done|]. iFrame. }
      iIntros (v0) "(-> & Hrw & Hro & HR)". i_glue.
      (* the tick, then [and_boolM (returnM false) _] SHORT-CIRCUITING past the
         [minstret_increment] read: this arm does not retire *)
      iApply (swp_bind0_use (tick_pc tt) _
                (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                _ with "[Hrw Hro] [-]").
      { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                  with "Hcert Hrw Hro"). }
      iIntros (u2) "[Hrw Hro]".
      unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
      rewrite !mbind0_ret.
      iApply swp_ret.
      iExists (wrap_post rs2 (register_lookup (R_bitvector_64 minstret)
                 (register_set (R_bitvector_64 PC)
                    (register_lookup (R_bitvector_64 nextPC) rs2) rs2))), rs2.
      iSplitR.
      { iPureIntro. unfold tsf_post. exists (Step_Fetch_Failure (Virtaddr xv, ex)).
        split; [exact HQ|]. eexists. reflexivity. }
      unfold wrap_post.
      rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
      rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
      iFrame.
    - (* ---- Step_Execute: four of the ten results are offered ---- *)
      destruct er as [ [] | ins | wr' | [] | [] | [[pr exc] epc] | [] | ce | de | [] ];
        [ | iDestruct "Harm" as %[] | | |
          iDestruct "Harm" as %[] | | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] | iDestruct "Harm" as %[]
        | iDestruct "Harm" as %[] ].
      + (* Retire_Success: the assert, then the tail WITH the bump *)
        iDestruct "Harm" as "(Hrw & Hro & HR)". i_glue.
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
        * iApply (swp_bind0_use _ _
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
          iApply swp_ret. iExists _, rs2. iSplitR.
          { iPureIntro. unfold tsf_post.
            exists (Step_Execute (Retire_Success tt, ib)).
            split; [exact HQ|]. eexists. reflexivity. }
          unfold wrap_post. iFrame.
        * iApply (swp_bind0_use _ _
                    (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                    with "[Hrw Hro] [-]").
          { iApply (swp_bind0_use _ _
                      (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I) _
                      with "[Hrw Hro] [-]").
            { iApply swp_ret. iFrame. }
            iIntros (u2') "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
          iIntros (u3) "[Hrw Hro]".
          iApply swp_ret.
          iExists (wrap_post rs2 (register_lookup (R_bitvector_64 minstret)
                     (register_set (R_bitvector_64 PC)
                        (register_lookup (R_bitvector_64 nextPC) rs2) rs2))), rs2.
          iSplitR.
          { iPureIntro. unfold tsf_post.
            exists (Step_Execute (Retire_Success tt, ib)).
            split; [exact HQ|]. eexists. reflexivity. }
          unfold wrap_post.
          rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
          rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
          iFrame.
      + (* Enter_Wait: the arm WRITES hart_state; no tick, no bump *)
        iDestruct "Harm" as "(%Hnop & Hrw & Hro & HR)".
        rewrite Hnop. i_glue. rewrite mbind0_ret.
        iApply (swp_bind_use _ _
                  (fun w => ⌜w = HART_WAITING (wr', ib)⌝ ∗
                     hreg_frame
                       (register_set hart_state (HART_WAITING (wr', ib)) rs2) Drw ∗
                     hreg_frame_ro Df
                       (register_set hart_state (HART_WAITING (wr', ib)) rs2) Dro ∗
                     R rs2)%I _
                  with "[Hrw Hro HR] [-]").
        { iApply (swp_bind0_use
                    (Defs.write_reg hart_state (HART_WAITING (wr', ib))) _
                    (fun _ => (hreg_frame
                        (register_set hart_state (HART_WAITING (wr', ib)) rs2) Drw ∗
                      hreg_frame_ro Df
                        (register_set hart_state (HART_WAITING (wr', ib)) rs2) Dro)%I)
                    _ with "[Hrw Hro] [-]").
          { iApply (swp_write_reg_owned Drw Dro Df rs2 hart_state
                      (HART_WAITING (wr', ib)) Hdisj HWhart
                      with "Hcert Hrw Hro"). }
          iIntros (u) "[Hrw Hro]".
          iApply (swp_mono with "[HR] [-]");
            [| iApply (swp_read_reg_pinned Drw Dro Df _ hart_state Hdisj HDhart
                         with "Hcert Hrw Hro") ].
          iIntros (w) "(-> & Hrw & Hro)". rewrite register_lookup_set.
          iSplitR; [done|]. iFrame. }
        iIntros (v) "(-> & Hrw & Hro & HR)". i_glue.
        iApply swp_ret.
        iExists (register_set hart_state (HART_WAITING (wr', ib)) rs2), rs2.
        iSplitR.
        { iPureIntro. unfold tsf_post.
          exists (Step_Execute (Enter_Wait wr', ib)).
          split; [exact HQ|]. split; [exact Hnop|reflexivity]. }
        iFrame.
      + (* Illegal_Instruction: deliver E_Illegal_Instr, then the no-bump tail *)
        i_glue.
        iApply (swp_bind_use _ _
                  (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)%I _
                  with "[Harm] [-]").
        { iApply (swp_bind0_use
                    (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt)) _
                    (fun _ => (hreg_frame rs2 Drw ∗
                               hreg_frame_ro Df rs2 Dro ∗ R rs2)%I)
                    _ with "Harm [-]").
          iIntros (u) "(Hrw & Hro & HR)".
          iApply (swp_mono with "[HR] [-]");
            [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                         with "Hcert Hrw Hro") ].
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
          iSplitR; [done|]. iFrame. }
        iIntros (v0) "(-> & Hrw & Hro & HR)". i_glue.
        (* the tick, then [and_boolM (returnM false) _] SHORT-CIRCUITING past the
           [minstret_increment] read: this arm does not retire *)
        iApply (swp_bind0_use (tick_pc tt) _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                    with "Hcert Hrw Hro"). }
        iIntros (u2) "[Hrw Hro]".
        unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
        rewrite !mbind0_ret.
        iApply swp_ret.
        iExists (wrap_post rs2 (register_lookup (R_bitvector_64 minstret)
                   (register_set (R_bitvector_64 PC)
                      (register_lookup (R_bitvector_64 nextPC) rs2) rs2))), rs2.
        iSplitR.
        { iPureIntro. unfold tsf_post. exists (Step_Execute (Illegal_Instruction tt, ib)).
          split; [exact HQ|]. eexists. reflexivity. }
        unfold wrap_post.
        rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
        rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
        iFrame.
      + (* Trap: the exception handler and its next-PC write, then no bump *)
        i_glue.
        iApply (swp_bind_use _ _
                  (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ R rs2)%I _
                  with "[Harm] [-]").
        { iApply (swp_bind0_use
                    (Defs.bind (exception_handler pr exc epc) set_next_pc) _
                    (fun _ => (hreg_frame rs2 Drw ∗
                               hreg_frame_ro Df rs2 Dro ∗ R rs2)%I)
                    _ with "Harm [-]").
          iIntros (u) "(Hrw & Hro & HR)".
          iApply (swp_mono with "[HR] [-]");
            [| iApply (swp_read_reg_pinned Drw Dro Df rs2 hart_state Hdisj HDhart
                         with "Hcert Hrw Hro") ].
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hhart2.
          iSplitR; [done|]. iFrame. }
        iIntros (v0) "(-> & Hrw & Hro & HR)". i_glue.
        (* the tick, then [and_boolM (returnM false) _] SHORT-CIRCUITING past the
           [minstret_increment] read: this arm does not retire *)
        iApply (swp_bind0_use (tick_pc tt) _
                  (fun _ => (hreg_frame _ Drw ∗ hreg_frame_ro Df _ Dro)%I)
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_tick_pc Drw Dro Df _ Hdisj HDnpc HWpc HDpc
                    with "Hcert Hrw Hro"). }
        iIntros (u2) "[Hrw Hro]".
        unfold Defs.and_boolM. rewrite /returnM mbind_ret. i_glue.
        rewrite !mbind0_ret.
        iApply swp_ret.
        iExists (wrap_post rs2 (register_lookup (R_bitvector_64 minstret)
                   (register_set (R_bitvector_64 PC)
                      (register_lookup (R_bitvector_64 nextPC) rs2) rs2))), rs2.
        iSplitR.
        { iPureIntro. unfold tsf_post. exists (Step_Execute (rv64d_types.Trap (pr, exc, epc), ib)).
          split; [exact HQ|]. eexists. reflexivity. }
        unfold wrap_post.
        rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
        rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
        iFrame.
  Qed.

  (* ================================================================== *)
  (* 4. THE BOUNDARY RULE: [WP Loop] from [WP Loop], all six arms.        *)
  (*                                                                    *)
  (* [swp_exec_step_any]'s wrapper verbatim -- [wp_loop_cycle] over       *)
  (* [swp_tick_wrap] over the body -- with [tsf_post Q] as the post-file  *)
  (* predicate in place of "[Q] of a [wrap_post]".                        *)
  (* ================================================================== *)
  Lemma swp_exec_step_full (Drw Dro : gset register)
      (Df : register -> dfrac) (rs1 rsA : regstate)
      (Q : Step -> regstate -> Prop) (Psi : regstate -> iProp Σ) :
    Drw ## Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (hart_state : register) ∈ Drw ->
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
    (forall st rs2, Q st rs2 ->
       register_lookup hart_state rs2 = HART_ACTIVE tt) ->
    (forall st rs2, Q st rs2 ->
       register_lookup (R_bool minstret_increment) rs2
       = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
           (register_lookup (R_bitvector_64 minstretcfg) rs1)
           (register_lookup cur_privilege rs1)) ->
    reg_agree_on (Drw ∪ Dro) (wrap_pre rs1) rsA ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs1 Drw -∗
    hreg_frame_ro Df rs1 Dro -∗
    (resv_frag cpu_id None -∗
     hreg_frame rsA Drw -∗ hreg_frame_ro Df rsA Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ rs2 : regstate, ⌜Q st rs2⌝ ∗
            match st with
            | Step_Execute (Retire_Success tt, _) =>
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Psi rs2
            | Step_Pending_Interrupt (i, p) =>
                swp (handle_interrupt i p)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi rs2)
            | Step_Execute (Illegal_Instruction tt, ib) =>
                swp (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt))
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi rs2)
            | Step_Execute (rv64d_types.Trap (p, exc, pcx), _) =>
                swp (Defs.bind (exception_handler p exc pcx) set_next_pc)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi rs2)
            | Step_Fetch_Failure (Virtaddr xv, e) =>
                swp (handle_exception xv e)
                  (fun _ => hreg_frame rs2 Drw ∗
                            hreg_frame_ro Df rs2 Dro ∗ Psi rs2)
            | Step_Execute (Enter_Wait wr, ib) =>
                ⌜wait_is_nop wr = false⌝ ∗
                hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Psi rs2
            | _ => False
            end)) -∗
    ▷ (∀ rs3 rs2 : regstate,
         ⌜∃ rsP : regstate, tsf_post Q rs2 rsP /\
            reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs3 rsP⌝ -∗
         hreg_frame rs3 Drw -∗ hreg_frame_ro Df rs3 Dro -∗ Psi rs2 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hdisj HWcy HWti HWip HDpriv HWhart HDhart HDmc HDcfg HWmi HDmi
      HWms HDms HWpc HDpc HDnpc Hhart HQhart HQmi Hpre.
    iIntros "#Hcert Hfrag Hrw Hro Hbody Hcont".
    iApply (wp_loop_cycle_ex Drw Dro Df
              (fun rsx => exists rs2 : regstate, tsf_post Q rs2 rsx)
              (fun rsx => ∃ rs2 : regstate, ⌜tsf_post Q rs2 rsx⌝ ∗ Psi rs2)%I
              Hdisj HWcy HWti HWip
              with "Hcert Hfrag [Hrw Hro Hbody] [Hcont]").
    2:{ iNext. iIntros (rs3 rsP) "%Hag Hrw Hro HPsi".
        destruct Hag as (_ & Hag).
        iDestruct "HPsi" as (rs2) "[%Hpost HPsi]".
        iApply ("Hcont" with "[%] Hrw Hro HPsi").
        exists rsP. split; [exact Hpost | exact Hag]. }
    iNext. iIntros "Hfrag".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_try_step_full Drw Dro Df rs1 Q Psi Hdisj HDpriv
                   HWhart HDhart HDmc HDcfg HWmi HDmi HWms HDms HWpc HDpc
                   HDnpc Hhart HQhart HQmi with "Hcert Hrw Hro [Hbody Hfrag]") ].
    { iIntros (u). iDestruct 1 as (rs3 rs2) "(%Hpost & Hrw & Hro & HPsi)".
      iExists rs3. iSplitR; [iPureIntro; by exists rs2|].
      iFrame "Hrw Hro". iExists rs2. iFrame "HPsi". iPureIntro. exact Hpost. }
    iIntros "Hrw Hro".
    rewrite (hreg_frame_ext _ rsA Drw (reg_agree_l _ _ _ _ Hpre)).
    rewrite (hreg_frame_ro_ext Df _ rsA Dro (reg_agree_r _ _ _ _ Hpre)).
    iApply ("Hbody" with "Hfrag Hrw Hro").
  Qed.

  (* ================================================================== *)
  (* 5. THE WAITING HART.                                                *)
  (* ================================================================== *)
  Lemma swp_try_step_waiting (Dr Dw : register -> bool)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (wr : WaitReason) (ib : SailStdpp.Values.mword 32) (R : iProp Σ) :
    Drw ## Dro ->
    (forall r, Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r, Dw r = true -> r ∈ Drw) ->
    Dr (R_bitvector_64 mip : register) = true ->
    Dr (R_bitvector_64 mie : register) = true ->
    Dw (hart_state : register) = true ->
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
    register_lookup hart_state rs = HART_WAITING (wr, ib) ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    R -∗
    swp (try_step 0 false)
      (fun _ => ∃ rs3 : regstate, ⌜wait_post (Drw ∪ Dro) rs rs3⌝ ∗
                  hreg_frame rs3 Drw ∗ hreg_frame_ro Df rs3 Dro ∗
                  resv_any cpu_id ∗ R)%I.
  Proof.
    intros Hdisj HDr HDw Hip Hie Hhs HDpriv HDhart HDmc HDcfg HWmi HDmi
      HWms HDms HWpc HDpc HDnpc Hhart.
    iIntros "#Hcert Hany Hrw Hro HR".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    (* ---- the prelude, verbatim from [swp_try_step_full] ---- *)
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
    i_peel. rewrite Hhart. fold (wrap_pre rs).
    (* ---- THE WAITING STEP.  [run_hart_waiting] is register-only, so it is
       ONE [swp_hmrun_of_exec] at [mm := ∅] off the reference state
       [MState (wrap_pre rs) ∅ dev0_state], where the rule's two hard-looking
       premises are [reg_agree_refl] and [∅ ⊆ _].  WHICH outcome the machine
       takes is not the caller's to know -- the wake test reads mip, which no
       continuation carries across a cycle, and [valid_reservation] is an
       opaque platform axiom -- so the three exec facts collapse into ONE
       pure disjunction here and the rule has exactly two Iris arms. ---- *)
    assert (Hempty : (∅ : gmap Arch.pa (bv 8))
                     ⊆ (MState (wrap_pre rs) ∅ dev0_state).(mem))
      by apply map_empty_subseteq.
    (* [bytes_own ∅] is [emp], hence PERSISTENT -- it lands in the □ context
       and is never consumed, so nothing below may reuse the name *)
    iAssert (bytes_own (∅ : gmap Arch.pa (bv 8))) with "[]" as "#Hemp";
      [ by rewrite /bytes_own big_sepM_empty |].
    assert (Hcase :
      exec (run_hart_waiting 0 wr ib false) (MState (wrap_pre rs) ∅ dev0_state)
        = Some (Step_Execute (Retire_Success tt, ib),
                set_reg (MState (wrap_pre rs) ∅ dev0_state) hart_state
                  (HART_ACTIVE tt))
      \/ exec (run_hart_waiting 0 wr ib false)
              (MState (wrap_pre rs) ∅ dev0_state)
         = Some (Step_Waiting wr, MState (wrap_pre rs) ∅ dev0_state)).
    { destruct (neq_vec (and_vec (register_lookup mip (wrap_pre rs))
                                 (register_lookup mie (wrap_pre rs)))
                        (zeros' 64)) eqn:Hwake.
      - left. by apply exec_run_hart_waiting_wake.
      - destruct (valid_reservation tt) eqn:Hvr.
        + right. apply exec_run_hart_waiting_stay; [exact Hwake | by left].
        + destruct wr.
          * right. apply exec_run_hart_waiting_stay; [exact Hwake | by right].
          * left. apply exec_run_hart_waiting_wake_resv;
              [exact Hwake | exact Hvr | by left].
          * left. apply exec_run_hart_waiting_wake_resv;
              [exact Hwake | exact Hvr | by right]. }
    destruct Hcase as [Hex | Hex].
    - (* ---- WAKE: hart_state := ACTIVE, then the ORDINARY retiring tail ---- *)
      iApply (swp_bind_use (run_hart_waiting 0 wr ib false) _ _ _
                with "[Hany Hrw Hro] [-]").
      { iApply (swp_hmrun_of_exec Dr Dw Drw Dro Df
                  (run_hart_waiting 0 wr ib false)
                  (MState (wrap_pre rs) ∅ dev0_state) _ _ (wrap_pre rs) ∅
                  Hdisj HDr HDw (reg_agree_refl _ _) Hempty
                  (goodmb_run_hart_waiting Dr Dw wr ib _ ∅ Hip Hie Hhs) Hex
                  with "Hcert Hany Hrw Hro Hemp"). }
      iIntros (stv) "(-> & Hpost)".
      iDestruct "Hpost" as (rs' mm') "(%Hag & _ & _ & Hrw & Hro & _ & Hany)".
      rewrite sregs_set_reg in Hag.
      assert (Hha : register_lookup hart_state rs' = HART_ACTIVE tt).
      { rewrite (Hag _ HDhart). apply register_lookup_set. }
      assert (Hmi2 : register_lookup (R_bool minstret_increment) rs'
                     = minstret_inc_flag
                         (register_lookup (R_bitvector_32 mcountinhibit) rs)
                         (register_lookup (R_bitvector_64 minstretcfg) rs)
                         (register_lookup cur_privilege rs)).
      { rewrite (Hag _ HDmi).
        rewrite (irrelevant_register_set (R_bool minstret_increment) hart_state);
          [ apply wrap_pre_mi | vm_compute; reflexivity ]. }
      i_glue.
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_ACTIVE tt⌝ ∗ hreg_frame rs' Drw ∗
                          hreg_frame_ro Df rs' Dro ∗ resv_any cpu_id ∗ R)%I _
                with "[Hrw Hro Hany HR] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗
                             resv_any cpu_id ∗ R)%I) _
                  with "[Hrw Hro Hany HR] [-]").
        { iApply (swp_bind_use (Defs.read_reg hart_state) _ _ _
                    with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                      with "Hcert Hrw Hro"). }
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hha.
          cbn beta iota zeta delta [hart_is_active Defs.assert_exp].
          iApply swp_ret. iFrame. }
        iIntros (u) "(Hrw & Hro & Hany & HR)".
        iApply (swp_mono with "[Hany HR] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs' hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hha.
        iSplitR; [done|]. iFrame. }
      iIntros (v0) "(-> & Hrw & Hro & Hany & HR)". i_glue.
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
            iIntros (v1) "(-> & Hrw & Hro)".
            iApply (swp_write_reg_owned Drw Dro Df _ _ _ Hdisj HWms
                      with "Hcert Hrw Hro"). }
          iIntros (u0) "[Hrw Hro]". i_glue. iApply swp_ret. iFrame. }
        iIntros (u1) "[Hrw Hro]".
        iApply swp_ret. iExists _. iSplitR.
        { iPureIntro. unfold wait_post. right. eexists rs', _.
          split; [exact Hag | reflexivity]. }
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
        iApply swp_ret.
        iExists (wrap_post rs' (register_lookup (R_bitvector_64 minstret)
                   (register_set (R_bitvector_64 PC)
                      (register_lookup (R_bitvector_64 nextPC) rs') rs'))).
        iSplitR.
        { iPureIntro. unfold wait_post. right. eexists rs', _.
          split; [exact Hag | reflexivity]. }
        unfold wrap_post.
        rewrite (hreg_frame_ext _ _ Drw (reg_set_id_agree_local Drw _ _)).
        rewrite (hreg_frame_ro_ext Df _ _ Dro (reg_set_id_agree_local Dro _ _)).
        iFrame.
    - (* ---- STAY: the whole cycle is the prelude's write; no tick, no bump ---- *)
      iApply (swp_bind_use (run_hart_waiting 0 wr ib false) _ _ _
                with "[Hany Hrw Hro] [-]").
      { iApply (swp_hmrun_of_exec Dr Dw Drw Dro Df
                  (run_hart_waiting 0 wr ib false)
                  (MState (wrap_pre rs) ∅ dev0_state) _ _ (wrap_pre rs) ∅
                  Hdisj HDr HDw (reg_agree_refl _ _) Hempty
                  (goodmb_run_hart_waiting Dr Dw wr ib _ ∅ Hip Hie Hhs) Hex
                  with "Hcert Hany Hrw Hro Hemp"). }
      iIntros (stv) "(-> & Hpost)".
      iDestruct "Hpost" as (rs' mm') "(%Hag & _ & _ & Hrw & Hro & _ & Hany)".
      cbn [sregs] in Hag.
      assert (Hhw : register_lookup hart_state rs' = HART_WAITING (wr, ib)).
      { rewrite (Hag _ HDhart).
        rewrite (wrap_pre_other hart_state rs);
          [ exact Hhart | vm_compute; reflexivity ]. }
      i_glue.
      iApply (swp_bind_use _ _
                (fun w => ⌜w = HART_WAITING (wr, ib)⌝ ∗ hreg_frame rs' Drw ∗
                          hreg_frame_ro Df rs' Dro)%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro)%I) _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind_use (Defs.read_reg hart_state) _ _ _
                    with "[Hrw Hro] [-]").
          { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                      with "Hcert Hrw Hro"). }
          iIntros (w) "(-> & Hrw & Hro)". rewrite Hhw.
          cbn beta iota zeta delta [hart_is_waiting Defs.assert_exp].
          iApply swp_ret. iFrame. }
        iIntros (u) "[Hrw Hro]".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_read_reg_pinned Drw Dro Df rs' hart_state Hdisj HDhart
                       with "Hcert Hrw Hro") ].
        iIntros (w) "(-> & Hrw & Hro)". rewrite Hhw.
        iSplitR; [done|]. iFrame. }
      iIntros (v0) "(-> & Hrw & Hro)". i_glue.
      iApply swp_ret. iExists rs'. iSplitR.
      { iPureIntro. unfold wait_post. by left. }
      iFrame.
  Qed.

  Lemma swp_exec_step_waiting (Dr Dw : register -> bool)
      (Drw Dro : gset register) (Df : register -> dfrac) (rs : regstate)
      (wr : WaitReason) (ib : SailStdpp.Values.mword 32) (Psi : iProp Σ) :
    Drw ## Dro ->
    (forall r, Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r, Dw r = true -> r ∈ Drw) ->
    Dr (R_bitvector_64 mip : register) = true ->
    Dr (R_bitvector_64 mie : register) = true ->
    Dw (hart_state : register) = true ->
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
    register_lookup hart_state rs = HART_WAITING (wr, ib) ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    Psi -∗
    ▷ (∀ rs3 : regstate,
         ⌜∃ rsP : regstate, wait_post (Drw ∪ Dro) rs rsP /\
            reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs3 rsP⌝ -∗
         hreg_frame rs3 Drw -∗ hreg_frame_ro Df rs3 Dro -∗
         resv_any cpu_id -∗ Psi -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hdisj HDr HDw Hip Hie Hhs HWcy HWti HWip HDpriv HDhart HDmc HDcfg
      HWmi HDmi HWms HDms HWpc HDpc HDnpc Hhart.
    iIntros "#Hcert Hany Hrw Hro HPsi Hcont".
    (* the plain [wp_loop_cycle], not the [_ex] twin: this rule has no body
       obligation, so the rider is a resource the CALLER hands in before the
       step and there is no post-file for it to be keyed on *)
    iApply (wp_loop_cycle Drw Dro Df (wait_post (Drw ∪ Dro) rs)
              (resv_any cpu_id ∗ Psi)%I Hdisj HWcy HWti HWip
              with "Hcert Hany [Hrw Hro HPsi] [Hcont]").
    2:{ iNext. iIntros (rs3) "%Hag Hrw Hro [Hany HPsi]".
        iApply ("Hcont" with "[%] Hrw Hro Hany HPsi"). exact Hag. }
    iNext. iIntros "Hfr".
    iDestruct (resv_any_intro cpu_id None with "Hfr") as "Hany".
    iApply (swp_try_step_waiting Dr Dw Drw Dro Df rs wr ib Psi Hdisj HDr HDw
              Hip Hie Hhs HDpriv HDhart HDmc HDcfg HWmi HDmi HWms HDms HWpc
              HDpc HDnpc Hhart with "Hcert Hany Hrw Hro HPsi").
  Qed.

End stepfull.
