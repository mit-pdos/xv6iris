(* UmodeStep.v -- the generic NON-RETIRING machine step: try_step around any
   dispatch arm that does not retire (pending interrupt, fetch failure,
   execute-level trap, illegal instruction, ...).

   WpIntrCore's [exec_riscv_step_interrupt] threads the try_step wrapper
   around exactly the Step_Pending_Interrupt arm.  The user-mode WP needs
   the same wrapper around EVERY trap-ish arm -- user code re-enters the
   kernel via fetch page faults (Step_Fetch_Failure), data-access faults
   and ecall (Step_Execute (Trap ...)), and undecodable words
   (Step_Execute (Illegal_Instruction ...)).  Rather than clone the
   threading per arm:

     [try_step_dispatch] / [step_retired] : the dispatch match and the
         retired computation of try_step, packaged as functions of the
         [Step] value.
     [exec_riscv_step_notretire] : ONE lemma, by case analysis on the
         [Step] value: if run_hart_active yields [sv], the dispatch body
         of [sv] runs to [s_trap], [sv] does not retire, and the hart
         stays ACTIVE, then the whole riscv_step runs to the PC-ticked
         [s_trap] with NO minstret bump.  Subsumes the interrupt arm.
     [wp_exec_step_trapish_inv] : the minstret_inv Iris engine on top,
         generalizing WpIntrCore's [wp_exec_step_interrupt_inv]: the
         caller picks the arm by supplying the two exec facts; the
         continuation comes back UNDER A LATER (for Löb).             *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep.
Require Import MinstretInv.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The dispatch body and the retired computation of try_step, as       *)
(*    functions of the Step value (verbatim copies of the match arms).    *)
(* ===================================================================== *)

Definition try_step_dispatch (step_val : Step) : M unit :=
  match step_val with
  | Step_Pending_Interrupt (intr, priv) =>
     let '(_) :=
       (if get_config_print_instr (tt) then
          print_bits ("Handling interrupt: ") ((interruptType_bits_forwards (intr)))
        else tt)
        : unit in
     (handle_interrupt (intr) (priv))
      : M (unit)
  | Step_Ext_Fetch_Failure e => returnM ((ext_handle_fetch_check_error (e)))
  | Step_Fetch_Failure (vaddr, e) =>
     (handle_exception ((bits_of_virtaddr (vaddr))) (e))  : M (unit)
  | Step_Waiting _ =>
     read_reg hart_state >>= fun (w__5 : HartState) =>
     (assert_exp (hart_is_waiting (w__5)) "cannot be Waiting in a non-Wait state")
      : M (unit)
  | Step_Execute (Retire_Success tt, _) =>
     read_reg hart_state >>= fun (w__6 : HartState) =>
     (assert_exp (hart_is_active (w__6)) "postlude/step.sail:219.74-219.75")
      : M (unit)
  | Step_Execute (ExecuteAs _, _) =>
     (internal_error ("postlude/step.sail") (223)
        ("Multiple chained ExecuteAs (only one redirection is supported)."))
      : M (unit)
  | Step_Execute (rv64d_types.Trap (tpriv, texc, tpc), _) =>
     (exception_handler (tpriv) (texc) (tpc)) >>= fun (w__7 : mword 64) =>
     (set_next_pc (w__7))
      : M (unit)
  | Step_Execute (Illegal_Instruction tt, instbits) =>
     (handle_exception ((zero_extend' (64) (instbits))) ((E_Illegal_Instr (tt))))  : M (unit)
  | Step_Execute (Virtual_Instruction tt, instbits) =>
     (handle_exception ((zero_extend' (64) (instbits))) ((E_Virtual_Instr (tt))))  : M (unit)
  | Step_Execute (Enter_Wait wr, instbits) =>
     (if wait_is_nop (wr) then
        read_reg hart_state >>= fun (w__8 : HartState) =>
        (assert_exp (hart_is_active (w__8)) "postlude/step.sail:232.41-232.42")
         : M (unit)
      else
        (if get_config_print_instr (tt) then
           ((read_reg PC)  : M (mword 64)) >>= fun (w__9 : mword 64) =>
           returnM ((print_endline
                       ((String.append ("entering ")
                           ((String.append ((wait_name_forwards (wr)))
                               ((String.append (" state at PC ") ((string_of_bits (w__9)))))))))))
         else returnM (tt)) >>
        write_reg hart_state (HART_WAITING ((wr, instbits)))
         : M (unit))
      : M (unit)
  | Step_Execute (Ext_CSR_Check_Failure tt, _) => returnM ((ext_check_CSR_fail (tt)))
  | Step_Execute (Ext_ControlAddr_Check_Failure e, _) =>
     returnM ((ext_handle_control_check_error (e)))
  | Step_Execute (Ext_DataAddr_Check_Failure e, _) => returnM ((ext_handle_data_check_error (e)))
  | Step_Execute (Ext_XRET_Priv_Failure tt, _) => returnM ((ext_fail_xret_priv (tt)))
  end.

Definition step_retired (step_val : Step) : bool :=
  match step_val with
  | Step_Execute (Retire_Success tt, g__0) => true
  | Step_Execute (Enter_Wait wr, g__1) => if wait_is_nop (wr) then true else false
  | _ => false
  end.

(* ===================================================================== *)
(* §2 The generic non-retiring step.                                      *)
(* ===================================================================== *)

Section StepNotretire.
  Context (s : mstate) (sv : Step) (s_x s_trap : mstate) (b : bool).

  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha : exec (run_hart_active 0) s_a = Some (sv, s_x).
  Hypothesis Hdisp : exec (try_step_dispatch sv) s_x = Some (tt, s_trap).
  Hypothesis Hret : step_retired sv = false.
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  (* the shared epilogue: from [exec TAIL s_trap] where TAIL = read
     hart_state -> ACTIVE -> tick_pc -> retired=false (no minstret bump) ->
     skip rvfi -> return false. *)
  Ltac step_epilogue Hhart_trap_h s_tick_t :=
    rewrite Hhart_trap_h; cbn beta iota;
    erewrite exec_bind0_Some; [ | apply exec_tick_pc ];
    erewrite exec_bind_Some;
    [ | unfold Defs.and_boolM;
        erewrite exec_bind_Some; [ | apply exec_returnM ];
        cbn beta iota; apply exec_returnM ];
    cbn beta iota; apply exec_returnm.

  Lemma exec_riscv_step_notretire : exec riscv_step s = Some (tt, s_tick).
  Proof using Hsi Hhart_a Hha Hdisp Hret Hhart_trap.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    unfold try_step_dispatch in Hdisp; unfold step_retired in Hret.
    change (get_config_print_instr tt) with false in Hdisp |- *.
    destruct sv as [ [intr priv] | eerr | [vaddr exc] | [res instbits] | wr ].
    - (* Step_Pending_Interrupt *)
      cbn match in Hdisp |- *. cbv zeta in Hdisp |- *.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
          apply (exec_read_reg hart_state s_trap). }
      cbn beta iota. step_epilogue Hhart_trap s_tick.
    - (* Step_Ext_Fetch_Failure *)
      cbn match in Hdisp |- *. cbv zeta.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
          apply (exec_read_reg hart_state s_trap). }
      cbn beta iota. step_epilogue Hhart_trap s_tick.
    - (* Step_Fetch_Failure *)
      cbn match in Hdisp |- *. cbv zeta.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
          apply (exec_read_reg hart_state s_trap). }
      cbn beta iota. step_epilogue Hhart_trap s_tick.
    - (* Step_Execute *)
      destruct res as [ [] | inst | wrr | [] | [] | [[tpriv texc] tpc] | [] | ce | de | [] ].
      + (* Retire_Success: contradicts step_retired = false *)
        discriminate Hret.
      + (* ExecuteAs: dispatch is an internal_error, no successful exec *)
        exfalso. cbn match in Hdisp.
        unfold internal_error in Hdisp. cbn in Hdisp. discriminate Hdisp.
      + (* Enter_Wait *)
        cbn match in Hdisp, Hret |- *.
        destruct (wait_is_nop wrr) eqn:Hnop; [ discriminate Hret | ].
        cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Illegal_Instruction *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Virtual_Instruction *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Trap *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Ext_CSR_Check_Failure *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Ext_ControlAddr_Check_Failure *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Ext_DataAddr_Check_Failure *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
      + (* Ext_XRET_Priv_Failure *)
        cbn match in Hdisp |- *. cbv zeta.
        erewrite exec_bind_Some.
        2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
            apply (exec_read_reg hart_state s_trap). }
        cbn beta iota. step_epilogue Hhart_trap s_tick.
    - (* Step_Waiting *)
      cbn match in Hdisp |- *. cbv zeta.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind0_Some. 2:{ exact Hdisp. }
          apply (exec_read_reg hart_state s_trap). }
      cbn beta iota. step_epilogue Hhart_trap s_tick.
  Qed.
End StepNotretire.

(* ===================================================================== *)
(* §3 The Iris engine: one machine step through a NON-RETIRING dispatch   *)
(*    arm.  Generalizes WpIntrCore's [wp_exec_step_interrupt_inv]: the    *)
(*    caller picks the arm by supplying [sv] and the two exec facts.      *)
(*    The continuation comes back UNDER A LATER (Löb strips it).          *)
(* ===================================================================== *)
Section WpTrapishEngine.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma wp_exec_step_trapish_inv E Φ {dq : dfrac} :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (sv : Step) (s_x s_trap : mstate),
         ⌜ exec (run_hart_active 0) σ = Some (sv, s_x) ⌝ ∗
         ⌜ exec (try_step_dispatch sv) s_x = Some (tt, s_trap) ⌝ ∗
         ⌜ step_retired sv = false ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
         mstate_interp s_trap ∗
         ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
            WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv Hhs H".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as (sv s_x s_trap) "(%Hha & %Hdisp & %Hret & Hpc & [Hreg Hmem] & Hcont)".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
    assert (Hhart_a :
      register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
        = HART_ACTIVE tt).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    iModIntro. iExists _. iSplitR.
    { iPureIntro.
      exact (exec_riscv_step_notretire σ sv s_x s_trap b
               Hsi Hhart_a Hha Hdisp Hret Hhart_trap). }
    iNext.
    iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
    iSplitL "Hmst Hmi".
    { iExists mst, b. iFrame. }
    iApply ("Hcont" with "Hhs Hpc").
  Qed.

End WpTrapishEngine.
