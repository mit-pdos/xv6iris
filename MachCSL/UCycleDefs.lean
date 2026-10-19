/-
MachCSL: the SHAPE of one machine cycle, as the user tier cuts it (lane U1-C;
brief `notes/design-rulings.md` G3; Rocq `RiscvTryStep.v` /
`HartStepFull.v` / `HartRunFull.v`).

`try_step 0 ew` is one `do` block with two join points and an early-return
block (`run_hart_active` is `SailME.run`).  The walker (`URunRW`) composes
facts by the bind law, so the cycle is first re-stated, once and by
equations, as a chain of named stretches:

    try_step 0 ew
      = ucPrelude >>= fun hs => ucBody ew hs >>= ucFinish         (uc_tryStep_eq)
    ucFinish st = ucArm st >>= fun _ => ucEpilogue (ucRetired st)  (by definition)
    run_hart_active 0
      = ucDispatch >>= fun o => match o with
          | some ip => pure (Step_Pending_Interrupt ip)
          | none    => ucPreFetch >>= fun pf =>
                         fetch () >>= ucAfterFetch pf.1 pf.2       (uc_runHartActive_eq)

* `ucPrelude` -- sail-riscv 0.16's per-cycle `mip` refresh (`update_mip`: the
  CLINT's software and timer interrupts, the Sstc compare), then
  `minstret_increment := should_inc_minstret priv`, then the `hart_state` read
  that picks the body;
* `ucBody ew` -- `run_hart_waiting` (a parked hart; `ew` is the harness's
  `exit_wait`, `riscvStep tick ew`) or `run_hart_active`;
* `ucArm st` -- the model's per-step match (Rocq's six arms: the interrupt
  trap, the fetch fault, the execute trap, the illegal instruction, the wait
  entry, the retire assertion; the others are the Sdtrig triggers, the
  extension hooks and the chained-`ExecuteAs` error);
* `ucEpilogue retired` -- the second `hart_state` read: a WAITING hart
  returns `true` (no tick); an ACTIVE one ticks the PC, bumps `minstret`
  iff `retired` and `minstret_increment`, clears `written_event_index` and
  checks `written_trigger_index = none` (`update_triggers`, Sdtrig off);
* `ucDispatch` -- the (disabled) pending-trigger check's privilege read, then
  the privilege read and `dispatchInterrupt`;
* `ucPreFetch` -- the (disabled) fetch-address trigger check's reads, the
  fetch privilege and the breakpoint-reentrancy check (`prevent_reentrance`);
* `ucAfterFetch fp ftr fr` -- `run_hart_active` after the fetch: the fetch
  shape (fault / base / compressed), the (disabled) fetch-instruction trigger
  check's reads, decode, the landing-pad check, the `Ext_Zca` gate,
  `nextPC := PC + len`, execute and its one `ExecuteAs` redirect
  (`ucExecAs`, which also names the executed instruction), and the step's
  `instr_info` (`ucII`).  The Sdtrig checks are off (`hartSupports Ext_Sdtrig
  = false`), so their early returns are dead (`uc_noPendingTrigger`,
  `uc_noMemTrigger`) and this stretch is plain `SailM`.

The fetch is the one stretch the walker does not take (fetch reads are their
own node rule, Rocq parity), so the cycle is cut AT it: everything before is a
walk (`ucPrelude`, `ucDispatch`, `ucPreFetch`), the fetch is a node
obligation, and everything after is a walk again (`ucAfterFetch fp ftr fr >>=
ucFinish`).

Every definition here is the model's own text (checked by the equations), up
to the dead Sdtrig returns and the disabled `print` configuration; nothing is
assumed about the model.
-/
import MachCSL.UExecAluGpr

noncomputable section

namespace MachCSL

open Sail Sail.ArchSem
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Register HartState Step ExecutionResult FetchResult ExceptionType

/-! ## The Sdtrig checks are off -/

/-- The pending-trigger check finds nothing (Sdtrig off). -/
theorem uc_noPendingTrigger (p : Privilege) : find_highest_priority_pending_trigger p = pure none := by
  unfold find_highest_priority_pending_trigger currentlyEnabled
  simp only [hartSupports_Ext_Sdtrig, LeanRV64D.not, pure_bind, Bool.not_false, ite_true]

/-- The memory-trigger checks before an access find nothing (Sdtrig off). -/
theorem uc_noMemTrigger (p : Privilege) (x : MemoryTriggerPayload) : match_memory_trigger_before p x = pure none := by
  unfold match_memory_trigger_before currentlyEnabled
  simp only [hartSupports_Ext_Sdtrig, LeanRV64D.not, pure_bind, Bool.not_false, ite_true]

/-- The icount triggers do nothing (Sdtrig off). -/
theorem uc_noIcount (p : Privilege) (b : Bool) : match_icount_triggers p b = pure () := by
  unfold match_icount_triggers currentlyEnabled
  simp only [hartSupports_Ext_Sdtrig, LeanRV64D.not, pure_bind, Bool.not_false, ite_true]

/-! ## The stretches -/

/-- The cycle's prelude: the `mip` refresh, `minstret_increment :=
should_inc_minstret priv`, then the `hart_state` read. -/
def ucPrelude : SailM HartState := do
  update_mip ()
  writeReg minstret_increment (← should_inc_minstret (← readReg cur_privilege))
  readReg hart_state

/-- The step body: a parked hart's `run_hart_waiting` (at the harness's
`exit_wait`) or an active hart's `run_hart_active`. -/
noncomputable def ucBody (ew : Bool) (hs : HartState) : SailM Step :=
  match hs with
  | .HART_WAITING (wr, ii) => run_hart_waiting 0 wr ii ew
  | .HART_ACTIVE () => run_hart_active 0

/-- The model's per-step match of `try_step` (its first half): the trigger and trap
handlers, the assertions, the wait entry. -/
def ucArm (step_val : Step) : SailM Unit := do
  match step_val with
  | .Step_Pending_Trigger pti =>
    (do
      let _ : Unit :=
        if ((get_config_print_trigger ()) : Bool)
        then
          (let (_, idx, _) := pti
          (print_endline (HAppend.hAppend "Handling trigger at index #" (Int.repr idx))))
        else ()
      (handle_pending_trigger pti))
  | .Step_Pending_Interrupt (intr, priv) =>
    (do
      let _ : Unit :=
        if ((get_config_print_instr ()) : Bool)
        then (print_bits "Handling interrupt: " (interruptType_bits_forwards intr))
        else ()
      (handle_interrupt intr priv))
  | .Step_Fetch_Trigger pti =>
    (do
      let _ : Unit :=
        if ((get_config_print_trigger ()) : Bool)
        then
          (let (_, idx, _) := pti
          (print_endline (HAppend.hAppend "Handling trigger at index #" (Int.repr idx))))
        else ()
      (fire_pending_before_triggers pti)
      (handle_pending_trigger pti))
  | .Step_Ext_Fetch_Failure e => (pure (ext_handle_fetch_check_error e))
  | .Step_Fetch_Failure e => (handle_exception e)
  | .Step_Waiting _ =>
    sail_assert (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
  | .Step_Execute (.Retire_Success (), instr_info) =>
    (do
      sail_assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:314.39-314.40"
      (match_icount_triggers instr_info.fetch_privilege instr_info.fetch_trigger_reentrance))
  | .Step_Execute (.ExecuteAs _, _) =>
    (internal_error "postlude/step.sail" 320
      "Multiple chained ExecuteAs (only one redirection is supported).")
  | .Step_Execute (.Trap (priv, ctx, pc), instr_info) =>
    (do
      let ctx ← do (transform_exception_context ctx instr_info)
      (set_next_pc (← (exception_handler priv ctx pc))))
  | .Step_Execute (.Illegal_Instruction (), instr_info) =>
    (handle_exception
      (make_instr_exception_context (E_Illegal_Instr ()) (zero_extend (m := 64) instr_info.instbits)))
  | .Step_Execute (.Virtual_Instruction (), instr_info) =>
    (handle_exception
      (make_instr_exception_context (E_Virtual_Instr ()) (zero_extend (m := 64) instr_info.instbits)))
  | .Step_Execute (.Enter_Wait wr, instr_info) =>
    (do
      if ((wait_is_nop wr) : Bool)
      then
        (do
          sail_assert (hart_is_active (← readReg hart_state)) "postlude/step.sail:333.41-333.42"
          (match_icount_triggers instr_info.fetch_privilege instr_info.fetch_trigger_reentrance))
      else
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (discard <| pure (print_endline
                (HAppend.hAppend "entering "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_WAITING (wr, instr_info))))
  | .Step_Execute (.PendingTrigger pti, _) =>
    (do
      let _ : Unit :=
        if ((get_config_print_trigger ()) : Bool)
        then
          (let (_, idx, _) := pti
          (print_endline (HAppend.hAppend "Handling trigger at index #" (Int.repr idx))))
        else ()
      (fire_pending_before_triggers pti)
      (handle_pending_trigger pti))
  | .Step_Execute (.Ext_CSR_Check_Failure (), _) => (pure (ext_check_CSR_fail ()))
  | .Step_Execute (.Ext_ControlAddr_Check_Failure e, _) => (pure (ext_handle_control_check_error e))
  | .Step_Execute (.Ext_DataAddr_Check_Failure e, _) => (pure (ext_handle_data_check_error e))
  | .Step_Execute (.Ext_XRET_Priv_Failure (), _) => (pure (ext_fail_xret_priv ()))

/-- Whether the step retired an instruction (the model's `retired`). -/
def ucRetired (step_val : Step) : Bool :=
  match step_val with
  | .Step_Execute (.Retire_Success (), _) => true
  | .Step_Execute (.Enter_Wait wr, _) =>
    (if ((wait_is_nop wr) : Bool)
    then true
    else false)
  | _ => false

/-- The epilogue of `try_step` (its second half): a WAITING hart returns
`true`; an ACTIVE one ticks the PC, bumps `minstret` iff `retired` and
`minstret_increment`, runs the event and trigger bookkeeping, and returns `false`. -/
def ucEpilogue (retired : Bool) : SailM Bool := do
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure true)
  | .HART_ACTIVE () =>
    (do
      (tick_pc ())
      if ((← do
           if (retired : Bool)
           then readReg minstret_increment
           else (pure false)) : Bool)
      then writeReg minstret (BitVec.addInt (← readReg minstret) 1)
      else (pure ())
      (dispatch_events ())
      (clear_written_event_index ())
      (update_triggers ())
      if ((get_config_rvfi ()) : Bool)
      then
        writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 127 64
          (zero_extend (m := 64) (← (get_arch_pc ()))))
      else (pure ())
      let _ : Unit := (ext_post_step_hook ())
      let _ : Unit :=
        if (retired : Bool)
        then (instret_callback ())
        else ()
      (pure false))


/-- The rest of the cycle once the step value is known. -/
def ucFinish (st : Step) : SailM Bool :=
  ucArm st >>= fun _ => ucEpilogue (ucRetired st)

/-- **The cycle, cut into stretches** (Rocq `RiscvTryStep`'s reductions). -/
theorem uc_tryStep_eq (ew : Bool) : try_step 0 ew = ucPrelude >>= fun hs => ucBody ew hs >>= ucFinish := by
  simp only [try_step, ucPrelude, ucBody, bind_assoc]
  congr 1; funext u; congr 1; funext p; congr 1; funext b; congr 1; funext u'; congr 1; funext hs
  congr 1; funext st
  cases st with
  | Step_Execute p =>
    obtain ⟨r, ii⟩ := p
    cases r <;> simp only [ucFinish, ucArm, ucRetired, ucEpilogue, bind_assoc, pure_bind] <;> rfl
  | _ => simp only [ucFinish, ucArm, ucRetired, ucEpilogue, bind_assoc, pure_bind] <;> rfl

/-- The dispatch stretch of `run_hart_active`: the (disabled) pending-trigger
check's privilege read, then the privilege read and `dispatchInterrupt`. -/
def ucDispatch : SailM (Option (InterruptType × Privilege)) := do
  let _ ← readReg cur_privilege
  dispatchInterrupt (← readReg cur_privilege)

/-- The stretch between the dispatch and the fetch: the (disabled)
fetch-address trigger check's reads, the fetch privilege and the
breakpoint-reentrancy check. -/
def ucPreFetch : SailM (Privilege × Bool) := do
  let _ ← readReg cur_privilege
  let _ ← readReg PC
  let fp ← readReg cur_privilege
  let ftr ← prevent_reentrance Trig_Action.TA_Breakpoint fp
  pure (fp, ftr)

/-- The step's `instr_info` record. -/
def ucII (fp : Privilege) (ftr : Bool) (fi : instruction) (ei : Option instruction) (ib : BitVec 32)
    (c : Bool) : instr_info :=
  { fetch_privilege := fp
    fetch_trigger_reentrance := ftr
    fetched_instruction := fi
    executed_instruction := ei
    instbits := ib
    compressed := c }

/-- Execute with its one `ExecuteAs` redirect, naming the executed
instruction (the model's inner block; `uxaExecAs` without the name). -/
def ucExecAs (i : instruction) : SailM (Option instruction × ExecutionResult) := do
  match ← execute i with
  | .ExecuteAs j => pure (some j, ← execute j)
  | r => pure (some i, r)

/-- `run_hart_active` after the fetch (plain `SailM`: the Sdtrig early return
past the fetch is dead). -/
noncomputable def ucAfterFetch (fp : Privilege) (ftr : Bool) (fr : FetchResult) : SailM Step := do
  match (ext_fetch_hook fr) with
  | .F_Ext_Error e => (pure (Step_Ext_Fetch_Failure e))
  | .F_Error e => (pure (Step_Fetch_Failure e))
  | .F_RVC h =>
    (do
      let _ ← readReg cur_privilege
      let _ ← readReg PC
      let instbits : instbits := (zero_extend (m := 32) h)
      let fi ← ext_decode_compressed h
      if ((← (is_landing_pad_expected ())) : Bool)
      then
        (do
          let r ← trap (make_landing_pad_exception ())
          (pure (Step_Execute (r, ucII fp ftr fi none instbits true))))
      else
        (do
          if ((← (currentlyEnabled extension.Ext_Zca)) : Bool)
          then
            (do
              writeReg nextPC (BitVec.addInt (← readReg PC) 2)
              let (ei, result) ← ucExecAs fi
              (pure (Step_Execute (result, ucII fp ftr fi ei instbits true))))
          else (pure (Step_Execute ((Illegal_Instruction ()), ucII fp ftr fi none instbits true)))))
  | .F_Base w =>
    (do
      let _ ← readReg cur_privilege
      let _ ← readReg PC
      let instbits : instbits := (zero_extend (m := 32) w)
      let fi ← ext_decode w
      if (((← (is_landing_pad_expected ())) && (LeanRV64D.not (is_lpad_instruction fi))) : Bool)
      then
        (do
          let r ← trap (make_landing_pad_exception ())
          (pure (Step_Execute (r, ucII fp ftr fi none instbits false))))
      else
        (do
          writeReg nextPC (BitVec.addInt (← readReg PC) 4)
          let (ei, result) ← ucExecAs fi
          (pure (Step_Execute (result, ucII fp ftr fi ei instbits false)))))

set_option linter.unusedSimpArgs false in
/-- **`run_hart_active`, cut at the fetch** (Rocq `HartRunFull`'s
`swp_run_hart_active_res` node order): the dispatch, then either the
interrupt step (an early return) or the pre-fetch reads, the fetch and the
rest. -/
theorem uc_runHartActive_eq : run_hart_active 0 =
    ucDispatch >>= fun o => match o with
      | some ip => pure (Step_Pending_Interrupt ip)
      | none => ucPreFetch >>= fun pf => fetch () >>= ucAfterFetch pf.1 pf.2 := by
  simp only [run_hart_active, ucDispatch, ucPreFetch, bind_assoc, uc_noPendingTrigger, uc_noMemTrigger,
    run_lift_bind, pure_bind]
  congr 1; funext u; congr 1; funext p; congr 1; funext o
  cases o with
  | some ip =>
    obtain ⟨i, q⟩ := ip
    simp only [run_throw_bind]
  | none =>
    simp only [pure_bind, run_lift_bind, bind_assoc, run_lift, run_pure, ucAfterFetch]
    congr 1; funext u1; congr 1; funext u2; congr 1; funext fp; congr 1; funext ftr; congr 1; funext fr
    cases fr <;> simp only [ext_fetch_hook, get_config_print_instr, Bool.false_eq_true, ite_false, pure_bind,
      run_lift_bind, bind_assoc, run_lift, run_pure, ucAfterFetch, ucExecAs, ucII]
    all_goals try rfl
    all_goals (congr 1; funext u3; congr 1; funext u4; congr 1; funext fi; congr 1; funext lp)
    · by_cases hlp : (lp && LeanRV64D.not (is_lpad_instruction fi)) = true
      · rw [ite_eq_left hlp, ite_eq_left hlp]
        simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
      · rw [ite_eq_right hlp, ite_eq_right hlp]
        simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
        congr 1; funext pc; congr 1; funext u; congr 1; funext r
        cases r <;> simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
    · by_cases hlp : lp = true
      · rw [ite_eq_left hlp, ite_eq_left hlp]
        simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
      · rw [ite_eq_right hlp, ite_eq_right hlp]
        simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
        congr 1; funext z
        by_cases hz : z = true
        · rw [ite_eq_left hz, ite_eq_left hz]
          simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
          congr 1; funext pc; congr 1; funext u; congr 1; funext r
          cases r <;> simp only [run_lift_bind, run_pure, bind_assoc, pure_bind]
        · rw [ite_eq_right hz, ite_eq_right hz]
          simp only [run_pure]

end MachCSL
