/-
MachCSL: **the waiting hart at User**, as walks (lane U1-C; brief
`notes/design-rulings.md` G3; Rocq `HartStepFull.v` §2 and
`swp_try_step_waiting`, `UserStep.v` §2).

A user `WRS.NTO`/`WRS.STO` (Zawrs) returns `Enter_Wait`, and the cycle parks
the hart in `HART_WAITING (wr, ii)` without ticking the PC
(`UCycle.uc_finish_wait`).  Every later cycle of the parked hart is
`ucPrelude`, then `run_hart_waiting 0 wr ii ew` (`ew` the harness's
`exit_wait`, `riscvStep tick ew`), then the finish -- a whole cycle with NO
fetch, so the parked step is ONE walk (`uw_tryStep`):

* WAKE (`uwWake`): an interrupt is pending and enabled (sail-riscv 0.16: the
  effective word, PLIC wires included, `ucIp mip meip seip &&& mie ≠ 0`), the
  reservation went invalid under a `WRS` wait, or the harness forces the exit
  (`ew`; at User a forced `WRS` exit retires: `mstatus.TW = 0`, no
  virtualization).  The hart goes back to `HART_ACTIVE` and the waiting
  instruction RETIRES: the tick (`PC := nextPC`, the `pc + 4` the wait entry
  set up) and the `minstret` bump (`ucEpi true`).  Nothing traps here: the
  pending interrupt is taken by the NEXT cycle's dispatch, which at User is
  unmaskable (`UCycle.uc_dispatch`, `sepc` the PC after the wait instruction).
* STAY: nothing but the prelude moves (`ucPreS`: the `mip` refresh and the
  `minstret_increment` write); the cycle returns `true`.

A forced exit from a `WAIT_WFI` at User would trap (illegal instruction); a
user hart never parks in WFI (a user `wfi` is illegal at once), so the
statements exclude it (`wr = .WAIT_WFI → ew = false`).

`valid_reservation ()` is the platform's opaque `xv6_resv_is_valid` (a
`Bool`, not a register): the walk takes it as it is, and `uwWake` names it,
so both answers are covered.

The machine picks the outcome (the wake test reads `mip` and the PLIC
wires), so the Iris rule (`UCycleSwp.swp_uwTryStep`) lands in
`uwLand ew wr s meip seip`, a function of the state and the wires.
-/
import MachCSL.UCycle

noncomputable section

namespace MachCSL

open Sail Sail.ArchSem
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Register HartState Step ExecutionResult WaitReason

/-- A `WRS` wait (the reservation can wake it). -/
def uwIsWrs : WaitReason → Bool
  | .WAIT_WFI => false
  | .WAIT_WRS_STO => true
  | .WAIT_WRS_NTO => true

/-- **The wake test** of a parked hart: an enabled pending interrupt, an
invalid reservation under a `WRS` wait, or the harness's forced exit. -/
def uwWake (ew : Bool) (wr : WaitReason) (ip ie : BitVec 64) : Bool :=
  (ip &&& ie != 0#64) || (!Functions.valid_reservation () && uwIsWrs wr) || ew

/-- The step value of the parked body. -/
def uwStep (wr : WaitReason) (ii : instr_info) (wake : Bool) : Step :=
  if wake then Step_Execute (Retire_Success (), ii) else Step_Waiting wr

/-- The state after the parked body. -/
def uwBodyS (s : UWSt) (wake : Bool) : UWSt :=
  if wake then s.setR .hart_state (.HART_ACTIVE ()) else s

/-- What the parked body reads and writes (beyond `UcFoot`): `mip`/`mie`
(the wake test) and `mstatus` (a forced `WRS.NTO` exit's `TW` check). -/
structure UwFoot (D : UFoot) : Prop where
  rd_mip : D.Dr .mip = true
  rd_mie : D.Dr .mie = true
  rd_mstatus : D.Dr .mstatus = true

variable {D : UFoot}

/-- **The parked body** (Rocq `exec_run_hart_waiting_wake` /
`_wake_resv` / `_stay`, one equation): wake or stay, by `uwWake`, the PLIC
wires off the oracle's first two answers. -/
theorem uw_runHartWaiting (hD : UcFoot D) (hW : UwFoot D) (orc : UOrc) (s : UWSt) (wr : WaitReason)
    (ii : instr_info) (ew : Bool) (hm : UcMisa D s) (hpriv : s.file .cur_privilege = Privilege.User)
    (htw : _get_Mstatus_TW (s.file .mstatus) = 0#1) (hwfi : wr = .WAIT_WFI → ew = false) :
    runRW D orc s (run_hart_waiting 0 wr ii ew) =
      some (uwStep wr ii (uwWake ew wr (ucIp (s.file .mip) ((orc 0).reg .sig_meip) ((orc 1).reg .sig_seip))
          (s.file .mie)),
        uwBodyS s (uwWake ew wr (ucIp (s.file .mip) ((orc 0).reg .sig_meip) ((orc 1).reg .sig_seip))
          (s.file .mie)), orc.tail.tail) := by
  simp only [run_hart_waiting, shouldWakeForInterrupt, bind_assoc, pure_bind,
    uc_readMip hm hD.rd_hgeie hW.rd_mip hD.meip_nr hD.meip_any hD.seip_nr hD.seip_any,
    MachCSL.uxa_readReg_bind D _ _ _ _ hW.rd_mie, get_config_print_instr, Bool.false_eq_true, ite_false]
  unfold uwStep uwBodyS uwWake
  have ez : (zeros : BitVec 64) = 0#64 := rfl
  rw [ez]
  generalize ucIp (s.file .mip) ((orc 0).reg .sig_meip) ((orc 1).reg .sig_seip) = ip
  cases hw : (ip &&& s.file .mie != 0#64)
  · simp only [Bool.false_eq_true, ite_false, Bool.false_or]
    cases hv : Functions.valid_reservation () <;> cases wr <;> cases ew <;>
      simp only [uwIsWrs, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.or_false,
        Bool.or_true, Bool.false_eq_true, ite_false, ite_true] <;>
      first
      | rfl
      | exact ucRW_writeReg D _ s _ _ _ hD.wr_hs
      | exact absurd (hwfi rfl) (by decide)
      | (rw [ucRW_writeReg D _ s _ _ _ hD.wr_hs]
         simp only [MachCSL.uxa_readReg_bind D _ _ _ _ hD.rd_priv,
           UWSt.setR_file_other _ _ _ _ (show Register.cur_privilege ≠ .hart_state by decide), hpriv,
           show (Privilege.User == Privilege.Machine) = false from rfl, Bool.false_eq_true, ite_false,
           MachCSL.uxa_readReg_bind D _ _ _ _ hW.rd_mstatus,
           UWSt.setR_file_other _ _ _ _ (show Register.mstatus ≠ .hart_state by decide), htw,
           show (0#1 == 1#1) = false from rfl, inVirtualPrivilege, utr_virt_user, bind_assoc, pure_bind]
         rfl)
  · simp only [ite_true, Bool.true_or]
    exact ucRW_writeReg D _ s _ _ _ hD.wr_hs

/-- Where a parked cycle lands, given the PLIC wires the wake test saw:
`(true, prelude state)` if it stays; if it wakes, `(false, …)` with the hart
ACTIVE, ticked and bumped (the wait instruction retires). -/
def uwLand (ew : Bool) (wr : WaitReason) (s : UWSt) (meip seip : BitVec 1) : Bool × UWSt :=
  if uwWake ew wr (ucIp ((ucPreS s).file .mip) meip seip) ((ucPreS s).file .mie) then
    (false, ucEpi true ((ucPreS s).setR .hart_state (.HART_ACTIVE ())))
  else (true, ucPreS s)

/-- **One cycle of a parked hart** (Rocq `swp_try_step_waiting`'s walk):
the prelude, the parked body, the finish -- no fetch, ONE walk; the landing
is `uwLand` at the wires the wake test read. -/
theorem uw_tryStep (hD : UcFoot D) (hW : UwFoot D) (orc : UOrc) (s : UWSt) (wr : WaitReason)
    (ii : instr_info) (ew : Bool) (hm : UcMisa D s) (hpriv : s.file .cur_privilege = Privilege.User)
    (htw : _get_Mstatus_TW (s.file .mstatus) = 0#1) (hwfi : wr = .WAIT_WFI → ew = false)
    (h : s.file .hart_state = .HART_WAITING (wr, ii)) (hwt : s.file .written_trigger_index = none) :
    ∃ meip seip orc', runRW D orc s (try_step 0 ew) =
      some ((uwLand ew wr s meip seip).1, (uwLand ew wr s meip seip).2, orc') := by
  obtain ⟨o1, h1⟩ := uc_prelude hD orc s hm
  have hP : ∀ r, r ≠ .minstret_increment → r ≠ .mip → (ucPreS s).file r = s.file r :=
    fun r a b => ucPreS_file_other s r a b
  rw [uc_tryStep_eq, runRW_bind_some D _ _ orc o1 s (ucPreS s) _ h1, h]
  show ∃ meip seip orc', runRW D o1 (ucPreS s) (run_hart_waiting 0 wr ii ew >>= ucFinish) = _
  rw [runRW_bind_some D _ _ o1 o1.tail.tail _ _ _ (uw_runHartWaiting hD hW o1 (ucPreS s) wr ii ew hm.preS
    (by rw [hP _ (by decide) (by decide), hpriv]) (by rw [hP _ (by decide) (by decide), htw]) hwfi)]
  refine ⟨(o1 0).reg .sig_meip, (o1 1).reg .sig_seip, o1.tail.tail, ?_⟩
  unfold uwLand uwStep uwBodyS
  cases hw : uwWake ew wr (ucIp ((ucPreS s).file .mip) ((o1 0).reg .sig_meip) ((o1 1).reg .sig_seip))
      ((ucPreS s).file .mie)
  · simp only [Bool.false_eq_true, ite_false]
    exact uc_finish_waiting hD _ _ wr wr ii (by rw [hP _ (by decide) (by decide), h])
  · simp only [ite_true]
    exact uc_finish_retire hD _ _ ii (UWSt.setR_file_same _ _ _)
      (by rw [UWSt.setR_file_other _ _ _ _ (by decide), hP _ (by decide) (by decide), hwt])

end MachCSL
