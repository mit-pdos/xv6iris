/-
Weak: the model-keyed `exec` facts the weak tier consumes (Rocq
`RiscvExec.v` §"exec_riscv_step_*" and `ExecCommon.v`), and the
`decide +kernel` evaluation test of a closed instruction step.

Rocq: `iris/RiscvExec.v` (the `exec_riscv_step_tick`, `exec_tick_pc`,
`StepHartActive`, `exec_should_inc_minstret_Some` part) and
`iris/ExecCommon.v` @ xxvzwolszwmp (1cc222280).

The Rocq header of `ExecCommon.v`, in substance: "shared Sail
symbolic-executor reduction facts: [exec e s = Some (v, s')] lemmas, the
instruction-word constants they are keyed by, and the two dispatch-peeling
tactics … There is NO weakest precondition here … Facts that are keyed only by
the model, not by a privilege mode or an instruction family, belong here."

Every statement is about `Weak.exec` (`Weak/Exec.lean`) over the Lean model
(sail-riscv `070832a1`, `-D SYMBOLIC`).

**Deviations from Rocq.**
1. Bit-vector guards are stated in the Lean model's own spelling (Rocq
   `eq_vec (access_vec_dec t 0) 'b"0" = true` ↦ `(BitVec.access t 0 == 0#1) = true`;
   Rocq `eq_vec (_get_Misa_U …) 'b"1"` ↦ `(_get_Misa_U … == 1#1) = true`), and
   registers by their Lean names (`register_lookup r s.(sregs)` ↦ `s.regs r`).
2. Lean's `hartSupports` is a pure `Bool` (Rocq's was monadic), so Rocq
   `exec_hartSupports_X : exec (hartSupports Ext_X) s = Some (true, s)` become
   `hartSupportsX : hartSupports .Ext_X = true`.
3. `exec_wX_bits_at`: Rocq's hypothesis names the target register as an
   `R_bitvector_64 r` with `regval_into_reg v`; Lean's registers are one flat
   enum, so the hypothesis is the equation of `wX` with any one register
   write followed by `pure ()`.
4. `exec_riscv_step_hart_active`: Rocq's section hypotheses become theorem
   premises; Rocq's `add_vec_int … 1` is Lean's `BitVec.addInt … 1`; the
   `get_config_rvfi tt = false` conversion is by computation.  Rocq's
   `s_a`/`s_tick`/`s_final` `Let`s are the definitions `hartActiveSA`,
   `hartActiveSTick`, `hartActiveSFinal`.
5. `exec_execute_JAL` reads `nextPC` first and then `PC`, as the Lean
   model's `execute_JAL` does (Rocq's order is the same).
6. `exec_jump_to` / `_zca`: `jump_to` is a `SailME.run` block; the proofs go
   through `execCatchEarlyReturn`/`execR*` (Weak/Exec.lean deviation 5).
7. Tactics: `skip_csr_false_clauses` is the macro `skip_csr_false_clauses`
   (one `execIfFalseG` peel per false guard, the guard closed by
   `decide +kernel`; Lean has no batching need, so `_g16`/`_g4` are kept as
   lemmas but not used by the macro); `csr_dispatch_eq` is the macro
   `csr_dispatch_eq` (`rfl`, falling back to `kernel_rfl` -- Lean's kernel
   has no Rocq `vm_compute` cost asymmetry to work around).

**Name map (Rocq → Lean).**  RiscvExec: `exec_riscv_step_tick` ↦
`execRiscvStepTick`, `exec_tick_pc` ↦ `execTickPc`,
`exec_riscv_step_hart_active` ↦ `execRiscvStepHartActive`,
`exec_should_inc_minstret_Some` ↦ `execShouldIncMinstretSome`.  ExecCommon:
`h_lui` ↦ `hLui`, `exec_returnM_true` ↦ `execReturnMTrue`, `exec_if_false_g`
↦ `execIfFalseG`, `exec_if_false_g16` ↦ `execIfFalseG16`, `exec_if_false_g4`
↦ `execIfFalseG4`, `skip_csr_false_clauses` ↦ `skip_csr_false_clauses`,
`imm_clui` ↦ `immClui`, `exec_wX_bits_at` ↦ `execWXBitsAt`,
`exec_set_next_pc` ↦ `execSetNextPc`, `exec_jump_to` ↦ `execJumpTo`,
`exec_jump_to_zca` ↦ `execJumpToZca`, `exec_execute_JAL` ↦ `execExecuteJAL`,
`mulop_mul` ↦ `mulopMul`, `exec_execute_ITYPE_ADDI` ↦ `execExecuteITYPEADDI`,
`w_csrr` ↦ `wCsrr`, `csr_csrr` ↦ `csrCsrr`, `i_rs1_csrr` ↦ `iRs1Csrr`,
`i_rd_csrr` ↦ `iRdCsrr`, `exec_rX_bits_x0` ↦ `execRXBitsX0`,
`csr_dispatch_eq` ↦ `csr_dispatch_eq`, `exec_read_CSR_csrr` ↦ `execReadCSRCsrr`,
`exec_architecture_Supervisor` ↦ `execArchitectureSupervisor`,
`exec_hartSupports_M/U/Sstc` ↦ `hartSupportsM/U/Sstc` (deviation 2),
`exec_currentlyEnabled_M` ↦ `execCurrentlyEnabledM`,
`exec_currentlyEnabled_U` ↦ `execCurrentlyEnabledU`,
`exec_currentlyEnabled_Sstc` ↦ `execCurrentlyEnabledSstc`.
Lean-only: `hartActiveSA/STick/SFinal`, `zeroRegs`, `testDevs`, `testSt`
and the `decide +kernel` tests `execTestAddi`, `execTestStep`.

**Not ported** (uses checked against `iris/{Weak,Ax,Wk}*.v`):
`exec_andM_true` (Lean's model has no `and_boolM`; weak uses: none);
`exec_check_CSR_csrr`, `exec_csr_id_read_callback_csrr`,
`exec_check_CSR_result_csrr` (Lean's `check_CSR` adds the Smstateen gate and
reads `mstateen0`/`menvcfg`-style state, so the Rocq "is `returnM true`"
statement does not hold verbatim at a symbolic state; weak uses: none -- the
weak leaves use their own `exec_eff_*` twins); the empty Rocq section
`StepADD` (no declarations).

**Statements checked**: all, against the Rocq source, modulo the deviations.
-/
import Weak.Exec
import MachCSL.BootReset

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. RiscvExec: the cycle wrapper -/

/-- Rocq `exec_should_inc_minstret_Some`: `should_inc_minstret` is total and
moves nothing. -/
theorem execShouldIncMinstretSome (priv : Privilege) (s : ExecSt) :
    ∃ b : Bool, exec (should_inc_minstret priv) s = some (b, s) := by
  unfold should_inc_minstret
  simp only [execBind, readReg, PreSail.readReg, PreSail.emit, exec]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Rocq `exec_tick_pc`: `PC := nextPC`. -/
theorem execTickPc (s : ExecSt) :
    exec (tick_pc ()) s = some ((), s.setReg .PC (s.regs .nextPC)) := rfl

/-- Rocq `exec_riscv_step_tick`: the tick branch is the no-tick branch then
`tick_clock`. -/
theorem execRiscvStepTick (s s' s'' : ExecSt) (h1 : exec (riscvStep false) s = some ((), s'))
    (h2 : exec (tick_clock ()) s' = some ((), s'')) : exec (riscvStep true) s = some ((), s'') := by
  unfold riscvStep at h1 ⊢
  rw [execBind] at h1 ⊢
  rcases h : exec (try_step 0 false) s with _ | ⟨b, s1⟩
  · rw [h] at h1; exact absurd h1 (by simp)
  · rw [h] at h1
    simp only [Bool.false_eq_true, ↓reduceIte, execReturnm, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, rfl⟩ := h1
    simpa using h2

/-- Rocq `s_a`: after the `minstret_increment` write. -/
def hartActiveSA (s : ExecSt) (b : Bool) : ExecSt := s.setReg .minstret_increment b

/-- Rocq `s_tick`: after `tick_pc`. -/
def hartActiveSTick (sExec : ExecSt) : ExecSt := sExec.setReg .PC (sExec.regs .nextPC)

/-- Rocq `s_final`: after the retirement count. -/
def hartActiveSFinal (sExec : ExecSt) (b : Bool) : ExecSt :=
  if b then (hartActiveSTick sExec).setReg .minstret
      (BitVec.addInt ((hartActiveSTick sExec).regs .minstret) 1)
  else hartActiveSTick sExec

/-- Rocq `exec_riscv_step_hart_active`: thread the `try_step` wrapper around
a retiring `run_hart_active` (the section hypotheses as premises). -/
theorem execRiscvStepHartActive (s sExec : ExecSt) (retval : BitVec 32) (b : Bool)
    (hsi : exec (should_inc_minstret (s.regs .cur_privilege)) s = some (b, s))
    (hhartA : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE ())
    (hha : exec (run_hart_active 0) (hartActiveSA s b) =
      some (.Step_Execute (.Retire_Success (), retval), sExec))
    (hhartExec : sExec.regs .hart_state = .HART_ACTIVE ())
    (hmiExec : sExec.regs .minstret_increment = b) :
    exec (riscvStep false) s = some ((), hartActiveSFinal sExec b) := by
  unfold hartActiveSA at hhartA hha
  unfold riscvStep try_step
  simp only [execBind, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, exec, hsi,
    hhartA, hha, hhartExec, assert, PreSail.assert, hart_is_active, ↓reduceIte, execReturnm, execTickPc,
    get_config_rvfi, Bool.false_eq_true]
  have hmi : (sExec.setReg .PC (sExec.regs .nextPC)).regs .minstret_increment = b := by
    show (sExec.regs.set .PC (sExec.regs .nextPC)) .minstret_increment = b
    rw [RegFile.set_other _ _ _ _ (by decide)]
    exact hmiExec
  rw [hmi]
  cases b <;> rfl

/-! ## 2. ExecCommon -/

/-- Rocq `h_lui`. -/
def hLui : BitVec 16 := 0x6505#16

/-- Rocq `exec_returnM_true`. -/
theorem execReturnMTrue (b : Bool) (s : ExecSt) (h : b = true) :
    exec (pure b : SailM Bool) s = some (true, s) := by
  subst h; rfl

/-- Rocq `exec_if_false_g`: peel one false guard. -/
theorem execIfFalseG {X : Type} (g : Bool) (A B : SailM X) (s : ExecSt) (h : g = false) :
    exec (if g then A else B) s = exec B s := by
  subst h; rfl

/-- Rocq `exec_if_false_g16`. -/
theorem execIfFalseG16 {X : Type}
    (g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 : Bool)
    (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B : SailM X) (s : ExecSt)
    (h1 : g1 = false) (h2 : g2 = false) (h3 : g3 = false) (h4 : g4 = false) (h5 : g5 = false)
    (h6 : g6 = false) (h7 : g7 = false) (h8 : g8 = false) (h9 : g9 = false) (h10 : g10 = false)
    (h11 : g11 = false) (h12 : g12 = false) (h13 : g13 = false) (h14 : g14 = false)
    (h15 : g15 = false) (h16 : g16 = false) :
    exec (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else
      if g5 then A5 else if g6 then A6 else if g7 then A7 else if g8 then A8 else
      if g9 then A9 else if g10 then A10 else if g11 then A11 else if g12 then A12 else
      if g13 then A13 else if g14 then A14 else if g15 then A15 else if g16 then A16 else B) s =
      exec B s := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16; rfl

/-- Rocq `exec_if_false_g4`. -/
theorem execIfFalseG4 {X : Type} (g1 g2 g3 g4 : Bool) (A1 A2 A3 A4 B : SailM X) (s : ExecSt)
    (h1 : g1 = false) (h2 : g2 = false) (h3 : g3 = false) (h4 : g4 = false) :
    exec (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else B) s =
      exec B s := by
  subst h1 h2 h3 h4; rfl

/-- Rocq `skip_csr_false_clauses`: peel every leading false guard of a
nested-`if` dispatch under `exec`. -/
macro "skip_csr_false_clauses" : tactic =>
  `(tactic| repeat (rw [execIfFalseG]; rotate_left; decide +kernel))

/-- `skip_csr_false_clauses` at work: two false guards peeled. -/
example (A B C : SailM Unit) (s : ExecSt) :
    exec (if (1 == 2 : Bool) then A else if (3 == 4 : Bool) then B else C) s = exec C s := by
  skip_csr_false_clauses

/-- Rocq `imm_clui`: the 6-bit immediate of `c.lui` in `h_lui`. -/
def immClui : BitVec 6 := hLui.extractLsb' 12 1 ++ hLui.extractLsb' 2 5

/-- Rocq `exec_wX_bits_at` (deviation 3). -/
theorem execWXBitsAt (i : BitVec 5) (r : Register) (v' : RegisterType r) (s : ExecSt) (v : BitVec 64)
    (heq : wX (.Regno (BitVec.toNatInt i) : regno) v = (writeReg r v' >>= fun _ => pure ())) :
    exec (wX_bits (.Regidx i : regidx) v) s = some ((), s.setReg r v') := by
  show exec (wX (.Regno (BitVec.toNatInt i) : regno) v) s = _
  rw [heq]; rfl

/-- Rocq `exec_set_next_pc`: the branch announcement is silent. -/
theorem execSetNextPc (target : BitVec 64) (s : ExecSt) :
    exec (set_next_pc target) s = some ((), s.setReg .nextPC target) := rfl

/-- Rocq `exec_jump_to`: an aligned target with bit 1 clear jumps. -/
theorem execJumpTo (target : BitVec 64) (s : ExecSt)
    (halign : (BitVec.access target 0 == 0#1) = true)
    (hbit1 : bit_to_bool (BitVec.access target 1) = false) :
    exec (jump_to target) s = some (RETIRE_SUCCESS, s.setReg .nextPC target) := by
  unfold jump_to
  rw [execCatchEarlyReturn]
  simp only [ext_control_check_pc, execRBind, execRReturnR, execRLiftR, assert, PreSail.assert,
    halign, ↓reduceIte, execReturnm, hbit1, Bool.false_eq_true, execSetNextPc]

/-- Rocq `exec_jump_to_zca`: with `Zca` on, a 2-aligned target jumps. -/
theorem execJumpToZca (target : BitVec 64) (s : ExecSt)
    (halign : (BitVec.access target 0 == 0#1) = true)
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s)) :
    exec (jump_to target) s = some (RETIRE_SUCCESS, s.setReg .nextPC target) := by
  unfold jump_to
  rw [execCatchEarlyReturn]
  cases hb : bit_to_bool (BitVec.access target 1)
  · simp only [ext_control_check_pc, execRBind, execRReturnR, execRLiftR, assert, PreSail.assert,
      halign, ↓reduceIte, execReturnm, Bool.false_eq_true, execSetNextPc]
  · simp only [ext_control_check_pc, execRBind, execRReturnR, execRLiftR, assert, PreSail.assert,
      halign, ↓reduceIte, execReturnm, hzca, Functions.not, Bool.not_true, Bool.false_eq_true,
      execSetNextPc]

/-- Rocq `exec_execute_JAL`. -/
theorem execExecuteJAL (imm : BitVec 21) (rd : regidx) (s sW : ExecSt)
    (halign : (BitVec.access (s.regs .PC + sign_extend (m := 64) imm) 0 == 0#1) = true)
    (hbit1 : bit_to_bool (BitVec.access (s.regs .PC + sign_extend (m := 64) imm) 1) = false)
    (hwx : exec (wX_bits rd (s.regs .nextPC))
      (s.setReg .nextPC (s.regs .PC + sign_extend (m := 64) imm)) = some ((), sW)) :
    exec (execute_JAL imm rd) s = some (RETIRE_SUCCESS, sW) := by
  unfold execute_JAL get_next_pc
  exec_steps [execJumpTo _ s halign hbit1, RETIRE_SUCCESS, hwx]

/-- Rocq `mulop_mul`. -/
def mulopMul : mul_op := { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }

/-- Rocq `exec_execute_ITYPE_ADDI`. -/
theorem execExecuteITYPEADDI (imm : BitVec 12) (rs1 rd : regidx) (a : BitVec 64) (s s' : ExecSt)
    (ha : exec (rX_bits rs1) s = some (a, s))
    (hw : exec (wX_bits rd (a + sign_extend (m := 64) imm)) s = some ((), s')) :
    exec (execute (.ITYPE (imm, rs1, rd, .ADDI))) s = some (RETIRE_SUCCESS, s') := by
  show exec (execute_ITYPE imm rs1 rd .ADDI) s = _
  unfold execute_ITYPE
  simp only [execBind, ha, execReturnm, hw]

/-- Rocq `w_csrr`: `csrr a1, mhartid`. -/
def wCsrr : BitVec 32 := 0xf14025f3#32
/-- Rocq `csr_csrr`. -/
def csrCsrr : BitVec 12 := wCsrr.extractLsb' 20 12
/-- Rocq `i_rs1_csrr`. -/
def iRs1Csrr : BitVec 5 := wCsrr.extractLsb' 15 5
/-- Rocq `i_rd_csrr`. -/
def iRdCsrr : BitVec 5 := wCsrr.extractLsb' 7 5

/-- Rocq `exec_rX_bits_x0`: `x0` reads zero. -/
theorem execRXBitsX0 (i : BitVec 5) (s : ExecSt) (h : BitVec.toNatInt i = 0) :
    exec (rX_bits (.Regidx i : regidx)) s = some (zero_reg, s) := by
  show exec (rX (.Regno (BitVec.toNatInt i) : regno)) s = _
  rw [h]; rfl

/-- Rocq `csr_dispatch_eq`: close a CSR-dispatch equation by computation. -/
macro "csr_dispatch_eq" : tactic => `(tactic| first | rfl | kernel_rfl)

/-- Rocq `exec_read_CSR_csrr`: `mhartid` reads its register. -/
theorem execReadCSRCsrr (s : ExecSt) : exec (read_CSR csrCsrr) s = some (s.regs .mhartid, s) := by
  have e : read_CSR csrCsrr = readReg .mhartid := by csr_dispatch_eq
  rw [e]; rfl

/-- Rocq `exec_architecture_Supervisor`. -/
theorem execArchitectureSupervisor (s : ExecSt)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) :
    exec (architecture .Supervisor) s = some (.RV64, s) := by
  unfold architecture
  simp only [execBind, readReg, PreSail.readReg, PreSail.emit, exec, execReturnm, hsxl]
  rfl

/-- Rocq `exec_hartSupports_M` (deviation 2). -/
theorem hartSupportsM : hartSupports .Ext_M = true := by decide +kernel
/-- Rocq `exec_hartSupports_U` (deviation 2). -/
theorem hartSupportsU : hartSupports .Ext_U = true := by decide +kernel
/-- Rocq `exec_hartSupports_Sstc` (deviation 2). -/
theorem hartSupportsSstc : hartSupports .Ext_Sstc = true := by decide +kernel

/-- Rocq `exec_currentlyEnabled_M`. -/
theorem execCurrentlyEnabledM (s : ExecSt) (hm : (_get_Misa_M (s.regs .misa) == 1#1) = true) :
    exec (currentlyEnabled .Ext_M) s = some (true, s) := by
  rw [currentlyEnabled]
  simp only [hartSupportsM, ↓reduceIte, execBind, readReg, PreSail.readReg, PreSail.emit, exec, hm,
    execReturnm]

/-- Rocq `exec_currentlyEnabled_U`. -/
theorem execCurrentlyEnabledU (s : ExecSt) (hu : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    exec (currentlyEnabled .Ext_U) s = some (true, s) := by
  rw [currentlyEnabled]
  simp only [hartSupportsU, ↓reduceIte, execBind, readReg, PreSail.readReg, PreSail.emit, exec, hu]
  rw [currentlyEnabled]
  have : hartSupports .Ext_Zicsr = true := by decide +kernel
  simp only [this, execReturnm]

/-- Rocq `exec_currentlyEnabled_Sstc`. -/
theorem execCurrentlyEnabledSstc (s : ExecSt) : exec (currentlyEnabled .Ext_Sstc) s = some (true, s) := by
  rw [currentlyEnabled]
  simp only [hartSupportsSstc, execReturnm]

/-! ## 3. Closed evaluation in the kernel

`exec` is structural, so at a closed state the kernel evaluates it; any
`DecidableEq` projection of the result is then a `decide +kernel` fact.
`execTestAddi` runs one `execute`; `execTestStep` runs one whole cycle
(`riscvStep false`: interrupt check, fetch from the byte map, decode, execute,
retire) of `addi x2, x1, 5` at `0x80000000` in machine mode. -/

/-- A closed register file: every register at its type's default. -/
def zeroRegs : RegFile := fun r => by cases r <;> exact default

/-- A closed device fabric. -/
def testDevs : DevStates := ⟨fun _ => default⟩

/-- `addi x2, x1, 5` (`0x00508113`) at `0x80000000`, `x1 = 7`: the boot
program's derived reset values (`MachCSL.resetValRun`: machine mode, `misa`,
the PMA regions, `PC`) over `zeroRegs`. -/
def testSt : ExecSt where
  regs := RegFile.set (fun r => (resetValRun ⟨0, by decide⟩ r).getD (zeroRegs r)) .x1 7#64
  mem := fun a =>
    if a = 0x80000000#64 then some 0x13#8 else if a = 0x80000001#64 then some 0x81#8
    else if a = 0x80000002#64 then some 0x50#8 else if a = 0x80000003#64 then some 0x00#8
    else none
  dev := testDevs

/-- One `execute` at a closed state, by kernel evaluation. -/
theorem execTestAddi :
    ((exec (execute (.ITYPE (5#12, .Regidx 1#5, .Regidx 2#5, .ADDI))) testSt).map
      fun p => ((match p.1 with | .Retire_Success () => true | _ => false), p.2.regs .x2)) =
      some (true, 12#64) := by
  decide +kernel

/-- One whole cycle at a closed state, by kernel evaluation: `x2 = 12`,
`PC` advanced by 4. -/
theorem execTestStep :
    ((exec (riscvStep false) testSt).map fun p => (p.2.regs .x2, p.2.regs .PC)) =
      some (12#64, 0x80000004#64) := by
  decide +kernel

end Weak
