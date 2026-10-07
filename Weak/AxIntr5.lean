/-
Weak: **NON-VACUITY of constraint B on the REAL Sail model**, at `AxSpineOk8`'s concrete S-mode
state (Sv39 over a real 3-level table, cold TLB, text `c.mv a0, ra` at VA = PA 0x80000000), varied
to SIE = 1.  PURE (no Iris).

Rocq: `iris/AxIntr5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`nvIOn`: SIE = 1, stvec = 0x80002000 (direct), mie.SSIE = 1, mip.SSIP = 1, mideleg = 0x222 (SSIP
delegated) — an S-software interrupt is PENDING.  `nvIOnTraps`: for BOTH ticks and EVERY pin
answer the real `riscvStep` TRAPS (boolean `evb` certificate, sound by `evbSound`): PC = stvec,
sepc = 0x80000000, scause = 0x8000000000000001, mstatus = `AxIntr2.trapMs elp ms`, priv = S, a0
NOT written, minstret NOT bumped.  `nvIOnFetchless`: the trap step performs NO memory access (the
certificate holds over the EMPTY image).  `nvIQuiet`: SIE = 1, mie = 0 — `nvIQuietProceeds`: the
real step executes c.mv.  `nvIExt`: SIE = 1, mie.SEIE = 1, mip = 0 — the PLIC wire decides:
`nvIExtBoth` (c.mv executed OR trapped with SEI), and neither arm alone holds for all answers
(`nvIExtNotAlwaysProceeds`, `nvIExtNotAlwaysTraps`).  `nvICtrlOk*`: the SIE-agnostic regime
`ctrlOkSI` HOLDS at all three states (any tree: the TLB is cold).  `nvIDispOn`: the symbolic
split dispatch field `spiDispSI` at `nvIOn`, next to the real dispatch answering
`some (I_S_Software, Supervisor)`.  `trapStepLabels`: with no announced instruction bits, every
register write of the trap is labelled `LCtrl []` (the nextPC redirect) or `LSilent`.

## Deviations from Rocq

1. SPELLING (as `AxSpineOk8` deviation 1): `mstate` ↦ `ExecSt`, `register_set` ↦ `RegFile.set`,
   `w64` ↦ `AxEpiProbe.w64` (Nat arguments; Rocq `Z`), `s_pc` ↦ `sPc`, `nvS_*` ↦ `nvS*`,
   `dev0_state` ↦ `nvST.dev` (`AxSpineOk8`'s probe device state), `img_of` ↦ `imgOf`,
   `bool_decide (x = y)` ↦ `x == y`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `MstatusBits.trap_ms` ↦ `AxIntr2.trapMs`, `DispPost` ↦ `dispPost`, `spi_disp_SI` ↦
   `spiDispSI`, the trap/mv/either posts' `cause` is a `Nat`.
2. Rocq `rd64 r t` (a lookup at a `register_bitvector_64` name) is DROPPED: Lean registers are
   one typed enumeration, so the posts read `t.regs .PC` etc. directly.
3. `vm_compute` ↦ `decide +kernel`; the Ltacs `vr`/`ctrl_ok_conc` are dropped (each `ctrlOkSI`
   conjunct is decided, as `AxSpineOk8.nvSCtrlOk`).  `pma_allows_all` ↦ `rs .pma_regions =
   bootPMA` (`AxIntr` deviation 1).
4. Pins (O2/`AxRunClose`): `evb` answers both pins (both 0, then both 1), so "every seip answer"
   reads "every pin answer".  At `nvIExt` the both-1 answer raises MEIP too (not enabled: mie.MEIE
   = 0) and SEIP (enabled, delegated), so the trap arm is still SEI.
5. `trapStepLabels`: Rocq's `ib : oib32` / `ib_bits` ↦ `Ibch` / `.ibBits`; `rds : List Nat`;
   `register_beq r nextPC` ↦ `if r = .nextPC`; `WeakPromise.LCtrl`/`LSilent` ↦ `Wlabel.LCtrl` /
   `Wlabel.LSilent`.

**Rocq → Lean name map.**  `with_intr` `withIntr`, `nvI_t` `nvIT`, `nvI_on` `nvIOn`, `nvI_quiet`
`nvIQuiet`, `nvI_ext` `nvIExt`, `trap_post` `trapPost`, `mv_post` `mvPost`, `img_on` `imgOn`,
`nvI_on_traps_false` `nvIOnTrapsFalse`, `nvI_on_traps_true` `nvIOnTrapsTrue`, `nvI_on_traps`
`nvIOnTraps`, `nvI_on_fetchless` `nvIOnFetchless`, `nvI_on_disp` `nvIOnDisp`, `nvI_quiet_false`
`nvIQuietFalse`, `nvI_quiet_true` `nvIQuietTrue`, `nvI_quiet_proceeds` `nvIQuietProceeds`,
`either_post` `eitherPost`, `nvI_ext_both_false` `nvIExtBothFalse`, `nvI_ext_both_true`
`nvIExtBothTrue`, `nvI_ext_both` `nvIExtBoth`, `nvI_ext_not_always_proceeds`
`nvIExtNotAlwaysProceeds`, `nvI_ext_not_always_traps` `nvIExtNotAlwaysTraps`, `nvI_tlb_cold`
`nvITlbCold`, `nvI_ctrl_ok_on` `nvICtrlOkOn`, `nvI_ctrl_ok_quiet` `nvICtrlOkQuiet`,
`nvI_ctrl_ok_ext` `nvICtrlOkExt`, `nvI_intr_on` `nvIIntrOn`, `nvI_disp_on` `nvIDispOn`,
`trap_step_labels` `trapStepLabels`.  None is in the duplicated-name table.  Lean-only: none.

**Dropped:** `rd64` (deviation 2); the Ltacs `vr`, `ctrl_ok_conc` (deviation 3); the
`Print Assumptions` lines (the lint's axiom check covers them).  Rocq 30 definitions/lemmas
(incl. `rd64`) + 2 Ltacs; Lean 29.
-/
import Weak.AxIntr2
import Weak.AxSpineOk8

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The three SIE = 1 states -/

/-- Rocq `with_intr`. -/
def withIntr (ms mieV mipV : Nat) : RegFile :=
  let rs := nvSRs
  let rs := rs.set .mstatus (AxEpiProbe.w64 ms)
  let rs := rs.set .stvec (AxEpiProbe.w64 0x80002000)
  let rs := rs.set .mie (AxEpiProbe.w64 mieV)
  let rs := rs.set .mip (AxEpiProbe.w64 mipV)
  rs

/-- Rocq `nvI_t`. -/
def nvIT (rs : RegFile) : ExecSt := ⟨rs, nvST.mem, nvST.dev⟩

/-- Rocq `nvI_on`: SIE = 1 on top of `sRegs`' mstatus 0xA00000000; SSIE and SSIP set. -/
def nvIOn : ExecSt := nvIT (withIntr 0xA00000002 0x2 0x2)
/-- Rocq `nvI_quiet`. -/
def nvIQuiet : ExecSt := nvIT (withIntr 0xA00000002 0x0 0x0)
/-- Rocq `nvI_ext`. -/
def nvIExt : ExecSt := nvIT (withIntr 0xA00000002 0x200 0x0)

/-- Rocq `trap_post`: the trap post, decidably (deviation 2). -/
def trapPost (t0 : ExecSt) (cause : Nat) (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == AxEpiProbe.w64 0x80002000) &&
  (t'.regs .sepc == AxEpiProbe.w64 sPc) &&
  (t'.regs .scause == AxEpiProbe.w64 cause) &&
  (t'.regs .mstatus == AxIntr2.trapMs (t0.regs .elp) (t0.regs .mstatus)) &&
  ((_get_Mstatus_SIE (t'.regs .mstatus) == 1#1) == false) &&
  (t'.regs .cur_privilege == .Supervisor) &&
  (t'.regs .x10 == t0.regs .x10) &&
  (t'.regs .minstret == t0.regs .minstret)

/-- Rocq `mv_post` (as `AxSpineOk8.nvSPost`). -/
def mvPost (t0 : ExecSt) (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == AxEpiProbe.w64 (sPc + 2)) && (t'.regs .x10 == t0.regs .x1)

/-- Rocq `img_on`. -/
def imgOn : Image := imgOf nvIOn

/-! # 2. Pending S-software interrupt: the real step TRAPS -/

/-- Rocq `nvI_on_traps_false`. -/
theorem nvIOnTrapsFalse :
    evb (imgOf nvIOn) (trapPost nvIOn 0x8000000000000001) (riscvStep false) nvIOn = true := by
  decide +kernel

/-- Rocq `nvI_on_traps_true`. -/
theorem nvIOnTrapsTrue :
    evb (imgOf nvIOn) (trapPost nvIOn 0x8000000000000001) (riscvStep true) nvIOn = true := by
  decide +kernel

/-- Rocq `nvI_on_traps`. -/
theorem nvIOnTraps (tick : Bool) :
    EvA (imgOf nvIOn) (fun _ _ => False)
      (fun x t' => trapPost nvIOn 0x8000000000000001 x t' = true) (riscvStep tick) nvIOn := by
  apply evbSound
  cases tick
  · exact nvIOnTrapsFalse
  · exact nvIOnTrapsTrue

/-- Rocq `nvI_on_fetchless`: NO memory access on the trap step — the certificate holds over the
EMPTY image. -/
theorem nvIOnFetchless (tick : Bool) :
    EvA (fun _ : Int => none) (fun _ _ => False)
      (fun x t' => trapPost nvIOn 0x8000000000000001 x t' = true) (riscvStep tick) nvIOn := by
  apply evbSound
  cases tick <;> decide +kernel

/-- Rocq `nvI_on_disp`: the real dispatch at `nvIOn` answers `some (S-software, S)` for every
pin answer. -/
theorem nvIOnDisp :
    evb (imgOf nvIOn)
      (fun r _ => r == some (InterruptType.I_S_Software, Privilege.Supervisor))
      (dispatchInterrupt .Supervisor) nvIOn = true := by
  decide +kernel

/-! # 3. SIE = 1, nothing pending: the real step PROCEEDS -/

/-- Rocq `nvI_quiet_false`. -/
theorem nvIQuietFalse : evb (imgOf nvIQuiet) (mvPost nvIQuiet) (riscvStep false) nvIQuiet = true := by
  decide +kernel

/-- Rocq `nvI_quiet_true`. -/
theorem nvIQuietTrue : evb (imgOf nvIQuiet) (mvPost nvIQuiet) (riscvStep true) nvIQuiet = true := by
  decide +kernel

/-- Rocq `nvI_quiet_proceeds`. -/
theorem nvIQuietProceeds (tick : Bool) :
    EvA (imgOf nvIQuiet) (fun _ _ => False) (fun x t' => mvPost nvIQuiet x t' = true)
      (riscvStep tick) nvIQuiet := by
  apply evbSound
  cases tick
  · exact nvIQuietFalse
  · exact nvIQuietTrue

/-! # 4. SIE = 1, SEIE = 1, mip = 0: the PLIC wire decides — both arms live -/

/-- Rocq `either_post`. -/
def eitherPost (t0 : ExecSt) (x : Unit) (t' : ExecSt) : Bool :=
  mvPost t0 x t' || trapPost t0 0x8000000000000009 x t'

/-- Rocq `nvI_ext_both_false`. -/
theorem nvIExtBothFalse : evb (imgOf nvIExt) (eitherPost nvIExt) (riscvStep false) nvIExt = true := by
  decide +kernel

/-- Rocq `nvI_ext_both_true`. -/
theorem nvIExtBothTrue : evb (imgOf nvIExt) (eitherPost nvIExt) (riscvStep true) nvIExt = true := by
  decide +kernel

/-- Rocq `nvI_ext_both`. -/
theorem nvIExtBoth (tick : Bool) :
    EvA (imgOf nvIExt) (fun _ _ => False) (fun x t' => eitherPost nvIExt x t' = true)
      (riscvStep tick) nvIExt := by
  apply evbSound
  cases tick
  · exact nvIExtBothFalse
  · exact nvIExtBothTrue

/-- Rocq `nvI_ext_not_always_proceeds`. -/
theorem nvIExtNotAlwaysProceeds :
    evb (imgOf nvIExt) (mvPost nvIExt) (riscvStep false) nvIExt = false := by
  decide +kernel

/-- Rocq `nvI_ext_not_always_traps`. -/
theorem nvIExtNotAlwaysTraps :
    evb (imgOf nvIExt) (trapPost nvIExt 0x8000000000000009) (riscvStep false) nvIExt = false := by
  decide +kernel

/-! # 5. The SIE-agnostic regime holds at the three SIE = 1 states -/

/-- Rocq `nvI_tlb_cold`. -/
theorem nvITlbCold (T : PTree) (ms mieV mipV : Nat) :
    tlbExact T (withIntr ms mieV mipV .tlb) := by
  have h : withIntr ms mieV mipV .tlb = nvSRs .tlb := by
    simp (disch := decide) only [withIntr, RegFile.set_other]
  rw [h]
  exact nvSTlbCold T

/-- Rocq `nvI_ctrl_ok_on`. -/
theorem nvICtrlOkOn (T : PTree) : ctrlOkSI T nvSSatp nvIOn.regs := by
  unfold ctrlOkSI AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts sieOk AxIntr.stvecDirect
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_, ?_,
    nvITlbCold T 0xA00000002 0x2 0x2, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Rocq `nvI_ctrl_ok_quiet`. -/
theorem nvICtrlOkQuiet (T : PTree) : ctrlOkSI T nvSSatp nvIQuiet.regs := by
  unfold ctrlOkSI AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts sieOk AxIntr.stvecDirect
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_, ?_,
    nvITlbCold T 0xA00000002 0x0 0x0, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Rocq `nvI_ctrl_ok_ext`. -/
theorem nvICtrlOkExt (T : PTree) : ctrlOkSI T nvSSatp nvIExt.regs := by
  unfold ctrlOkSI AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts sieOk AxIntr.stvecDirect
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_, ?_,
    nvITlbCold T 0xA00000002 0x200 0x0, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Rocq `nvI_intr_on`. -/
theorem nvIIntrOn : intrOn nvIOn.regs := by
  unfold intrOn
  decide +kernel

/-- Rocq `nvI_disp_on`: the symbolic split dispatch field at `nvIOn`, next to the real answer. -/
theorem nvIDispOn (T : PTree) :
    EvA (imgOf nvIOn) (fun _ _ => False) (dispPost nvIOn) (dispatchInterrupt .Supervisor) nvIOn ∧
    EvA (imgOf nvIOn) (fun _ _ => False)
      (fun r _ => (r == some (InterruptType.I_S_Software, Privilege.Supervisor)) = true)
      (dispatchInterrupt .Supervisor) nvIOn := by
  refine ⟨?_, evbSound _ _ _ _ nvIOnDisp⟩
  have H := spiDispSI (imgOf nvIOn) T nvSSatp nvIOn (nvICtrlOkOn T)
  have hp : nvIOn.regs .cur_privilege = .Supervisor := rfl
  rw [hp] at H
  exact H

/-! # 6. How the graph sees a taken interrupt -/

/-- Rocq `trap_step_labels` (deviation 5): with no announced bits, every register write of the
trap is the `LCtrl []` redirect (nextPC) or silent. -/
theorem trapStepLabels (ib : Ibch) (rds : List Nat) (r : Register) :
    ib.ibBits = none →
    erwLabel (erwOf (depsOfIb ib.ibBits) rds r) = if r = .nextPC then .LCtrl [] else .LSilent := by
  intro h
  rw [h, depsOfIbNone]
  by_cases hr : r = .nextPC
  · subst hr; rfl
  · simp only [erwOf, hr, if_false]
    rfl

end Weak
