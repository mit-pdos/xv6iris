/-
Weak: **constraint B, §3/§4 of `AxIntr`: the SPLIT dispatch field and the TRAP arm,
symbolically (for all states of the SIE-agnostic regime).**  PURE (no Iris).

Rocq: `iris/AxIntr2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`spiDispSI`: `dispatchInterrupt Supervisor` at `ctrlOkSI`, with the demonic pin reads: for EVERY
pin answer the result is `none` or `some (ip, Supervisor)`, the latter only when SIE = 1
(`dispPost`); `dispPostOff`: at SIE = 0 it is `none` (the old field).  `trapSt t ip`: the state
`execHandleInterruptS` computes; it writes EXACTLY mstatus, elp, scause, stval, sepc,
cur_privilege, nextPC (`trapStOther`).  `rfFHandleInterrupt`: the handler tree
(`handle_interrupt ip Supervisor` = `trap_handler` + `set_next_pc`) is REGISTER-ONLY on every
branch (no memory / barrier node, no pin access — checked over ALL branches).
`EvAHandleInterrupt`: the SC exec lemma transferred.  `trapOkSI`: the trap lands in the regime
again, now at SIE = 0 (`trapMs` clears SIE; `sconfMsFacts` survives `trapMs`; elp reset).

## Deviations from Rocq

1. All of `AxIntr`'s spelling deviations (`mstate` ↦ `ExecSt`, `register_lookup r rs` ↦ `rs r`,
   `set_reg` ↦ `ExecSt.setReg`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `zeros' 64` ↦
   `zeros (n := 64)`, `update_subrange_vec_dec` ↦ `Sail.BitVec.updateSubrange`,
   `IntrDefs.sconf_ms_facts` ↦ `AxSpineOk6.sconfMsFacts`, `stvec_direct` ↦ `AxIntr.stvecDirect`,
   `WpIntrCore.stvec_base` ↦ `stvecBase`, `seip_reg` ↦ `AxRunClose.pinReg`).
2. `trapSt` is stated through `ExecSC7.trapSupS9` (the same write chain as Rocq's `s1 … s9`,
   which `ExecSC7` deviation 4 already names) followed by the `nextPC` write.
3. Rocq's `MstatusBits.trap_ms` (an SC module the Lean tree ports as an ANALOG,
   `MachCSL.trapMs`, with elp fixed to 0) is restated here verbatim as the Lean-only
   `AxIntr2.trapMs elp ms`; the `trap_ms_*` bit facts this file uses are proved in place
   (`AxIntr2.trapMsSIEFalse`, inside `sconfMsFactsTrap`).
4. `spiDispSI`: the Lean model's `read_mip` reads BOTH pins (`sig_meip` then `sig_seip`), each
   answered demonically (`AxSpineOk7.evFactReadPin`); Lean `dispatchInterrupt` additionally runs
   `findPendingInterrupt` (either arm satisfies `dispPost`).  `and_boolM`/`or_boolM` do not
   exist (plain `&&`/`||`).
5. TACTICS: the Ltacs `nseip`, `tlk`, `ev_step`, `ev_go`, `ev_use` are not redeclared
   (`ax_sym2_ev_go`, `AxSymEngine2.evFactUse`, `simp` over `RegFile.set_*`).  Section `disp`'s
   `img` and `EvM` notation are unfolded (`img` is an explicit argument).
6. `rfFHandleInterrupt` is proved through `AxSpinVA6r.rfFTrapHandlerS` (Rocq: `rfF_auto` over the
   whole tree).

**Rocq → Lean name map.**  `scause_intr` `scauseIntr`, `trap_st` `trapSt`,
`exec_handle_interrupt_trap` `execHandleInterruptTrap`, `rfF_handle_interrupt`
`rfFHandleInterrupt`, `EvA_handle_interrupt` `EvAHandleInterrupt`, `trap_st_other` `trapStOther`,
`trap_st_mstatus` `trapStMstatus`, `trap_st_elp` `trapStElp`, `trap_st_scause` `trapStScause`,
`trap_st_stval` `trapStStval`, `trap_st_sepc` `trapStSepc`, `trap_st_priv` `trapStPriv`,
`trap_st_nextPC` `trapStNextPC`, `sconf_ms_facts_trap` `sconfMsFactsTrap`, `trap_ok_SI`
`trapOkSI`, `DispPost` `dispPost`, `spi_disp_SI` `spiDispSI`, `DispPost_off` `dispPostOff`.
None is in the duplicated-name table.  Lean-only (file-qualified): `AxIntr2.trapMs` (Rocq
`MstatusBits.trap_ms`), `AxIntr2.trapMsSIEFalse` (Rocq `MstatusBits.trap_ms_SIE_false`).

**Dropped:** the Ltacs (deviation 5).  Rocq 18 definitions/lemmas + 5 Ltacs; Lean 18 + 2 Lean-only.
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxIntr
import Weak.AxSpinVA6r

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The trap-entry state -/

/-- Rocq `scause_intr`. -/
def scauseIntr (ip : InterruptType) (scOld : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange scOld (64 - 1) (64 - 1)
      (bool_to_bit (trapCause_is_interrupt (.Interrupt ip))))
    (64 - 2) 0 (zero_extend (m := 64 - 1) (trapCause_bits_forwards (.Interrupt ip)))

/-- (Lean-only, deviation 3) Rocq `MstatusBits.trap_ms`: SPIE := SIE; SIE := 0; SPP := 1, in the
model's update order.  (Rocq also had SPELP := elp; since 2026-11-04 the hart has no Zicfilp and the
trap leaves SPELP alone; `elpV` is kept, unused.) -/
def AxIntr2.trapMs (_elpV : BitVec 1) (ms : BitVec 64) : BitVec 64 :=
  let ms_e := ms
  let ms_a := Sail.BitVec.updateSubrange ms_e 5 5 (_get_Mstatus_SIE ms_e)
  let ms_b := Sail.BitVec.updateSubrange ms_a 1 1 0#1
  Sail.BitVec.updateSubrange ms_b 8 8 1#1

/-- Rocq `trap_st` (deviation 2). -/
def trapSt (s : ExecSt) (ip : InterruptType) : ExecSt :=
  (trapSupS9 s ip (s.regs .PC) (s.regs .mstatus) (s.regs .scause) (s.regs .elp)).setReg .nextPC
    (stvecBase (s.regs .stvec))

/-- Rocq `exec_handle_interrupt_trap`. -/
theorem execHandleInterruptTrap (s : ExecSt) (ip : InterruptType) :
    s.regs .cur_privilege = .Supervisor →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    AxIntr.stvecDirect s.regs →
    exec (handle_interrupt ip .Supervisor) s = some ((), trapSt s ip) := by
  intro hp hm hd
  exact execHandleInterruptS s ip _ _ _ _ _ hp rfl rfl rfl rfl hm hd rfl

/-- Rocq `rfF_handle_interrupt` (deviation 6). -/
theorem rfFHandleInterrupt (ip : InterruptType) : rfF (handle_interrupt ip .Supervisor) := by
  unfold handle_interrupt
  repeat (first
      | with_reducible exact rfFTrapHandlerS _ _ _ _
      | rff_step
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | exact True.intro
      | rfl)

/-- Rocq `EvA_handle_interrupt`. -/
theorem EvAHandleInterrupt (img : Image) (s : ExecSt) (ip : InterruptType) :
    s.regs .cur_privilege = .Supervisor →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    AxIntr.stvecDirect s.regs →
    EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = () ∧ t' = trapSt s ip) (handle_interrupt ip .Supervisor) s := by
  intro hp hm hd
  exact EvAOfRfF img _ (rfFHandleInterrupt ip) s () (trapSt s ip)
    (execHandleInterruptTrap s ip hp hm hd)

/-- Rocq `trap_st_other`: lookups through the trap. -/
theorem trapStOther (s : ExecSt) (ip : InterruptType) (r : Register) :
    r ≠ .mstatus → r ≠ .elp → r ≠ .scause → r ≠ .stval → r ≠ .sepc → r ≠ .cur_privilege →
    r ≠ .nextPC → (trapSt s ip).regs r = s.regs r := by
  intro h1 h2 h3 h4 h5 h6 h7
  simp only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h3, RegFile.set_other _ _ _ _ h4,
    RegFile.set_other _ _ _ _ h5, RegFile.set_other _ _ _ _ h6, RegFile.set_other _ _ _ _ h7]

/-- Rocq `trap_st_mstatus`. -/
theorem trapStMstatus (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .mstatus = AxIntr2.trapMs (s.regs .elp) (s.regs .mstatus) := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]
  rfl

/-- Rocq `trap_st_elp` -- CHANGED 2026-11-04: with no Zicfilp the trap leaves `elp` alone (Rocq:
`elp := NO_LP_EXPECTED`). -/
theorem trapStElp (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .elp = s.regs .elp := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `trap_st_scause`. -/
theorem trapStScause (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .scause = scauseIntr ip (s.regs .scause) := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]
  rfl

/-- Rocq `trap_st_stval`. -/
theorem trapStStval (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .stval = zeros (n := 64) := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `trap_st_sepc`. -/
theorem trapStSepc (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .sepc = s.regs .PC := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `trap_st_priv`. -/
theorem trapStPriv (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .cur_privilege = .Supervisor := by
  simp (disch := decide) only [trapSt, trapSupS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `trap_st_nextPC`. -/
theorem trapStNextPC (s : ExecSt) (ip : InterruptType) :
    (trapSt s ip).regs .nextPC = stvecBase (s.regs .stvec) := by
  simp only [trapSt, ExecSt.setReg_regs, RegFile.set_same]

section bits

/-- The shared normaliser of the `trapMs` bit facts. -/
local macro "trap_bits" : tactic =>
  `(tactic| (simp only [AxIntr2.trapMs, _get_Mstatus_SIE, _get_Mstatus_MPRV, _get_Mstatus_SXL,
               _get_Mstatus_MXR, _get_Mstatus_TSR, _get_Mstatus_XS, _get_Mstatus_FS,
               _get_Mstatus_VS, _get_Mstatus_SD, _get_Mstatus_MPP, _get_Mstatus_TVM, _get_Mstatus_SPELP, _get_Mstatus_MPELP,
               Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
               BitVec.extractLsb]
             bv_decide))

/-- (Lean-only) Rocq `MstatusBits.trap_ms_SIE_false`. -/
theorem AxIntr2.trapMsSIEFalse (e : BitVec 1) (ms : BitVec 64) :
    (_get_Mstatus_SIE (AxIntr2.trapMs e ms) == 1#1) = false := by
  have h : _get_Mstatus_SIE (AxIntr2.trapMs e ms) = 0#1 := by trap_bits
  rw [h]; decide

/-- Rocq `sconf_ms_facts_trap`. -/
theorem sconfMsFactsTrap (e : BitVec 1) (ms : BitVec 64) :
    AxSpineOk6.sconfMsFacts ms → AxSpineOk6.sconfMsFacts (AxIntr2.trapMs e ms) := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have e1 : _get_Mstatus_MPRV (AxIntr2.trapMs e ms) = _get_Mstatus_MPRV ms := by trap_bits
  have e2 : _get_Mstatus_SXL (AxIntr2.trapMs e ms) = _get_Mstatus_SXL ms := by trap_bits
  have e3 : _get_Mstatus_MXR (AxIntr2.trapMs e ms) = _get_Mstatus_MXR ms := by trap_bits
  have e4 : _get_Mstatus_TSR (AxIntr2.trapMs e ms) = _get_Mstatus_TSR ms := by trap_bits
  have e5 : _get_Mstatus_XS (AxIntr2.trapMs e ms) = _get_Mstatus_XS ms := by trap_bits
  have e6 : _get_Mstatus_FS (AxIntr2.trapMs e ms) = _get_Mstatus_FS ms := by trap_bits
  have e7 : _get_Mstatus_VS (AxIntr2.trapMs e ms) = _get_Mstatus_VS ms := by trap_bits
  have e8 : _get_Mstatus_SD (AxIntr2.trapMs e ms) = _get_Mstatus_SD ms := by trap_bits
  have e9 : _get_Mstatus_MPP (AxIntr2.trapMs e ms) = _get_Mstatus_MPP ms := by trap_bits
  have e10 : _get_Mstatus_TVM (AxIntr2.trapMs e ms) = _get_Mstatus_TVM ms := by trap_bits
  have e11 : _get_Mstatus_SPELP (AxIntr2.trapMs e ms) = _get_Mstatus_SPELP ms := by trap_bits
  have e12 : _get_Mstatus_MPELP (AxIntr2.trapMs e ms) = _get_Mstatus_MPELP ms := by trap_bits
  unfold AxSpineOk6.sconfMsFacts
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end bits

/-- Rocq `trap_ok_SI`: the trap lands in the regime, at SIE = 0. -/
theorem trapOkSI (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (ip : InterruptType) :
    ctrlOkSI T satp0 s.regs →
    ctrlOkSI T satp0 (trapSt s ip).regs ∧ ¬ intrOn (trapSt s ip).regs := by
  intro hc
  have hms : (_get_Mstatus_SIE ((trapSt s ip).regs .mstatus) == 1#1) = false := by
    rw [trapStMstatus]; exact AxIntr2.trapMsSIEFalse _ _
  refine ⟨?_, by unfold intrOn; rw [hms]; decide⟩
  have ho := trapStOther s ip
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, -, h10, h11, h12, h13⟩ := hc
  unfold AxSpineOk6.pmpOk at h13
  unfold ctrlOkSI AxSpineOk6.pmpOk sieOk
  simp (disch := decide) only [trapStPriv, trapStElp, trapStMstatus, ho]
  exact ⟨by first | trivial | rfl, h2, h3, h4, h5, h6, h7, sconfMsFactsTrap _ _ h8,
    Or.inl (AxIntr2.trapMsSIEFalse _ _), h10, h11, h12, h13⟩

/-! # 2. The split dispatch field -/

/-- Rocq `DispPost`. -/
def dispPost (t : ExecSt) (r : Option (InterruptType × Privilege)) (t' : ExecSt) : Prop :=
  t' = t ∧ (r = none ∨ ∃ ip, r = some (ip, .Supervisor) ∧ intrOn t.regs)

/-- Rocq `spi_disp_SI`: THE SPLIT DISPATCH FIELD (deviation 4). -/
theorem spiDispSI (img : Image) (T : PTree) (satp0 : BitVec 64) (t : ExecSt) :
    ctrlOkSI T satp0 t.regs →
    EvA img (fun (_ : Sail.Error exception) (_ : ExecSt) => False) (dispPost t)
      (dispatchInterrupt (t.regs .cur_privilege)) t := by
  intro hc
  obtain ⟨hpriv, -, hmisa, -, -, -, -, -, -, hand0, -⟩ := hc
  have hS : (_get_Misa_S (t.regs .misa) == 1#1) = true := by rw [hmisa]; decide
  have HSA : EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t)
      (currentlyEnabled .Ext_S) t := by
    have h := AxSpineOk7.evCurS img t
    rwa [hS] at h
  rw [hpriv]
  unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse HSA ?_
  ax_sym2_ev_go
  refine AxSpineOk7.evFactReadPin (Or.inr rfl) fun vm => ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse HSA ?_
  ax_sym2_ev_go
  refine AxSpineOk7.evFactReadPin (Or.inl rfl) fun vs => ?_
  ax_sym2_ev_go
  have hz : (zeros : BitVec 64) = 0#64 := rfl
  cases hSIE : (_get_Mstatus_SIE (t.regs .mstatus) == 1#1)
  · simp (config := { decide := true }) only [hand0, hz, BitVec.and_zero, bne_self_eq_false,
      Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    ax_sym2_ev_go
    exact .evRet _ _ ⟨rfl, Or.inl rfl⟩
  · simp (config := { decide := true }) only [hand0, hz, BitVec.and_zero, bne_self_eq_false,
      Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    repeat' (ax_sym2_ev_go; first | split)
    all_goals first
      | exact .evRet _ _ ⟨rfl, Or.inl rfl⟩
      | exact .evRet _ _ ⟨rfl, Or.inr ⟨_, rfl, hSIE⟩⟩

/-- Rocq `DispPost_off`: at SIE = 0 the field is the old one. -/
theorem dispPostOff (t : ExecSt) (r : Option (InterruptType × Privilege)) (t' : ExecSt) :
    dispPost t r t' → ¬ intrOn t.regs → r = none ∧ t' = t := by
  rintro ⟨rfl, rfl | ⟨ip, rfl, hon⟩⟩ hoff
  · exact ⟨rfl, rfl⟩
  · exact absurd hon hoff

end Weak
