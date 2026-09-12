/-
Proof of `_entry`'s specification (`SpecEntry.ENTRY`).

`_entry` calls no kernel function, so the proof takes no callee interfaces; it
chains the framework's machine-mode instruction rules (`MachCSL.WpMmode`) --
one per instruction, no symbolic execution here -- over the code facts of
`CodeEntry`.
-/
import MachCSL.WpMmode
import MachCSL.GprLit
import Xv6.SpecEntry
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-- Normalise the literal arithmetic an instruction rule leaves behind
(next `PC`, immediates) and the register cells it is stated over. -/
macro "entry_norm" : tactic =>
  `(tactic| try simp only [gpr_x1, gpr_x2, gpr_x10, gpr_x11, instrLen, BitVec.reduceAdd,
      BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceMul, KernelSyms.«_entry», startAddr,
      KernelSyms.«start», stack0Slot, BitVec.reduceOfNat])

/-- One instruction: apply its rule, frame the resources (the instruction
itself from the persistent context), step into the continuation. -/
macro "entry_step" rule:term : tactic =>
  `(tactic| (iapply $rule:term
             entry_norm
             iframe
             iframe #
             inext))

set_option maxHeartbeats 4000000 in
theorem EntryProof : ENTRY where
  wp_entry cpu dq hartid s0 v1 v2 v10 v11 := by
    unfold wp_entry_body
    iintro ⟨HmBoot, Hmhartid, Hclock, Htok, #Htext, Hslot, Hpc, Hx1, Hx2, Hx10, Hx11, HΦ⟩
    ihave #Hi00 := text_instr 0x80000000#64 false (instruction.UTYPE (0xa#20, regidx.Regidx 2#5, uop.AUIPC)) _ rfl rfl $$ Htext
    ihave #Hi04 := text_instr 0x80000004#64 false (instruction.LOAD (600#12, regidx.Regidx 2#5, regidx.Regidx 2#5, false, 8)) _ rfl rfl $$ Htext
    ihave #Hi08 := text_instr 0x80000008#64 true (instruction.UTYPE (BitVec.signExtend 20 1#6, regidx.Regidx 10#5, uop.LUI)) _ rfl rfl $$ Htext
    ihave #Hi0a := text_instr 0x8000000a#64 false (instruction.CSRReg (0xF14#12, regidx.Regidx 0#5, regidx.Regidx 11#5, csrop.CSRRS)) _ rfl rfl $$ Htext
    ihave #Hi0e := text_instr 0x8000000e#64 true (instruction.ITYPE (BitVec.signExtend 12 1#6, regidx.Regidx 11#5, regidx.Regidx 11#5, iop.ADDI)) _ rfl rfl $$ Htext
    ihave #Hi10 := text_instr 0x80000010#64 false (instruction.MUL (regidx.Regidx 11#5, regidx.Regidx 10#5, regidx.Regidx 10#5, { signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Signed, result_part := VectorHalf.Low })) _ rfl rfl $$ Htext
    ihave #Hi14 := text_instr 0x80000014#64 true (instruction.RTYPE (regidx.Regidx 10#5, regidx.Regidx 2#5, regidx.Regidx 2#5, rop.ADD)) _ rfl rfl $$ Htext
    ihave #Hi16 := text_instr 0x80000016#64 false (instruction.JAL (66#21, regidx.Regidx 1#5)) _ rfl rfl $$ Htext
    entry_norm
    -- 80000000: auipc sp, 0xa
    entry_step wp_m_auipc cpu dq bootConf bootConf_ok _ false 0xa#20 2#5 (by decide) v2
    iintro HmBoot Hclock Hpc Hx2
    entry_norm
    -- 80000004: ld sp, 600(sp)
    entry_step wp_m_ld_same cpu dq dq bootConf bootConf_ok _ false 600#12 2#5 (by decide) 0x8000a000#64 s0
    iintro HmBoot Hclock Hpc Hx2 Htok Hslot
    entry_norm
    -- 80000008: c.lui a0, 0x1
    entry_step wp_m_lui cpu dq bootConf bootConf_ok _ true (BitVec.signExtend 20 1#6) 10#5 (by decide) v10
    iintro HmBoot Hclock Hpc Hx10
    entry_norm
    -- 8000000a: csrr a1, mhartid
    entry_step wp_m_csrr_mhartid cpu dq dq bootConf bootConf_ok _ false 11#5 (by decide) v11 hartid
    iintro HmBoot Hclock Hpc Hx11 Hmhartid
    entry_norm
    -- 8000000e: c.addi a1, a1, 1
    entry_step wp_m_addi_same cpu dq bootConf bootConf_ok _ true (BitVec.signExtend 12 1#6) 11#5 (by decide) hartid
    iintro HmBoot Hclock Hpc Hx11
    entry_norm
    -- 80000010: mul a0, a0, a1
    entry_step wp_m_mul_same cpu dq bootConf bootConf_ok _ false 10#5 11#5 (by decide) (by decide) _ _
    iintro HmBoot Hclock Hpc Hx10 Hx11
    entry_norm
    -- 80000014: c.add sp, sp, a0
    entry_step wp_m_add_same cpu dq bootConf bootConf_ok _ true 2#5 10#5 (by decide) (by decide) _ _
    iintro HmBoot Hclock Hpc Hx2 Hx10
    entry_norm
    -- 80000016: jal start
    entry_step wp_m_jal cpu dq bootConf bootConf_ok 0x80000016#64 false 66#21 1#5 (by decide) v1 (by decide)
    iintro HmBoot Hclock Hpc Hx1
    entry_norm
    iapply HΦ $$ HmBoot Hmhartid Hclock Htok Hslot Hpc Hx1 Hx2 Hx10 Hx11

end Xv6
