/-
Weak: **NON-VACUITY of the symbolic data side (`AxDataX4`)** at `AxSmodeProbe`'s concrete S-mode
state (Sv39, the real 3-level table `pT` of AxSymCtl3, cold TLB, A/D preset).

Rocq: `iris/AxDataX8.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`nvDataLd` / `nvDataSt`: `dataAtS` holds for the probe's data doubleword (VA = PA = sSp + 8 =
0x80001008, the second 4 KiB page of the table), for Load Data and Store Data — the premises of
`ExecDLoadS` / `ExecDStoreS` are SATISFIABLE.  `ExecDLdNv`: the symbolic `ExecD` instantiated at
the probe — c.ldsp ra, 8(sp)'s `execute` (`LOAD (8, sp, ra, false, 8)`, the instruction
`AxSymMem4.nvldCert` runs concretely); `ExecDLdNvRun`: the ∀-state certificate specialised to the
probe's own post-fetch state (the regime holds there: `nvSCtrlOk`), i.e. the same instruction at
the same state as `AxSymMem4.nvldCert`, now with the DEMONIC read value flowing into ra (`ldRes`)
— information the concrete certificate does not carry (its post pins only the PC).  `ExecDStNv`
the c.sdsp twin (regime `ctrlOkSW`: the probe's PMP entry has W, `nvPmpW`).

## Deviations from Rocq

1. SPELLING as `AxDataX4` deviation 1 (`mword n` ↦ `BitVec n`, `w64` ↦ `AxEpiProbe.w64`,
   `s_sp` ↦ `AxSmodeProbe.sSp`, `uint` ↦ `paZ`, `Z_to_bv n z` ↦ `BitVec.ofNat n z`,
   `add_vec (gpr_val rs r) (sign_extend' 64 imm)` ↦ `gprVal rs r + sign_extend (m := 64) imm`,
   `set_reg t nextPC (add_vec_int pc 2)` ↦ `t.setReg .nextPC (BitVec.addInt pc 2)`,
   `update_PTE_Bits (autocast dW) acc = None` ↦ `update_PTE_Bits dW acc = none`).
2. `nvDok`'s address is an `Int` (`(sSp : Int) + 8`), its width a `Nat` (`AxDataX` deviation 4).
3. The Ltac `vr8` is dropped (`decide +kernel` / `ax_epi_ledger_krfl`, `AxSymCtl3` style).
4. `ExecDLdNv` discharges the extra Lean premise `ra5'.toNat ≠ 0` of `ExecDLoadS` (Lean
   `wrState` drops x0 writes); statements unchanged.

**Rocq → Lean name map.**  `nv_va` `nvVa`, `dvpn` `dvpn`, `dW` `dW`, `dT_maps` `dTMaps`,
`dT_slot2/1/0` `dTSlot2/1/0`, `nv_data` `nvData`, `nv_data_ld` `nvDataLd`, `nv_data_st`
`nvDataSt`, `nv_dok` `nvDok`, `sp5` `sp5`, `ra5'` `ra5'`, `imm8` `AxDataX8.imm8` (duplicated
name), `nv_va_eq` `nvVaEq`, `nv_dok_ok` `nvDokOk`, `ExecD_ld_nv` `ExecDLdNv`, `ExecD_ld_nv_run`
`ExecDLdNvRun`, `nv_pmpW` `nvPmpW`, `ExecD_st_nv` `ExecDStNv`, `nv_ctrl_ok_SW` `nvCtrlOkSW`.

**Dropped:** the Ltac `vr8` (deviation 3).  Rocq 21 definitions/lemmas, Lean 21.
-/
import Weak.AxDataX4
import Weak.AxSymCtl3

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `nv_va`: the probe's data doubleword (VA = PA). -/
def nvVa : BitVec 64 := AxEpiProbe.w64 (AxSmodeProbe.sSp + 8)
/-- Rocq `dvpn`. -/
def dvpn : BitVec 27 := WeakKpt.svpnOf nvVa
/-- Rocq `dW`: the data page's leaf. -/
def dW : BitVec 64 := AxEpiProbe.w64 (AxSmodeProbe.pteLeaf 0x80001)

/-- Rocq `dT_maps`. -/
theorem dTMaps : AxPtProt.ptreeMaps pT dvpn pP2 pP1 dW := by
  unfold AxPtProt.ptreeMaps pteValid ptePtr pteLeaf AxPtProt.pteNoNapot ptePbmt0
  refine ⟨pT1, pT0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro s; ax_epi_ledger_krfl)
    | decide +kernel
    | ax_epi_ledger_krfl

/-- Rocq `dT_slot2`. -/
theorem dTSlot2 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr2 pT dvpn) pP2 :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
/-- Rocq `dT_slot1`. -/
theorem dTSlot1 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr1 pP2 dvpn) pP1 :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
/-- Rocq `dT_slot0`. -/
theorem dTSlot0 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr0 pP1 dvpn) dW :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Rocq `nv_data`. -/
theorem nvData (acc : MemoryAccessType mem_payload) :
    (∀ mxr dosum : Bool, pteCheckOk acc .Supervisor mxr dosum dW) →
    update_PTE_Bits dW acc = none →
    dataAtS nvST pT acc nvVa 8 nvVa := by
  intro Hchk Hupd
  refine ⟨pP2, pP1, dW, dTMaps, dTSlot2, dTSlot1, dTSlot0, Hchk, Hupd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel
  · exact AxSymCtl3.ramOkZ _ _ (by decide +kernel)
  · decide +kernel
  · decide +kernel

/-- Rocq `nv_data_ld`. -/
theorem nvDataLd : dataAtS nvST pT (.Load .Data) nvVa 8 nvVa := by
  apply nvData
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel

/-- Rocq `nv_data_st`. -/
theorem nvDataSt : dataAtS nvST pT (.Store .Data) nvVa 8 nvVa := by
  apply nvData
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel

/-- Rocq `nv_dok` (deviation 2). -/
def nvDok (a : Int) (n : Nat) : Prop := a = (AxSmodeProbe.sSp : Int) + 8 ∧ n = 8
/-- Rocq `sp5`. -/
def sp5 : BitVec 5 := BitVec.ofNat 5 2
/-- Rocq `ra5'`. -/
def ra5' : BitVec 5 := BitVec.ofNat 5 1
/-- Rocq `imm8` (duplicated name). -/
def AxDataX8.imm8 : BitVec 12 := BitVec.ofNat 12 8

/-- Rocq `nv_va_eq`. -/
theorem nvVaEq : nvVa = gprVal nvSRs sp5 + sign_extend (m := 64) AxDataX8.imm8 := by
  decide +kernel

/-- Rocq `nv_dok_ok`. -/
theorem nvDokOk : nvDok (paZ nvVa) 8 := by
  refine ⟨?_, rfl⟩
  decide +kernel

/-- Rocq `ExecD_ld_nv`. -/
theorem ExecDLdNv :
    ExecD (imgS nvST) nvDok true (ctrlOkS pT nvSSatp) nvSRs (AxEpiProbe.w64 sPc)
      (wrLoad ra5' (ldRes false 8)) (dpLd 8)
      (.LOAD (AxDataX8.imm8, .Regidx sp5, .Regidx ra5', false, 8)) :=
  ExecDLoadS nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase nvDok nvSRs (AxEpiProbe.w64 sPc)
    AxDataX8.imm8 sp5 ra5' false 8 nvVa nvVa (by decide) (Or.inr (Or.inr (Or.inr rfl)))
    (by decide) (by decide) nvVaEq nvDataLd nvDokOk

/-- Rocq `ExecD_ld_nv_run`: the ∀-state certificate at the probe's own post-fetch state. -/
theorem ExecDLdNvRun :
    EvD (imgS nvST) nvDok true (fun _ _ _ => False)
      (fun d x t' => x = RETIRE_SUCCESS ∧ d ≠ .DPend ∧ dpLd 8 d ∧
        ∃ t0, tlbFrame (nvST.setReg .nextPC (BitVec.addInt (AxEpiProbe.w64 sPc) 2)) t0 ∧
          ctrlOkS pT nvSSatp t0.regs ∧ t' = wrState (wrLoad ra5' (ldRes false 8)) d t0)
      .DPend (execute (.LOAD (AxDataX8.imm8, .Regidx sp5, .Regidx ra5', false, 8)))
      (nvST.setReg .nextPC (BitVec.addInt (AxEpiProbe.w64 sPc) 2)) := by
  apply ExecDLdNv
  · have hne : ∀ r ∈ ctrlRegs, r ≠ Register.nextPC := by decide
    refine ctrlOkSAgree pT nvSSatp nvSRs _ ?_ (nvSCtrlOk pT)
    intro r hr
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (hne r hr)]
    rfl
  · rw [ExecSt.setReg_regs, RegFile.set_same]
  · intro r _
    rw [ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    rfl

/-- Rocq `nv_pmpW`. -/
theorem nvPmpW : pmpW nvSRs := by
  unfold pmpW
  decide +kernel

/-- Rocq `ExecD_st_nv`. -/
theorem ExecDStNv :
    ExecD (imgS nvST) nvDok false (ctrlOkSW pT nvSSatp) nvSRs (AxEpiProbe.w64 sPc)
      wrStore (dpSt nvSRs ra5' 8) (.STORE (AxDataX8.imm8, .Regidx ra5', .Regidx sp5, 8)) :=
  ExecDStoreS nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase nvDok nvSRs (AxEpiProbe.w64 sPc)
    AxDataX8.imm8 ra5' sp5 8 nvVa nvVa (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
    nvVaEq nvDataSt nvDokOk

/-- Rocq `nv_ctrl_ok_SW`. -/
theorem nvCtrlOkSW : ctrlOkSW pT nvSSatp nvSRs := ⟨nvSCtrlOk pT, nvPmpW⟩

end Weak
