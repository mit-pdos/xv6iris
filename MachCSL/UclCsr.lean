/-
MachCSL: **the CSR family at User over the user footprint's read set** (lane
U3-A; U1-X3's `UExecCsr` at `UxrFoot`/`uxrPin`; Rocq `UserCsr.v`
`exec_execute_CSRReg_total_U`/`exec_execute_CSRImm_total_U` + `goodmb_…`).

Every CSR instruction whose number is outside `uclEager` is
`Illegal_Instruction`, state and oracle unchanged, over any footprint reading
`uclReads` (the user tier's `ufFoot` does) at any state satisfying U1-X3's
`UxrCfg`.  The eleven `uclEager` numbers are the eager-`&&` backend issue
(`UclCsrPin`'s header): the classification carries them as a hypothesis.
-/
import MachCSL.UclCsrTab
import MachCSL.UExecCsr

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

section
variable {D : UFoot} {s : UWSt}

/-- The `FS`-gated numbers: the check walks to `CSR_Illegal`. -/
theorem ucl_ccr_fs (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (c : BitVec 12)
    (h : c = 1#12 ∨ c = 2#12 ∨ c = 3#12) (acc : CSRAccessType) :
    runRW D orc s (check_CSR_result c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), s, orc) := by
  obtain ⟨b, hb⟩ := ucl_checkCSR_fs s.file acc hc.fs c h
  unfold check_CSR_result
  rw [runRW_bind, uxr_runRW_of_pin hD hc orc _ _ _ hb]
  apply uxr_runRW_of_pin hD hc orc _ _ false
  rcases h with rfl | rfl | rfl <;> kernel_rfl

/-- **The check at User** over the user read set: every number outside
`uclEager` walks to `CSR_Illegal`, state and oracle unchanged. -/
theorem ucl_ccr (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (c : BitVec 12)
    (hz : uclEager c.toNat = false) (acc : CSRAccessType) :
    runRW D orc s (check_CSR_result c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), s, orc) := by
  by_cases hd : uxrDflt c = true
  · exact uxr_runRW_of_pin hD hc orc _ _ _ (ucl_ccr_dflt s.file c acc hd)
  by_cases he : uxrExc c.toNat = true
  · apply ucl_ccr_fs hD hc orc c _ acc
    simp only [uxrExc, Bool.or_eq_true, Nat.beq_eq] at he
    rcases he with (h | h) | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simpa using h)))
    · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by simpa using h)))
  · obtain ⟨b, hb⟩ := ucl_ccr_spec s.file c acc (by simpa using hd) (by simpa using he) hz
    exact uxr_runRW_of_pin hD hc orc _ _ _ hb

/-- **`doCSR` at User** over the user read set: `Illegal_Instruction`. -/
theorem ucl_doCSR (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (c : BitVec 12)
    (hz : uclEager c.toNat = false) (v : BitVec 64) (rd : regidx) (op : csrop) (acc : CSRAccessType) :
    runRW D orc s (doCSR c v rd op acc) = some (ExecutionResult.Illegal_Instruction (), s, orc) := by
  unfold doCSR
  rw [runRW_bind, uxr_readReg orc .cur_privilege (hD _ (by decide)), Option.bind, hc.priv, runRW_bind,
    ucl_ccr hD hc orc c hz acc]
  rfl

/-- **`CSRImm` at User** over the user read set. -/
theorem ucl_execute_CSRImm (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (csr : BitVec 12)
    (hz : uclEager csr.toNat = false) (imm : BitVec 5) (rd : regidx) (op : csrop) :
    runRW D orc s (execute (.CSRImm (csr, imm, rd, op))) = some (ExecutionResult.Illegal_Instruction (), s, orc) :=
  ucl_doCSR hD hc orc csr hz _ rd op _

/-- **`CSRReg` at User** over the user read set (the source GPR read, then
`doCSR`). -/
theorem ucl_execute_CSRReg (hA : UxaFoot D) (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc)
    (csr : BitVec 12) (hz : uclEager csr.toNat = false) (rs1 rd : regidx) (op : csrop) :
    runRW D orc s (execute (.CSRReg (csr, rs1, rd, op))) = some (ExecutionResult.Illegal_Instruction (), s, orc) := by
  cases rs1 with
  | Regidx i =>
    show runRW D orc s (execute_CSRReg csr (regidx.Regidx i) rd op) = _
    unfold execute_CSRReg
    rw [runRW_bind, uxa_rX hA orc s i, Option.bind]
    exact ucl_doCSR hD hc orc csr hz _ rd op _

end

end MachCSL
