/-
**The execute classification UP TO DISCARDED READS** (lane U3-A, on lane
AND-ELIM's walker form `URunSc`, MachCSL/SailAndElim).

The user loop's contract `UstExecOk` (UserStepLand) is a plain `runRW`
equation for the model's EAGER `uxaExecAs i`.  For the CSR instructions the
eager program is not a walk over the user footprint at eleven numbers (the
eager `&&` of `check_CSR`: `uclEager`), so `ucl_execTotal` carries them as
`UclCsrEager`.  Lane U1-X3's (post-AND-ELIM) facts instead state `execute`
up to discarded reads (`URunSc`), for every number but `0x747`/`0x757`.

This file restates the contract in that form -- `UstExecOkSc` /
`UstExecTotalSc`, consumed by `swp_URunSc` (the eager program's `swp` from a
walk of its short-circuit form) -- and proves it with the CSR hypothesis
shrunk to `mseccfg`/`mseccfgh` (`UclCsrZkr`, the report's `hZkr`):

* `ustExecOkSc_of`: every `UstExecOk` fact is a `UstExecOkSc` fact (a plain
  walk is a walk up to discards), so every non-CSR row carries over;
* `ucl_rowSc_csrReg`/`ucl_rowSc_csrImm`: the CSR rows from U1-X3's
  `uxr_execute_CSRReg/Imm` (`URunSc.bind` through the redirect);
* `ucl_execTotalSc (hZkr : UclCsrZkr C P) (hM : UclMemArms C P) :
  UstExecTotalSc C P`.

Switching the loop (UserStepActive's execute tail) from `UstExecTotal` to
`UstExecTotalSc` is lane U3-L's call: the tail composes the execute walk
under `ucAfterFetch` by `runRW_bind_some`; the `URunSc` twin is
`URunSc.bind` + `swp_URunSc`.  `UstExecTotal → UstExecTotalSc`
(`ustExecTotalSc_of`), so nothing proved against the old contract is lost.
-/
import Xv6.UserClassify
import MachCSL.SailAndElim

namespace Xv6

open MachCSL
open Sail LeanRV64D LeanRV64D.Functions

set_option linter.unusedSectionVars false

/-- **One instruction's execute fact, up to discarded reads**: a walk (of a
short-circuit form) of `uxaExecAs i` from the `nextPC := PC + len` state
answers, for every oracle, an admissible outcome. -/
def UstExecOkSc (C : UCfg) (P : UPtd) (t0 : PTree) (mm0 : BMap) (s : UWSt) (i : instruction) (len : Int) :
    Prop :=
  ∃ res : UOrc → Option (ExecutionResult × UWSt × UOrc),
    URunSc ufFoot (ucNpcS s len) (uxaExecAs i) res ∧
      ∀ orc, ∃ (r : ExecutionResult) (s' : UWSt) (orc' : UOrc),
        res orc = some (r, s', orc') ∧ UstResOk C P t0 mm0 r s'

/-- **The execute classification, up to discarded reads** (`UstExecTotal`'s
twin). -/
structure UstExecTotalSc (C : UCfg) (P : UPtd) : Prop where
  base : ∀ (t0 : PTree) (mm0 : BMap) (s : UWSt) (i : instruction), UstLand C P t0 mm0 s →
    (s.file .PC).getLsbD 0 = false → decodableU i = true → UstExecOkSc C P t0 mm0 s i 4
  rvc : ∀ (t0 : PTree) (mm0 : BMap) (s : UWSt) (i : instruction), UstLand C P t0 mm0 s →
    (s.file .PC).getLsbD 0 = false → decodableUC i = true → UstExecOkSc C P t0 mm0 s i 2

/-- **The CSR hypothesis, up to discards** (the report's `hZkr`): only
`mseccfg`/`mseccfgh`, whose check has no Sail step in the current model. -/
structure UclCsrZkr (C : UCfg) (P : UPtd) : Prop where
  reg : ∀ (t0 : PTree) (mm0 : BMap) (s : UWSt) (csr : BitVec 12) (rs1 rd : regidx) (op : csrop),
    UstLand C P t0 mm0 s → (s.file .PC).getLsbD 0 = false → (csr = 0x747#12 ∨ csr = 0x757#12) →
      UstExecOkSc C P t0 mm0 s (.CSRReg (csr, rs1, rd, op)) 4
  imm : ∀ (t0 : PTree) (mm0 : BMap) (s : UWSt) (csr : BitVec 12) (imm : BitVec 5) (rd : regidx) (op : csrop),
    UstLand C P t0 mm0 s → (s.file .PC).getLsbD 0 = false → (csr = 0x747#12 ∨ csr = 0x757#12) →
      UstExecOkSc C P t0 mm0 s (.CSRImm (csr, imm, rd, op)) 4

variable {C : UCfg} {P : UPtd} {t0 : PTree} {mm0 : BMap}

/-- A plain execute fact is one up to discards. -/
theorem ustExecOkSc_of {s : UWSt} {i : instruction} {len : Int} (h : UstExecOk C P t0 mm0 s i len) :
    UstExecOkSc C P t0 mm0 s i len :=
  ⟨fun orc => runRW ufFoot orc (ucNpcS s len) (uxaExecAs i), URunSc.of_runRW fun _ => rfl, h⟩

/-- The old contract implies the new one. -/
theorem ustExecTotalSc_of (h : UstExecTotal C P) : UstExecTotalSc C P :=
  ⟨fun t0 mm0 s i hL hpc hd => ustExecOkSc_of (h.base t0 mm0 s i hL hpc hd),
   fun t0 mm0 s i hL hpc hd => ustExecOkSc_of (h.rvc t0 mm0 s i hL hpc hd)⟩

/-- An illegal `execute`, up to discards and state-preserving, is an
admissible row. -/
theorem ucl_rowSc_illegal {s : UWSt} (hL : UstLand C P t0 mm0 s) (len : Int) (i : instruction)
    (h : URunSc ufFoot (ucNpcS s len) (execute i)
      (fun orc => some (ExecutionResult.Illegal_Instruction (), ucNpcS s len, orc))) :
    UstExecOkSc C P t0 mm0 s i len :=
  ⟨fun orc => some (ExecutionResult.Illegal_Instruction (), ucNpcS s len, orc),
   URunSc.bind (g := fun o => o) (res := fun orc => some (ExecutionResult.Illegal_Instruction (), ucNpcS s len, orc))
     h (URunSc.of_runRW fun _ => rfl),
   fun _ => ⟨_, _, _, rfl, ucl_resOk_illegal (ucl_land_npc hL len)⟩⟩

/-- **The CSRReg row, up to discards** (U1-X3's `uxr_execute_CSRReg`). -/
theorem ucl_rowSc_csrReg {s : UWSt} (hL : UstLand C P t0 mm0 s) (len : Int) (csr : BitVec 12)
    (hz : csr ≠ 0x747#12 ∧ csr ≠ 0x757#12) (rs1 rd : regidx) (op : csrop) :
    UstExecOkSc C P t0 mm0 s (.CSRReg (csr, rs1, rd, op)) len :=
  ucl_rowSc_illegal hL len _
    (uxr_execute_CSRReg ufFoot_uxa ufFoot_uxr (ucl_uxrCfg (ucl_land_npc hL len)) csr hz rs1 rd op)

/-- **The CSRImm row, up to discards** (U1-X3's `uxr_execute_CSRImm`). -/
theorem ucl_rowSc_csrImm {s : UWSt} (hL : UstLand C P t0 mm0 s) (len : Int) (csr : BitVec 12)
    (hz : csr ≠ 0x747#12 ∧ csr ≠ 0x757#12) (imm : BitVec 5) (rd : regidx) (op : csrop) :
    UstExecOkSc C P t0 mm0 s (.CSRImm (csr, imm, rd, op)) len :=
  ucl_rowSc_illegal hL len _
    (uxr_execute_CSRImm ufFoot_uxr (ucl_uxrCfg (ucl_land_npc hL len)) csr hz imm rd op)

/-- **The CSR row, up to discards** (every number; `mseccfg`/`mseccfgh` from
`hZkr`). -/
theorem ucl_rowSc_csr (hZkr : UclCsrZkr C P) {s : UWSt} (hL : UstLand C P t0 mm0 s)
    (hpc : (s.file .PC).getLsbD 0 = false) (i : instruction) (h : uclCsrU i = true) :
    UstExecOkSc C P t0 mm0 s i 4 := by
  cases i <;> first | exact absurd h Bool.false_ne_true | skip
  case CSRReg p =>
    obtain ⟨csr, rs1, rd, op⟩ := p
    by_cases hz : csr = 0x747#12 ∨ csr = 0x757#12
    · exact hZkr.reg t0 mm0 s csr rs1 rd op hL hpc hz
    · exact ucl_rowSc_csrReg hL 4 csr (not_or.1 hz) rs1 rd op
  case CSRImm p =>
    obtain ⟨csr, imm, rd, op⟩ := p
    by_cases hz : csr = 0x747#12 ∨ csr = 0x757#12
    · exact hZkr.imm t0 mm0 s csr imm rd op hL hpc hz
    · exact ucl_rowSc_csrImm hL 4 csr (not_or.1 hz) imm rd op

/-- **The 32-bit classification, up to discards.** -/
theorem ucl_baseSc (hZkr : UclCsrZkr C P) (hM : UclMemArms C P) (t0 : PTree) (mm0 : BMap) (s : UWSt)
    (i : instruction) (hL : UstLand C P t0 mm0 s) (hpc : (s.file .PC).getLsbD 0 = false)
    (hdec : decodableU i = true) : UstExecOkSc C P t0 mm0 s i 4 := by
  have hc := ucl_cover32 i hdec
  simp only [Bool.or_eq_true] at hc
  rcases hc with (((ha | hc) | hr) | hf) | hm
  · exact ustExecOkSc_of (ucl_row_alu32 hL 4 i ha)
  · exact ustExecOkSc_of (ucl_row_ctl32 hL hpc 4 i hdec hc)
  · exact ucl_rowSc_csr hZkr hL hpc i hr
  · exact ustExecOkSc_of (ucl_row_cfgRefused hL 4 i hf)
  · exact ustExecOkSc_of (ucl_row_mem32 hM hL 4 i hdec hm)

/-- **THE EXECUTE CLASSIFICATION, up to discarded reads**: only
`mseccfg`/`mseccfgh` and the memory contract remain. -/
theorem ucl_execTotalSc (hZkr : UclCsrZkr C P) (hM : UclMemArms C P) : UstExecTotalSc C P :=
  ⟨ucl_baseSc hZkr hM,
   fun t0 mm0 s i hL hpc hd => ustExecOkSc_of (ucl_rvc hM t0 mm0 s i hL hpc hd)⟩

end Xv6
