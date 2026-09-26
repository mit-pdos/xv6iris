/-
**The execute classification UP TO DISCARDED READS** (lane U3-A, on lane
AND-ELIM's walker form `URunSc`, MachCSL/SailAndElim): the user loop's
execute contract `UstExecTotalSc` (UserStepLand), consumed through
`swp_URunSc` (MachCSL/UCycleSc).

The model's eager `&&` in `check_CSR` reads `mstateen1..3`/`sstateen1..3`
(outside `ufFoot`) and, for `0x747`/`0x757`, reaches `currentlyEnabled
Ext_Zkr`, which has no clause (`assert false`).  Lane U1-X3's (post-AND-ELIM)
facts state `execute` up to discarded reads (`URunSc`), for every number but
`0x747`/`0x757`; so the contract is proved with the CSR hypothesis shrunk to
`mseccfg`/`mseccfgh` (`UclCsrZkr`, the report's `hZkr`):

* `ustExecOkSc_of`: every `UstExecOk` fact is a `UstExecOkSc` fact (a plain
  walk is a walk up to discards), so every non-CSR row carries over;
* `ucl_rowSc_csrReg`/`ucl_rowSc_csrImm`: the CSR rows from U1-X3's
  `uxr_execute_CSRReg/Imm` (`URunSc.bind` through the redirect);
* `ucl_execTotalSc (hZkr : UclCsrZkr C P) (hM : UclMemArms C P) :
  UstExecTotalSc C P`.
-/
import Xv6.UserClassify
import MachCSL.SailAndElim

namespace Xv6

open MachCSL
open Sail LeanRV64D LeanRV64D.Functions

set_option linter.unusedSectionVars false

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
