/-
Weak: **W9a (B) B1 — the dataflow of ONE instruction's execute stage** (plan
`notes/weak-allocproc-plan.md` rev 49 §C "W9a (B)" (B1); spike `notes/W9aB-spike.md` §4).
Lean-only.

The cycle executes `uxaExecAs ast` (`MachCSL/UExecAluGpr.lean`: `execute` and its ONE `ExecuteAs`
redirect) after the announce.  This file states, for the decoded instruction `ast` and the
announced word's role `ro`, the B1 obligation of the clause: along every path, either the result
is a FAILURE (`failRes`, a trap-type result: the cycle then takes the trap) or the slot counter
is full and no bad register write happened (`dfDone`), i.e. the `LRegW` labels the execute stage
emits are exactly `dfDests ro`, each with sources covering the decoded ones.

* **Destination-free roles** (`dfDests ro = []`: stores, branches, fences, `c.j`, `ORnone`):
  EVERY instruction is neutral, by W-SCO's per-clause footprints (`SailCycleOrderFp.fpExecNotFI`:
  no announce, so the role stays and no write can be an `LRegW`) and `fence.i` by hand
  (`dfExecNoDest`, `dfExecAsNoDest`).
* **GPR-destination roles** (and `dfNwRole`): the base clauses of `Weak/PinDataflowExec1.lean`, indexed by the
  summary `dfSum ast = (rd, req)` (destination, registers read first); a compressed form is its
  `ExecuteAs` target (`dfPure`, `dfSumAs`, the model's `execute_C_*` are pure).  The role must agree
  with the summary (`dfRoleOk`: `depsRd ro = (rd, dec)`, no `depsRd2`, every decoded register
  source read) -- a decidable per-word check (`dfInstrOk`).
* `dfInstr` -- the headline: `dfInstrOk st.ro ast = true`, slots empty → `dfB dfDone (uxaExecAs ast)`.

Not covered here (the check answers `false`, so nothing is claimed): Zicsr (`CSRReg`/`CSRImm`;
`Weak/PinDataflowCsr.lean`, whose `dfInstrAll` is the combined headline), AMOs/LR/SC, M-extension
forms other than `REM` (`remu`), and every class outside the certified walks' opcode set (spike §4)
-- at a destination-free role they ARE covered, by the first bullet.

Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflowExec1
import Weak.SailCycleOrderAllExec

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataflow
open SailCycleOrderK

/-! ## 1. Destination-free roles: any instruction -/

theorem dfExecNoDest (i : instruction) (st : DfSt) (h1 : depsRd st.ro = none)
    (h2 : depsRd2 st.ro = none) : dfB (fun _ st' => dfExt st st') (execute i) st := by
  cases hfi : SailCycleOrderFp.isFI i
  · exact dfBMono _ _ (fun _ _ h => h.2) _ _
      (dfOfFp false _ _ st h1 h2 (SailCycleOrderFp.fpExecNotFI i hfi))
  · cases i
    all_goals first
      | (exfalso; revert hfi; simp only [SailCycleOrderFp.isFI]; decide)
      | exact fun _ => dfExtRefl _

theorem dfExecAsNoDest (i : instruction) (st : DfSt) (h1 : depsRd st.ro = none)
    (h2 : depsRd2 st.ro = none) : dfB (fun _ st' => dfExt st st') (uxaExecAs i) st := by
  unfold uxaExecAs
  refine dfBBind _ _ _ _ st (dfExecNoDest i st h1 h2) (fun r st1 h => ?_)
  cases r
  case ExecuteAs j =>
    exact dfBMono _ _ (fun _ _ h' => dfExtTrans _ _ _ h h') _ _
      (dfExecNoDest j st1 (h.1 ▸ h1) (h.1 ▸ h2))
  all_goals exact h

/-! ## 2. GPR-destination roles -/

/-- A base clause's post survives the redirect stage (a failure or a retirement is no redirect). -/
theorem dfExecAsRet (i : instruction) (st : DfSt) (rd : BitVec 5) (req : List (BitVec 5))
    (h : dfB (dfRet st rd req) (execute i) st) : dfB (dfRet st rd req) (uxaExecAs i) st := by
  unfold uxaExecAs
  refine dfBBind _ _ _ _ st h (fun r st1 hr => ?_)
  rcases hr with hr | ⟨rfl, hr⟩
  · cases r <;> first | exact Or.inl hr | (simp only [failRes] at hr; exact absurd hr (by decide))
  · exact Or.inr ⟨rfl, hr⟩

/-- **The summary of a base clause** (header): its destination GPR and the registers it reads
before writing it. -/
def dfSum (i : instruction) : Option (BitVec 5 × List (BitVec 5)) :=
  match i with
  | .RTYPE (rs2, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1, uxaIdx rs2])
  | .ITYPE (_, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1])
  | .SHIFTIOP (_, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1])
  | .SHIFTIWOP (_, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1])
  | .RTYPEW (rs2, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1, uxaIdx rs2])
  | .ADDIW (_, rs1, rd) => some (uxaIdx rd, [uxaIdx rs1])
  | .REM (rs2, rs1, rd, _) => some (uxaIdx rd, [uxaIdx rs1, uxaIdx rs2])
  | .UTYPE (_, rd, _) => some (uxaIdx rd, [])
  | .JAL (_, rd) => some (uxaIdx rd, [])
  | .JALR (_, rs1, rd) => some (uxaIdx rd, [uxaIdx rs1])
  | .LOAD (_, rs1, rd, _, _) => some (uxaIdx rd, [uxaIdx rs1])
  | _ => none

theorem dfExecSum (i : instruction) (rd : BitVec 5) (req : List (BitVec 5))
    (h : dfSum i = some (rd, req)) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd req) (execute i) st := by
  cases i
  all_goals first | (simp only [dfSum, reduceCtorEq] at h) | skip
  case RTYPE a =>
    obtain ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecRtype rs2 rs1 rd' op st hro
  case ITYPE a =>
    obtain ⟨imm, ⟨rs1⟩, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecItype imm rs1 rd' op st hro
  case SHIFTIOP a =>
    obtain ⟨sh, ⟨rs1⟩, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecShiftiop sh rs1 rd' op st hro
  case SHIFTIWOP a =>
    obtain ⟨sh, ⟨rs1⟩, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecShiftiwop sh rs1 rd' op st hro
  case RTYPEW a =>
    obtain ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecRtypew rs2 rs1 rd' op st hro
  case ADDIW a =>
    obtain ⟨imm, ⟨rs1⟩, ⟨rd'⟩⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecAddiw imm rs1 rd' st hro
  case REM a =>
    obtain ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd'⟩, u⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecRem rs2 rs1 rd' u st hro
  case UTYPE a =>
    obtain ⟨imm, ⟨rd'⟩, op⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecUtype imm rd' op st hro
  case JAL a =>
    obtain ⟨imm, ⟨rd'⟩⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecJal imm rd' st hro
  case JALR a =>
    obtain ⟨imm, ⟨rs1⟩, ⟨rd'⟩⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecJalr imm rs1 rd' st hro
  case LOAD a =>
    obtain ⟨imm, ⟨rs1⟩, ⟨rd'⟩, u, w⟩ := a
    simp only [uxaIdx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dfExecLoad imm rs1 rd' u w st hro

/-- The compressed forms (RV64C, the model's pure `execute_C_*`): their `execute` result. -/
def dfPure (c : instruction) : Option ExecutionResult :=
  match c with
  | .C_NOP a => some (execute_C_NOP a)
  | .C_ADDI4SPN (rdc, nzimm) => some (execute_C_ADDI4SPN rdc nzimm)
  | .C_LW (uimm, rsc, rdc) => some (execute_C_LW uimm rsc rdc)
  | .C_LD (uimm, rsc, rdc) => some (execute_C_LD uimm rsc rdc)
  | .C_SW (uimm, rsc1, rsc2) => some (execute_C_SW uimm rsc1 rsc2)
  | .C_SD (uimm, rsc1, rsc2) => some (execute_C_SD uimm rsc1 rsc2)
  | .C_ADDI (imm, rsd) => some (execute_C_ADDI imm rsd)
  | .C_ADDIW (imm, rsd) => some (execute_C_ADDIW imm rsd)
  | .C_LI (imm, rd) => some (execute_C_LI imm rd)
  | .C_ADDI16SP imm => some (execute_C_ADDI16SP imm)
  | .C_LUI (imm, rd) => some (execute_C_LUI imm rd)
  | .C_SRLI (shamt, rsd) => some (execute_C_SRLI shamt rsd)
  | .C_SRAI (shamt, rsd) => some (execute_C_SRAI shamt rsd)
  | .C_ANDI (imm, rsd) => some (execute_C_ANDI imm rsd)
  | .C_SUB (rsd, rs2) => some (execute_C_SUB rsd rs2)
  | .C_XOR (rsd, rs2) => some (execute_C_XOR rsd rs2)
  | .C_OR (rsd, rs2) => some (execute_C_OR rsd rs2)
  | .C_AND (rsd, rs2) => some (execute_C_AND rsd rs2)
  | .C_SUBW (rsd, rs2) => some (execute_C_SUBW rsd rs2)
  | .C_ADDW (rsd, rs2) => some (execute_C_ADDW rsd rs2)
  | .C_J imm => some (execute_C_J imm)
  | .C_BEQZ (imm, rs) => some (execute_C_BEQZ imm rs)
  | .C_BNEZ (imm, rs) => some (execute_C_BNEZ imm rs)
  | .C_SLLI (shamt, rsd) => some (execute_C_SLLI shamt rsd)
  | .C_LWSP (uimm, rd) => some (execute_C_LWSP uimm rd)
  | .C_LDSP (uimm, rd) => some (execute_C_LDSP uimm rd)
  | .C_SWSP (uimm, rs2) => some (execute_C_SWSP uimm rs2)
  | .C_SDSP (uimm, rs2) => some (execute_C_SDSP uimm rs2)
  | .C_JR rs1 => some (execute_C_JR rs1)
  | .C_JALR rs1 => some (execute_C_JALR rs1)
  | .C_MV (rd, rs2) => some (execute_C_MV rd rs2)
  | .C_ADD (rsd, rs2) => some (execute_C_ADD rsd rs2)
  | _ => none

theorem dfPureExec (c : instruction) (r : ExecutionResult) (h : dfPure c = some r) :
    execute c = pure r := by
  cases c
  all_goals first | (simp only [dfPure, reduceCtorEq] at h) | skip
  all_goals (simp only [Option.some.injEq] at h; subst h; rfl)

/-- The summary of the instruction the redirect stage runs. -/
def dfSumAs (c : instruction) : Option (BitVec 5 × List (BitVec 5)) :=
  match dfPure c with
  | some (.ExecuteAs i) => dfSum i
  | _ => dfSum c

theorem dfExecAsSum (c : instruction) (rd : BitVec 5) (req : List (BitVec 5)) (st : DfSt)
    (hro : dfNwRole st.ro) (h : dfSumAs c = some (rd, req)) :
    dfB (dfRet st rd req) (uxaExecAs c) st := by
  unfold dfSumAs at h
  split at h
  · rename_i i hp
    unfold uxaExecAs
    rw [dfPureExec c _ hp]
    exact dfExecSum i rd req h st hro
  · exact dfExecAsRet c st rd req (dfExecSum c rd req h st hro)

/-! ## 3. The role check, the slot arithmetic, the headline -/

/-- **THE PER-WORD CHECK, GPR destination** (header): the role's one destination is `rd`'s
number, and every register its decoded sources name is read by the clause. -/
def dfRoleOk (ro : OpRoles) (rd : BitVec 5) (req : List (BitVec 5)) : Bool :=
  match depsRd ro, depsRd2 ro with
  | some (k, dec), none =>
      (gprNum rd == some k) &&
        dec.all (fun x =>
          match x with
          | .DReg r => req.any (fun i => i.toNat == r && i.toNat != 0)
          | .DLdRes => true)
  | _, _ => false

/-- **THE PER-WORD CHECK** (header): a destination-free role, or a GPR role agreeing with the
summary of the instruction the redirect stage runs. -/
def dfInstrOk (ro : OpRoles) (c : instruction) : Bool :=
  (dfDests ro).isEmpty ||
    (match dfSumAs c with
     | some (rd, req) => dfRoleOk ro rd req
     | none => false)

/-- **The instruction-level post** (header): a failure, or every destination slot filled and no
bad register write. -/
def dfDone (r : ExecutionResult) (st' : DfSt) : Prop :=
  failRes r = true ∨ (st'.ok = true ∧ st'.n = (dfDests st'.ro).length)

theorem dsubbCovers (dec : List Dsrc) (rds : List Nat)
    (hcov : ∀ r, Dsrc.DReg r ∈ dec → r ∈ rds) : dsubb dec (erwSrcs dec rds) = true := by
  unfold dsubb
  refine List.all_eq_true.2 (fun x hx => List.any_eq_true.2 ⟨x, ?_, decide_eq_true rfl⟩)
  exact erwSrcsCovers dec rds x hx (fun r e => hcov r (e ▸ hx))

theorem gprNumLt (rd : BitVec 5) (k : Nat) (h : gprNum rd = some k) : k < 32 := by
  unfold gprNum at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    exact rd.isLt

/-- **The GPR write fills the role's one slot.** -/
theorem dfGprWrFill (st1 : DfSt) (rd : BitVec 5) (k : Nat) (dec : List Dsrc)
    (hk : gprNum rd = some k) (hrd : depsRd st1.ro = some (k, dec)) (h2 : depsRd2 st1.ro = none)
    (hn : st1.n = 0) (hcov : ∀ r, Dsrc.DReg r ∈ dec → r ∈ st1.rds) :
    (dfGprWr st1 rd).n = 1 ∧ (dfGprWr st1 rd).ok = st1.ok ∧ (dfGprWr st1 rd).ro = st1.ro := by
  have hs : slotOk st1.ro 0 k (erwSrcs dec st1.rds) = true := by
    simp only [slotOk, dfDests, hrd, h2, Option.toList, List.append_nil,
      List.getElem?_cons_zero, Nat.beq_refl, Bool.true_and]
    exact dsubbCovers dec st1.rds hcov
  have he : erwOfNum st1.ro st1.rds (some k) = .ERWreg k (erwSrcs dec st1.rds) := by
    simp only [erwOfNum, hrd, ↓reduceIte]
  simp only [dfGprWr, hk, he, erwLabel, dfLab, hn, hs, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem dfDestsNil (ro : OpRoles) (h : (dfDests ro).isEmpty = true) :
    depsRd ro = none ∧ depsRd2 ro = none := by
  unfold dfDests at h
  cases h1 : depsRd ro <;> cases h2 : depsRd2 ro <;> simp_all [Option.toList]

/-- **B1, the execute stage of ONE instruction** (header). -/
theorem dfInstr (c : instruction) (st : DfSt) (hn : st.n = 0) (hok : st.ok = true)
    (h : dfInstrOk st.ro c = true) : dfB dfDone (uxaExecAs c) st := by
  unfold dfInstrOk at h
  cases he : (dfDests st.ro).isEmpty
  · rw [he, Bool.false_or] at h
    split at h
    · rename_i rd req hsum
      unfold dfRoleOk at h
      split at h
      · rename_i k dec hrd h2
        rw [Bool.and_eq_true] at h
        obtain ⟨hk, hdec⟩ := h
        have hk' : gprNum rd = some k := of_decide_eq_true (by simpa using hk)
        have hro : dfNwRole st.ro := by
          intro p hp
          simp only [dfDests, hrd, h2, Option.toList, List.append_nil, List.mem_singleton] at hp
          subst hp
          have := gprNumLt rd k hk'
          exact ⟨by simp only [wcsr, MIP]; omega, by simp only [wcsr, TIME]; omega⟩
        refine dfBMono _ _ ?_ _ _ (dfExecAsSum c rd req st hro hsum)
        rintro r st' (hr | ⟨-, st1, h1, hmem, h'⟩)
        · exact Or.inl hr
        · have hcov : ∀ r, Dsrc.DReg r ∈ dec → r ∈ st1.rds := by
            intro r hr
            have := List.all_eq_true.1 hdec _ hr
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
            obtain ⟨i, hi, rfl, hz⟩ := this
            exact hmem i hi hz
          obtain ⟨f1, f2, f3⟩ := dfGprWrFill st1 rd k dec hk' (h1.1 ▸ hrd) (h1.1 ▸ h2)
            (h1.2.1.trans hn) hcov
          refine Or.inr ⟨?_, ?_⟩
          · rw [h'.2.2.1, f2, h1.2.2.1, hok]
          · rw [h'.2.1, f1, h'.1, f3, h1.1]
            simp only [dfDests, hrd, h2, Option.toList, List.append_nil, List.length_singleton]
      · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true
  · obtain ⟨h1, h2⟩ := dfDestsNil st.ro he
    refine dfBMono _ _ ?_ _ _ (dfExecAsNoDest c st h1 h2)
    intro r st' h'
    refine Or.inr ⟨h'.2.2.1.trans hok, ?_⟩
    rw [h'.2.1, hn, h'.1]
    simp only [dfDests, h1, h2, Option.toList, List.append_nil, List.length_nil]

end PinDataflow
end Weak
