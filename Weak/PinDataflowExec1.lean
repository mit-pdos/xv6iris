/-
Weak: **W9a (B) B1 — the per-clause dataflow lemmas, base instructions** (plan
`notes/weak-allocproc-plan.md` rev 49 §C "W9a (B)" (B1); spike `notes/W9aB-spike.md` §4, the opcode
set of the 1,631 certified-walk states).  Lean-only.

For each destination-writing base `execute_*` clause of the set, symbolic in its operands, at any
state whose role has no `mip`/`mtime` destination (`dfNwRole`): along every path, the result is a
FAILURE (`failRes`: neither a retirement nor an `ExecuteAs` redirect), or it is `RETIRE_SUCCESS`
and the clause wrote its destination GPR `rd` ONCE (`dfGprWr`, nothing for `x0`), after reading
every register of its source list `req` (`dfRet st rd req`).  Each is walked by hand (the
register-only chain `df_alu`, dispatched on the bound tree's head) over the GPR leaves
(`dfRX`/`dfWX`) and `nwB` subtrees with value posts (`jump_to`, `vmem_read_addr`).  The
destination-free classes (`STORE`, `BTYPE`, `FENCE`, ...) need no clause lemma:
`Weak/PinDataflowExec2.lean` covers EVERY instruction at a destination-free role.

| class | `rd` | `req` | how |
|---|---|---|---|
| RTYPE, RTYPEW, REM | `rd` | `rs1, rs2` | leaves |
| ITYPE, ADDIW, SHIFTIOP, SHIFTIWOP | `rd` | `rs1` | leaves |
| UTYPE (LUI/AUIPC), JAL | `rd` | none | leaves, `jump_to` (`nwJumpTo`) |
| JALR | `rd` | `rs1` | leaves, `update_elp_state`, `jump_to` |
| LOAD | `rd` | `rs1` | `vmem_read` = the address (`rX_bits rs1`) then `vmem_read_addr` (`nwVmemReadAddr`) |

Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflowMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataflow
open SailCycleOrderK

/-! ## 1. The clause post -/

/-- Read GPRs `l` in order. -/
def dfGprRds (st : DfSt) (l : List (BitVec 5)) : DfSt := l.foldl dfGprRd st

theorem dfExtGprRds (st : DfSt) (l : List (BitVec 5)) : dfExt st (dfGprRds st l) := by
  induction l generalizing st with
  | nil => exact dfExtRefl st
  | cons i l ih => exact dfExtTrans _ _ _ (dfExtGprRd st i) (ih (dfGprRd st i))

theorem dfGprRdsMem (st : DfSt) (l : List (BitVec 5)) :
    ∀ i, i ∈ l → i.toNat ≠ 0 → i.toNat ∈ (dfGprRds st l).rds := by
  induction l generalizing st with
  | nil => intro i h; cases h
  | cons j l ih =>
    intro i hi hz
    rcases List.mem_cons.1 hi with rfl | hi
    · exact dfExtMem _ _ _ (dfExtGprRds (dfGprRd st i) l) (dfGprRdMem st i hz)
    · exact ih (dfGprRd st j) i hi hz

/-- **THE CLAUSE POST** (header): a failure, or a retirement that wrote `rd` once after reading
`req`. -/
def dfRet (st : DfSt) (rd : BitVec 5) (req : List (BitVec 5)) (r : ExecutionResult)
    (st' : DfSt) : Prop :=
  failRes r = true ∨
  (r = RETIRE_SUCCESS ∧ ∃ st1, dfExt st st1 ∧ (∀ i, i ∈ req → i.toNat ≠ 0 → i.toNat ∈ st1.rds) ∧
    dfExt (dfGprWr st1 rd) st')

theorem dfRetOk (st : DfSt) (rd : BitVec 5) (req : List (BitVec 5)) (st1 st' : DfSt)
    (h1 : dfExt (dfGprRds st req) st1) (h : dfExt (dfGprWr st1 rd) st') :
    dfRet st rd req RETIRE_SUCCESS st' :=
  Or.inr ⟨rfl, st1, dfExtTrans _ _ _ (dfExtGprRds st req) h1,
    fun i hi hz => dfExtMem _ _ _ h1 (dfGprRdsMem st req i hi hz), h⟩

/-! ## 2. `nwB` pieces -/

@[nw_reg] theorem nwAssert (p : Bool) (s : String) : nwT (assert p s : SailM Unit) := by
  nw_walk

theorem nwReadReg (r : Register) : nwT (readReg r : SailM (RegisterType r)) := by
  nw_walk

@[nw_reg] theorem nwGetNextPc (u : Unit) : nwT (get_next_pc u) := by
  nw_walk

@[nw_reg] theorem nwGetArchPc (u : Unit) : nwT (get_arch_pc u) := by
  nw_walk

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwUpdateElpState (rs1 : regidx) : nwT (update_elp_state rs1) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwTransformEffectiveAddress (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    nwT (transform_effective_address va acc) := by
  nw_walk

/-! ## 4. The register-only classes -/

theorem dfNwRoleExt (st st' : DfSt) (he : dfExt st st') (h : dfNwRole st.ro) : dfNwRole st'.ro :=
  he.1 ▸ h

/-- The head constant of the bound tree of a `dfB` goal `dfB P (x >>= f) st` (`none`: no bind). -/
def dfBindHead? (t : Lean.Expr) : Option Lean.Name :=
  let t := t.consumeMData
  if t.isAppOfArity ``Weak.PinDataflow.dfB 4 then
    let m := (t.getArg! 2).consumeMData
    if m.isAppOfArity ``Bind.bind 6 then (m.getArg! 4).consumeMData.getAppFn.constName? else none
  else none

open Lean Elab Tactic in
/-- One step of the register-only chain, dispatched on the bound tree's head constant (so no
failing unification unfolds a Sail definition): a GPR read, a `pure` bind, the closing GPR write. -/
elab "df_alu1" hro:term : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  match dfBindHead? t with
  | some ``LeanRV64D.Functions.rX_bits =>
      evalTactic (← `(tactic| refine dfRXBind _ _ _ _ (fun _ => ?_)))
  | some ``Pure.pure => evalTactic (← `(tactic| refine dfBPureBind _ _ _ _ ?_))
  | some ``LeanRV64D.Functions.wX_bits =>
      evalTactic (← `(tactic|
        exact dfWXBind _ _ _ _ _ $hro (fun _ _ h => dfRetOk _ _ _ _ _ (dfExtRefl _) h)))
  | _ =>
    let t' := t.consumeMData
    let m := if t'.isAppOfArity ``Weak.PinDataflow.dfB 4 then (t'.getArg! 2).consumeMData else t'
    if m.isLet || m.isAppOf ``letFun then evalTactic (← `(tactic| dsimp only))
    else throwError "df_alu1: no step{indentExpr t}"

/-- The register-only chain. -/
macro "df_alu" hro:term : tactic => `(tactic| repeat' df_alu1 $hro)

theorem dfExecRtype (rs2 rs1 rd : BitVec 5) (op : rop) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1, rs2])
      (execute_RTYPE (regidx.Regidx rs2) (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_RTYPE
  dsimp only
  cases op <;> (dsimp only; df_alu hro)

theorem dfExecItype (imm : BitVec 12) (rs1 rd : BitVec 5) (op : iop) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1]) (execute_ITYPE imm (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_ITYPE
  dsimp only
  cases op <;> (dsimp only; df_alu hro)

theorem dfExecShiftiop (shamt : BitVec 6) (rs1 rd : BitVec 5) (op : sop) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1])
      (execute_SHIFTIOP shamt (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_SHIFTIOP
  dsimp only
  cases op <;> (dsimp only; df_alu hro)

theorem dfExecShiftiwop (shamt : BitVec 5) (rs1 rd : BitVec 5) (op : sopw) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1])
      (execute_SHIFTIWOP shamt (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_SHIFTIWOP
  df_alu hro

theorem dfExecRtypew (rs2 rs1 rd : BitVec 5) (op : ropw) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1, rs2])
      (execute_RTYPEW (regidx.Regidx rs2) (regidx.Regidx rs1) (regidx.Regidx rd) op) st := by
  unfold execute_RTYPEW
  df_alu hro

theorem dfExecAddiw (imm : BitVec 12) (rs1 rd : BitVec 5) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1]) (execute_ADDIW imm (regidx.Regidx rs1) (regidx.Regidx rd)) st := by
  unfold execute_ADDIW
  df_alu hro

theorem dfExecRem (rs2 rs1 rd : BitVec 5) (u : Bool) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1, rs2])
      (execute_REM (regidx.Regidx rs2) (regidx.Regidx rs1) (regidx.Regidx rd) u) st := by
  unfold execute_REM
  df_alu hro

theorem dfExecUtype (imm : BitVec 20) (rd : BitVec 5) (op : uop) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfRet st rd []) (execute_UTYPE imm (regidx.Regidx rd) op) st := by
  unfold execute_UTYPE
  cases op
  · dsimp only
    df_alu hro
  · refine dfNwBind false _ _ _ _ st hro (nwGetArchPc ()) (fun _ st1 _ h1 => ?_)
    refine dfBPureBind _ _ _ _ ?_
    exact dfWXBind _ _ _ _ _ (dfNwRoleExt _ _ h1 hro) (fun _ _ h => dfRetOk _ _ _ _ _ h1 h)

/-! ## 5. Jumps -/

/-- The jumps' tail: the `jump_to` result, then the link write at a retirement. -/
theorem dfJumpTail (st st3 : DfSt) (rd : BitVec 5) (req : List (BitVec 5)) (link : BitVec 64)
    (r : ExecutionResult) (hr : retOrFail r) (h3 : dfExt st st3) (hro : dfNwRole st.ro)
    (hmem : ∀ i, i ∈ req → i.toNat ≠ 0 → i.toNat ∈ st3.rds) :
    dfB (dfRet st rd req)
      (match (generalizing := false) r with
        | ExecutionResult.Retire_Success PUnit.unit => do
          wX_bits (regidx.Regidx rd) link
          pure (ExecutionResult.Retire_Success ())
        | failure => pure failure) st3 := by
  rcases hr with hr | rfl
  · cases r <;> first | exact Or.inl rfl | (simp only [failRes] at hr; exact absurd hr (by decide))
  · exact dfWXBind _ _ _ _ _ (dfNwRoleExt _ _ h3 hro)
      (fun _ st4 h4 => Or.inr ⟨rfl, st3, h3, hmem, h4⟩)

theorem dfExecJal (imm : BitVec 21) (rd : BitVec 5) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd []) (execute_JAL imm (regidx.Regidx rd)) st := by
  unfold execute_JAL
  refine dfNwBind false _ _ _ _ st hro (nwGetNextPc ()) (fun link st1 _ h1 => ?_)
  refine dfNwBind false _ _ _ _ st1 (dfNwRoleExt _ _ h1 hro) (nwReadReg _)
    (fun pc st2 _ h2 => ?_)
  have h12 := dfExtTrans _ _ _ h1 h2
  refine dfNwBind false _ _ _ _ st2 (dfNwRoleExt _ _ h12 hro) (nwJumpTo _)
    (fun r st3 hr h3 => ?_)
  exact dfJumpTail st st3 rd [] link r hr (dfExtTrans _ _ _ h12 h3) hro
    (fun i h => absurd h List.not_mem_nil)

theorem dfExecJalr (imm : BitVec 12) (rs1 rd : BitVec 5) (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1]) (execute_JALR imm (regidx.Regidx rs1) (regidx.Regidx rd)) st := by
  unfold execute_JALR
  refine dfNwBind false _ _ _ _ st hro (nwUpdateElpState _) (fun _ st1 _ h1 => ?_)
  refine dfNwBind false _ _ _ _ st1 (dfNwRoleExt _ _ h1 hro) (nwGetNextPc ())
    (fun link st2 _ h2 => ?_)
  have h12 := dfExtTrans _ _ _ h1 h2
  refine dfRXBind _ _ _ _ (fun _ => ?_)
  refine dfBPureBind _ _ _ _ ?_
  have h2r := dfExtTrans _ _ _ h12 (dfExtGprRd st2 rs1)
  refine dfNwBind false _ _ _ _ _ (dfNwRoleExt _ _ h2r hro) (nwJumpTo _)
    (fun r st3 hr h3 => ?_)
  refine dfJumpTail st st3 rd [rs1] link r hr (dfExtTrans _ _ _ h2r h3) hro ?_
  intro i hi hz
  rcases List.mem_singleton.1 hi with rfl
  exact dfExtMem _ _ _ h3 (dfGprRdMem st2 i hz)

/-! ## 6. Loads -/

/-- `vmem_read` = the address computation, then `vmem_read_addr` (the early return of its
`SailME` block, by equations). -/
theorem vmemReadEq (rs : regidx) (off : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload)
    (aq rl res : Bool) :
    vmem_read rs off w acc aq rl res =
      (get_transformed_data_addr rs off acc w >>= fun r =>
        match r with
        | .Ext_DataAddr_OK va => vmem_read_addr va w acc aq rl res
        | .Ext_DataAddr_Error e => pure (Err (ExecutionResult.Ext_DataAddr_Check_Failure e))) := by
  simp only [vmem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc,
    pure_bind]
  congr 1; funext r
  cases r <;> simp only [ExceptT.run_pure, run_SailME_throw, pure_bind, bind_assoc, bind_pure]

/-- The address computation reads the base register (and nothing numbered is written). -/
theorem dfGtda (rs : BitVec 5) (off : BitVec 64) (acc : MemoryAccessType mem_payload) (w : Nat)
    (st : DfSt) (hro : dfNwRole st.ro) :
    dfB (fun _ st' => dfExt (dfGprRd st rs) st')
      (get_transformed_data_addr (regidx.Regidx rs) off acc w) st := by
  unfold get_transformed_data_addr ext_data_get_addr
  refine dfBBind (fun r st' => st' = dfGprRd st rs ∧ ∃ va, r = Ext_DataAddr_Check.Ext_DataAddr_OK va)
    _ _ _ st (dfRXBind _ _ _ _ (fun _ => ⟨rfl, _, rfl⟩)) ?_
  rintro r st' ⟨rfl, va, rfl⟩
  exact dfNwBind false _ _ _ _ _ hro (nwTransformEffectiveAddress va acc) (fun _ st'' _ h => h)

theorem dfExecLoad (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool) (w : Nat) (st : DfSt)
    (hro : dfNwRole st.ro) :
    dfB (dfRet st rd [rs1]) (execute_LOAD imm (regidx.Regidx rs1) (regidx.Regidx rd) u w) st := by
  unfold execute_LOAD
  refine dfNwBind false _ _ _ _ st hro (nwAssert _ _) (fun _ st1 _ h1 => ?_)
  rw [vmemReadEq, bind_assoc]
  refine dfBBind _ _ _ _ st1 (dfGtda rs1 _ _ w st1 (dfNwRoleExt _ _ h1 hro)) (fun a st2 h2 => ?_)
  have h12 := dfExtTrans _ _ _ (dfExtTrans _ _ _ h1 (dfExtGprRd st1 rs1)) h2
  cases a with
  | Ext_DataAddr_Error e => exact Or.inl rfl
  | Ext_DataAddr_OK va =>
    refine dfNwBind false resFail _ _ _ st2 (dfNwRoleExt _ _ h12 hro)
      (nwVmemReadAddr va w _ (by intro h; cases h) false false false) (fun res st3 hres h3 => ?_)
    cases res with
    | Ok data =>
      refine dfWXBind _ _ _ _ _ (dfNwRoleExt _ _ (dfExtTrans _ _ _ h12 h3) hro)
        (fun _ st4 h4 => Or.inr ⟨rfl, st3, dfExtTrans _ _ _ h12 h3, ?_, h4⟩)
      intro i hi hz
      rcases List.mem_singleton.1 hi with rfl
      exact dfExtMem _ _ _ h3 (dfExtMem _ _ _ h2 (dfGprRdMem st1 i hz))
    | Err e => exact Or.inl hres

end PinDataflow
end Weak
