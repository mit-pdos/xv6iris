/-
MachCSL: **the CSR family at User privilege** (lane U1-X3, brief
`notes/briefs/user_layer.md` G10): `execute (CSRReg …)` and `execute (CSRImm …)`
for EVERY csr number, operation, source and destination, as walks up to
discarded reads (`URunSc`, over `runRW` walk equations) from any walker state
(the statement shape of lanes U1-X1/U1-X2).
Rocq `UserCsr.v` (`exec_doCSR_U`/`goodmb_doCSR_U`,
`exec_execute_CSRReg_total_U`/`goodmb_…`, `exec_execute_CSRImm_total_U`/
`goodmb_…`).

**The outcome at xv6's configuration.**  With `scounteren = 0` every
counter (`cycle`/`time`/`instret`/`hpmcounter3..31`, the only CSRs whose
privilege bits admit User and whose extension is live) is refused by
`counter_enabled` (`feature_enabled_for_priv User` needs the `scounteren` bit
once `S` is enabled); `fflags`/`frm`/`fcsr` are refused by `FS = Off`, the
vector CSRs by `Zve32x` being off, `ssp` by `menvcfg.SSE = 0`, `seed` is not a
defined CSR, and every other number fails the privilege or the read-only gate.
So EVERY CSR instruction at User is `Illegal_Instruction`, the state and the
oracle unchanged (`uxr_execute_CSRReg`, `uxr_execute_CSRImm`) -- Rocq's
`u_csr_readable` retiring branch is empty at these pins (Rocq keeps the
counter enables symbolic, so it proves the disjunction; the Lean facts are
the exact outcome).

**Stated up to discarded reads.**  The model's check chain runs every
operand of Sail's short-circuit `&` (the Lean backend hoists `(← …)`); the
facts walk Sail's own evaluation order (`UExecCsrSc.uxrResultSc`) and are
stated for the model's `execute` through the elimination theorem: `URunSc D s
(execute …) (fun orc => some (Illegal_Instruction (), s, orc))`, consumed by
`swp_URunSc` (`MachCSL/SailAndElim.lean`).  So the footprint does not read
the discarded operands' registers (`mstateen1..3`/`sstateen1..3`).

**Except `0x747` and `0x757`** (`mseccfg`/`mseccfgh`): there the model's
step is an ERROR (`uxr_ccr_zkr`, `uxr_currentlyEnabled_Zkr_error`), so the
facts for `execute` carry `csr ≠ 0x747 ∧ csr ≠ 0x757`; the short-circuit walk
(`uxr_ccrSc`) holds for them too.  See `UExecCsrTab`'s header; this needs a
model patch (the missing `currentlyEnabled Ext_Zkr` clause).

**How.**  The short-circuit check chain (`uxrResultSc c User acc`) is
read-only: it is walked by `DecodeBridge.runRead` at the table `uxrPin` and
lifted by `uxr_runRW_of_pin`.  The csr number is split into three classes:
the default class (`UExecCsrDflt`, one symbolic split of each dispatcher),
the 341 named numbers (`UExecCsrTab`, closed kernel walks), and the three
`FS`-gated numbers (composition, `FS = 0` rewriting the symbolic gate).
-/
import MachCSL.UExecCsrTab
import MachCSL.UExecAluGpr

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## The check at User, per class -/

/-- The default class: the short-circuit check at the table is `CSR_Illegal`. -/
theorem uxr_ccr_dflt (f : RegFile) (c : BitVec 12) (acc : CSRAccessType) (h : uxrDflt c = true) :
    runRead (uxrPin f) (uxrResultSc c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), false) := by
  simp only [uxrResultSc, uxrCheckSc, uxr_isAcc_dflt _ _ _ h, pure_bind, bind_assoc,
    Bool.false_eq_true, ↓reduceIte, ite_self]
  kernel_rfl

/-- The `FS`-gated numbers: under `FS = 0` the short-circuit check answers
`false` (Rocq `exec_currentlyEnabled_F_off`, at the `is_CSR_accessible`
clause). -/
theorem uxr_checkCSR_fs (f : RegFile) (acc : CSRAccessType) (hfs : _get_Mstatus_FS (f .mstatus) = 0#2)
    (c : BitVec 12) (hc : c = 1#12 ∨ c = 2#12 ∨ c = 3#12) :
    ∃ b, runRead (uxrPin f) (uxrCheckSc c Privilege.User acc) = some (false, b) := by
  have hite : ∀ y : Bool, (if y = true then (pure true : SailM Bool) else pure false) = pure y := by
    intro y; cases y <;> rfl
  rcases hc with rfl | rfl | rfl
  · have hp : check_CSR_priv 1#12 Privilege.User = pure true := by kernel_rfl
    have hacc : check_CSR_access 1#12 acc = true := by cases acc <;> kernel_rfl
    have hst : stateen_allows_CSR_access 1#12 Privilege.User acc = pure true := by kernel_rfl
    simp only [uxrCheckSc, hp, hacc, hst, pure_bind, Bool.and_self, ↓reduceIte, hite, bind_pure]
    kernel_walk h : runRead (uxrPin f) (is_CSR_accessible 1#12 Privilege.User acc)
    rw [h]; simp [hfs]
  · have hp : check_CSR_priv 2#12 Privilege.User = pure true := by kernel_rfl
    have hacc : check_CSR_access 2#12 acc = true := by cases acc <;> kernel_rfl
    have hst : stateen_allows_CSR_access 2#12 Privilege.User acc = pure true := by kernel_rfl
    simp only [uxrCheckSc, hp, hacc, hst, pure_bind, Bool.and_self, ↓reduceIte, hite, bind_pure]
    kernel_walk h : runRead (uxrPin f) (is_CSR_accessible 2#12 Privilege.User acc)
    rw [h]; simp [hfs]
  · have hp : check_CSR_priv 3#12 Privilege.User = pure true := by kernel_rfl
    have hacc : check_CSR_access 3#12 acc = true := by cases acc <;> kernel_rfl
    have hst : stateen_allows_CSR_access 3#12 Privilege.User acc = pure true := by kernel_rfl
    simp only [uxrCheckSc, hp, hacc, hst, pure_bind, Bool.and_self, ↓reduceIte, hite, bind_pure]
    kernel_walk h : runRead (uxrPin f) (is_CSR_accessible 3#12 Privilege.User acc)
    rw [h]; simp [hfs]

section
variable {D : UFoot} {s : UWSt}

/-- The `FS`-gated numbers: the short-circuit check walks to `CSR_Illegal`. -/
theorem uxr_ccr_fs (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (c : BitVec 12)
    (h : c = 1#12 ∨ c = 2#12 ∨ c = 3#12) (acc : CSRAccessType) :
    runRW D orc s (uxrResultSc c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), s, orc) := by
  obtain ⟨b, hb⟩ := uxr_checkCSR_fs s.file acc hc.fs c h
  unfold uxrResultSc
  rw [runRW_bind, uxr_runRW_of_pin hD hc orc _ _ _ hb]
  apply uxr_runRW_of_pin hD hc orc _ _ false
  rcases h with rfl | rfl | rfl <;> kernel_rfl

/-- **The short-circuit check at User** (Rocq `exec_check_CSR_result_U`):
every number walks to `CSR_Illegal`, state and oracle unchanged. -/
theorem uxr_ccrSc (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc) (c : BitVec 12) (acc : CSRAccessType) :
    runRW D orc s (uxrResultSc c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), s, orc) := by
  by_cases hd : uxrDflt c = true
  · exact uxr_runRW_of_pin hD hc orc _ _ _ (uxr_ccr_dflt s.file c acc hd)
  by_cases he : uxrExc c.toNat = true
  · apply uxr_ccr_fs hD hc orc c _ acc
    simp only [uxrExc, Bool.or_eq_true, Nat.beq_eq] at he
    rcases he with (h | h) | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simpa using h)))
    · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by simpa using h)))
  · obtain ⟨b, hb⟩ := uxr_ccr_spec s.file c acc (by simpa using hd) (by simpa using he)
    exact uxr_runRW_of_pin hD hc orc _ _ _ hb

/-- **The model's check at User, up to discarded reads**: every number but
`0x747`/`0x757` walks to `CSR_Illegal`, state and oracle unchanged. -/
theorem uxr_ccr (hD : UxrFoot D) (hc : UxrCfg s) (c : BitVec 12)
    (hz : c ≠ 0x747#12 ∧ c ≠ 0x757#12) (acc : CSRAccessType) :
    URunSc D s (check_CSR_result c Privilege.User acc)
      (fun orc => some (CSRCheckResult.CSR_Illegal (), s, orc)) :=
  URunSc.of_stut (uxr_resultSc_stut c _ acc hz.1 hz.2) fun orc => uxr_ccrSc hD hc orc c acc

/-! ## `doCSR` and the two families -/

/-- A register read, as a walk. -/
theorem uxr_readReg (orc : UOrc) (r : Register) (h : D.Dr r = true) :
    runRW D orc s (readReg r) = some (s.file r, s, orc) :=
  runRW_regRead_dr D orc s r _ h

/-- **`doCSR` at User** (Rocq `exec_doCSR_U`): `Illegal_Instruction`, nothing
written, whatever the operand, destination, operation and access type (up to
discarded reads). -/
theorem uxr_doCSR (hD : UxrFoot D) (hc : UxrCfg s) (c : BitVec 12)
    (hz : c ≠ 0x747#12 ∧ c ≠ 0x757#12) (v : BitVec 64) (rd : regidx) (op : csrop)
    (acc : CSRAccessType) :
    URunSc D s (doCSR c v rd op acc) (fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc)) := by
  unfold doCSR
  refine URunSc.bind (x := Privilege.User) (s' := s) (g := fun o => o)
    (res := fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc))
    (URunSc.of_runRW fun orc => ?_) ?_
  · rw [uxr_readReg orc .cur_privilege (hD _ (by decide)), hc.priv]
  · exact URunSc.bind (x := CSRCheckResult.CSR_Illegal ()) (s' := s) (g := fun o => o)
      (res := fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc))
      (uxr_ccr hD hc c hz acc) (URunSc.of_runRW fun _ => rfl)

/-- **`CSRImm` at User** (Rocq `exec_execute_CSRImm_total_U` +
`goodmb_execute_CSRImm_total_U`), up to discarded reads. -/
theorem uxr_execute_CSRImm (hD : UxrFoot D) (hc : UxrCfg s) (csr : BitVec 12)
    (hz : csr ≠ 0x747#12 ∧ csr ≠ 0x757#12) (imm : BitVec 5) (rd : regidx) (op : csrop) :
    URunSc D s (execute (.CSRImm (csr, imm, rd, op)))
      (fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc)) :=
  uxr_doCSR hD hc csr hz _ rd op _

/-- **`CSRReg` at User** (Rocq `exec_execute_CSRReg_total_U` +
`goodmb_execute_CSRReg_total_U`), up to discarded reads: the source GPR is
read (lane U1-X1's `uxa_rX`), then `doCSR`. -/
theorem uxr_execute_CSRReg (hA : UxaFoot D) (hD : UxrFoot D) (hc : UxrCfg s)
    (csr : BitVec 12) (hz : csr ≠ 0x747#12 ∧ csr ≠ 0x757#12) (rs1 rd : regidx) (op : csrop) :
    URunSc D s (execute (.CSRReg (csr, rs1, rd, op)))
      (fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc)) := by
  cases rs1 with
  | Regidx i =>
    show URunSc D s (execute_CSRReg csr (regidx.Regidx i) rd op) _
    unfold execute_CSRReg
    exact URunSc.bind (x := uxaXget s.file i) (s' := s) (g := fun o => o)
      (res := fun orc => some (ExecutionResult.Illegal_Instruction (), s, orc))
      (URunSc.of_runRW fun orc => uxa_rX hA orc s i) (uxr_doCSR hD hc csr hz _ rd op _)

end

/-! ## `mseccfg`: the model fails -/

/-- The generated `currentlyEnabled` has no `Ext_Zkr` clause: it is the
fall-through's assertion failure. -/
theorem uxr_currentlyEnabled_Zkr_error :
    (match currentlyEnabled .Ext_Zkr with
     | .impure (.error _) _ => true
     | _ => false) = true := by
  kernel_rfl

/-- **`mseccfg`/`mseccfgh` at User**: the check chain does not complete (it
reaches `currentlyEnabled Ext_Zkr`, an error), so a user `csrr` of them has
no Sail step. -/
theorem uxr_ccr_zkr (f : RegFile) (acc : CSRAccessType) :
    runRead (uxrPin f) (check_CSR_result 0x747#12 Privilege.User acc) = none ∧
    runRead (uxrPin f) (check_CSR_result 0x757#12 Privilege.User acc) = none :=
  ⟨by kernel_rfl, by kernel_rfl⟩

end MachCSL
