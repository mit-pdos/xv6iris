/-
Weak: **`dataOkR` (3k) — THE EXECUTE STAGE of a walk load/store under `dkB`: it RETIRES**
(`execute_LOAD` / `execute_STORE`, `InstsEnd.lean:17779,18244`, through the one `ExecuteAs`
redirect of a compressed form, `MachCSL.uxaExecAs`): under the interface's filters the access
takes no exception, so no trap result reaches the trap handler (`PROGRESS-dataOk.md`).  Lean-only.
Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkVmem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **A walk load retires.** -/
theorem dkExecLoad (c : DCfg) (hr : c.ram) (imm : BitVec 12) (rs1 rd : regidx) (u : Bool) (w : Int)
    (hw : accW w.toNat) (hbase : (uxaIdx rs1).toNat = c.base) (h0 : c.base ≠ 0)
    (hva : (c.va imm).toNat < 2 ^ 38) (hv : c.vpn = vpnOf (c.va imm)) (hal : (c.va imm).toNat % w.toNat = 0) :
    dkB c (fun r => r = RETIRE_SUCCESS) (execute (.LOAD (imm, rs1, rd, u, w))) := by
  simp only [execute, execute_LOAD]
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  refine dkBind _ _ _ _ (dkVmemRead c hr rs1 imm _ hw hbase h0 hva hv hal) (fun r h => ?_)
  match r with
  | .Err e => exact absurd rfl (h e)
  | .Ok d => exact dkBind _ _ _ _ (dkOfFp _ _ (SailCycleOrderFp.fpWXBits _ _)) (fun _ _ => rfl)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **A walk store retires.** -/
theorem dkExecStore (c : DCfg) (hr : c.ram) (hp : c.perm = .rw) (imm : BitVec 12) (rs2 rs1 : regidx) (w : Int)
    (hw : accW w.toNat) (hbase : (uxaIdx rs1).toNat = c.base) (h0 : c.base ≠ 0)
    (hva : (c.va imm).toNat < 2 ^ 38) (hv : c.vpn = vpnOf (c.va imm)) (hal : (c.va imm).toNat % w.toNat = 0) :
    dkB c (fun r => r = RETIRE_SUCCESS) (execute (.STORE (imm, rs2, rs1, w))) := by
  simp only [execute, execute_STORE]
  refine dkXfT _ _ (by xf_walk) (fun _ => ?_)
  refine dkBind (fun _ => True) _ _ _ (dkOfFp _ _ (SailCycleOrderFp.fpRXBits _)) (fun d _ => ?_)
  simp only [pure_bind]
  refine dkBind _ _ _ _ (dkVmemWrite c hr hp rs1 imm _ hw hbase h0 hva hv hal _) (fun r h => ?_)
  match r with
  | .Err e => exact absurd rfl (h e)
  | .Ok _ => rfl

set_option maxHeartbeats 40000000 in
/-- **(3) THE PER-ACCESS SAIL OBLIGATION, DISCHARGED**: the walk instruction at `pc` whose access
`dAccOk` describes RETIRES under the interface's filters — its `uxaExecAs` (the redirect included)
answers `RETIRE_SUCCESS` along every filter-admitted path. -/
theorem dkExecWalkAcc (pc : Int) (c : DCfg) (hr : c.ram) (h : dAccOk pc c) :
    ∃ a, PinWalkTab.decS pc = some a ∧ dkB c (fun r => r = RETIRE_SUCCESS) (uxaExecAs a) := by
  obtain ⟨a, b, rs1, imm, w, st, hdec, hab, hacc, hw, hbase, h0, hv, hal, hva, hst⟩ := h
  refine ⟨a, hdec, ?_⟩
  have hexec : dkB c (fun r => r = RETIRE_SUCCESS) (execute b) := by
    cases b with
    | LOAD x =>
      obtain ⟨imm', rs1', rd, u, w'⟩ := x
      simp only [memAcc, Option.some.injEq, Prod.mk.injEq] at hacc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hacc
      exact dkExecLoad c hr _ _ rd u _ hw hbase h0 hva hv.symm hal
    | STORE x =>
      obtain ⟨imm', rs2, rs1', w'⟩ := x
      simp only [memAcc, Option.some.injEq, Prod.mk.injEq] at hacc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hacc
      exact dkExecStore c hr (hst rfl) _ rs2 _ _ hw hbase h0 hva hv.symm hal
    | _ => simp [memAcc] at hacc
  unfold uxaExecAs
  rcases hab with rfl | he
  · refine dkBind _ _ _ _ hexec (fun r hr' => ?_)
    subst hr'
    rfl
  · rw [he, pure_bind]
    exact hexec

end PinDataOk
end Weak
