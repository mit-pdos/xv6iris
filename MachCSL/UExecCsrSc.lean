/-
MachCSL: the CSR check chain, SHORT-CIRCUIT (lane AND-ELIM, applied to lane
U1-X3's CSR family).

Sail's `check_CSR` is `check_CSR_priv & check_CSR_access & is_CSR_accessible
& stateen_allows_CSR_access` with short-circuit `&`, and `check_CSR_result`
consults `is_CSR_exception_virtual` only at a virtual privilege.  The Lean
backend runs every operand (`(← …) && (← …)` is hoisted), so the model's
chain at User also runs the stateen check of `sstateen1..3`/`hstateen1..3`
(reading `mstateen1..3`/`sstateen1..3`) and the whole Supervisor-level
check behind `is_CSR_exception_virtual`.

`uxrCheckSc` / `uxrResultSc` are the chain as Sail runs it, and
`uxr_checkSc_stut` / `uxr_resultSc_stut` relate them to the model's own
functions (`SailStut`): the discarded operands are read-only and total
(`MachCSL/SailROCsr.lean`) at every number but `0x747`/`0x757`, where the
eager model genuinely fails (the missing `currentlyEnabled Ext_Zkr` clause).
The CSR facts (`MachCSL/UExecCsr.lean`) walk the short-circuit chain and are
stated for the model's `execute` up to discards (`URunSc`), so their
footprint no longer reads `mstateen1..3`/`sstateen1..3`.
-/
import MachCSL.UExecCsrBase
import MachCSL.SailROCsr
import MachCSL.SailAndElim

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `check_CSR`, short-circuit: the accessibility check only after the
privilege and read-only gates, the stateen check only after that. -/
def uxrCheckSc (c : BitVec 12) (p : Privilege) (acc : CSRAccessType) : SailM Bool :=
  check_CSR_priv c p >>= fun x =>
    if x && check_CSR_access c acc then
      is_CSR_accessible c p acc >>= fun y =>
        if y then stateen_allows_CSR_access c p acc >>= pure else pure false
    else pure false

/-- `check_CSR_result`, short-circuit: the virtual-instruction check only at a
virtual privilege. -/
def uxrResultSc (c : BitVec 12) (p : Privilege) (acc : CSRAccessType) : SailM CSRCheckResult :=
  uxrCheckSc c p acc >>= fun ok =>
    if ok = true then pure (CSRCheckResult.CSR_Check_OK ())
    else if (p == Privilege.VirtualSupervisor || p == Privilege.VirtualUser) = true then
      is_CSR_exception_virtual c p acc >>= fun v =>
        if v = true then pure (CSRCheckResult.CSR_Virtual ()) else pure (CSRCheckResult.CSR_Illegal ())
    else pure (CSRCheckResult.CSR_Illegal ())

/-- The model's `check_CSR` is its short-circuit form with discarded reads. -/
theorem uxr_checkSc_stut (c : BitVec 12) (p : Privilege) (acc : CSRAccessType)
    (h1 : c ≠ 0x747#12) (h2 : c ≠ 0x757#12) : SailStut (uxrCheckSc c p acc) (check_CSR c p acc) := by
  unfold uxrCheckSc check_CSR
  exact SailStut.and3 (check_CSR_priv c p) (check_CSR_access c acc)
    (ro_is_CSR_accessible c p acc h1 h2) (ro_stateen_allows_CSR_access c p acc) pure

/-- The model's `check_CSR_result` is its short-circuit form with discarded
reads. -/
theorem uxr_resultSc_stut (c : BitVec 12) (p : Privilege) (acc : CSRAccessType)
    (h1 : c ≠ 0x747#12) (h2 : c ≠ 0x757#12) :
    SailStut (uxrResultSc c p acc) (check_CSR_result c p acc) := by
  unfold uxrResultSc check_CSR_result
  exact SailStut.bind (uxr_checkSc_stut c p acc h1 h2) fun _ =>
    SailStut.ite (fun _ => .refl _) (fun _ =>
      SailStut.and (p == Privilege.VirtualSupervisor || p == Privilege.VirtualUser)
        (ro_is_CSR_exception_virtual c p acc h1 h2)
        (fun z => if z = true then pure (CSRCheckResult.CSR_Virtual ())
          else pure (CSRCheckResult.CSR_Illegal ())))

end MachCSL
