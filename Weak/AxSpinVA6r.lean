/-
Weak: **the spinlock plan, PHASE 5 item (4)** — the register-only (`rfF`) footprints of the
S-mode exception trap's pieces: `trap_handler Supervisor` (any cause, tval, extension payload)
and `exception_delegatee`.

Rocq: `iris/AxSpinVA6r.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. Tactics: Rocq's local `pcfg` (reduce the `get_config_print_*` constants) is not needed
   (`AxSpineOk2`'s `rff_step` covers an `if` on a print constant on both branches;
   `print_endline` is pure).  Rocq `rfF_auto2` ↦ the local tactics `va6r_auto` / `va6r_auto2`:
   `rff_auto` that first tries the Lean-only callee lemmas below (at reducible transparency —
   at default transparency a failed `exact` unfolds the whole tree and times out).
2. The trap-tracking callback `csr_name_write_callback name v` runs lean-sail's
   `csr_name_map_backwards name`, a ~350-arm string match: unfolding it in `rff_step` exceeds
   the recursion depth, and splitting it at a free name times out.  The four names the S-mode
   trap uses (`mstatus`, `scause`, `stval`, `sepc`) are discharged by evaluation
   (`AxSpinVA6r.rfFCsrNameWrite*`, proof `True.intro`), and `trap_handler`'s callees are proved
   one by one (`AxSpinVA6r.rfFCurrentlyEnabledS`/`H`, `rfFPrivLevelToStrS`,
   `rfFZicfilpPreserveElpS`, `rfFPrepareTrapVectorS`, `rfFTrackTrapS`).
3. Imports: only `Weak.AxSpineOk2` (Rocq also imports `WeakSailComplete`, `AxSymEngine`, which
   these lemmas do not use).

**Rocq → Lean name map.**  `rfF_trap_handler_S` `rfFTrapHandlerS`, `rfF_exception_delegatee`
`rfFExceptionDelegatee`; tactics `pcfg`/`rfF_auto2` ↦ `va6r_auto`/`va6r_auto2` (local).  None is
in the duplicated-name table.  Lean-only (file-qualified): `AxSpinVA6r.rfFCsrNameWriteMstatus`/
`Scause`/`Stval`/`Sepc`, `AxSpinVA6r.rfFCurrentlyEnabledS`/`rfFCurrentlyEnabledH`,
`AxSpinVA6r.rfFPrivLevelToStrS`, `AxSpinVA6r.rfFZicfilpPreserveElpS`,
`AxSpinVA6r.rfFPrepareTrapVectorS`, `AxSpinVA6r.rfFTrackTrapS`.

**Dropped:** none.
-/
import Weak.AxSpineOk2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # Callees (Lean-only) -/

theorem AxSpinVA6r.rfFCsrNameWriteMstatus (v : BitVec 64) :
    rfF (csr_name_write_callback "mstatus" v) := True.intro
theorem AxSpinVA6r.rfFCsrNameWriteScause (v : BitVec 64) :
    rfF (csr_name_write_callback "scause" v) := True.intro
theorem AxSpinVA6r.rfFCsrNameWriteStval (v : BitVec 64) :
    rfF (csr_name_write_callback "stval" v) := True.intro
theorem AxSpinVA6r.rfFCsrNameWriteSepc (v : BitVec 64) :
    rfF (csr_name_write_callback "sepc" v) := True.intro

theorem AxSpinVA6r.rfFCurrentlyEnabledS : rfF (currentlyEnabled .Ext_S) := by rff_auto
theorem AxSpinVA6r.rfFCurrentlyEnabledH : rfF (currentlyEnabled .Ext_H) := by rff_auto
theorem AxSpinVA6r.rfFPrivLevelToStrS : rfF (privLevel_to_str .Supervisor) := by rff_auto
theorem AxSpinVA6r.rfFZicfilpPreserveElpS : rfF (zicfilp_preserve_elp_on_trap .Supervisor) := by
  rff_auto
theorem AxSpinVA6r.rfFPrepareTrapVectorS (x : BitVec 64) :
    rfF (prepare_trap_vector .Supervisor x) := by rff_auto

/-- `rff_auto` with the CSR-name callbacks first. -/
local macro "va6r_auto" : tactic => `(tactic| repeat (first
      | with_reducible exact AxSpinVA6r.rfFCsrNameWriteMstatus _
      | with_reducible exact AxSpinVA6r.rfFCsrNameWriteScause _
      | with_reducible exact AxSpinVA6r.rfFCsrNameWriteStval _
      | with_reducible exact AxSpinVA6r.rfFCsrNameWriteSepc _
      | rff_step
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | exact True.intro
      | rfl))

theorem AxSpinVA6r.rfFTrackTrapS (b : Bool) (c : BitVec 6) :
    rfF (track_trap .Supervisor b c) := by
  unfold track_trap long_csr_write_callback
  va6r_auto

/-- `rff_auto` with all of `trap_handler Supervisor`'s callees first (Rocq `rfF_auto2`). -/
local macro "va6r_auto2" : tactic => `(tactic| repeat (first
      | with_reducible exact AxSpinVA6r.rfFCurrentlyEnabledS
      | with_reducible exact AxSpinVA6r.rfFCurrentlyEnabledH
      | with_reducible exact AxSpinVA6r.rfFPrivLevelToStrS
      | with_reducible exact AxSpinVA6r.rfFZicfilpPreserveElpS
      | with_reducible exact AxSpinVA6r.rfFPrepareTrapVectorS _
      | with_reducible exact AxSpinVA6r.rfFTrackTrapS _ _
      | rff_step
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | exact True.intro
      | rfl))

/-! # The S-mode trap's pieces -/

theorem rfFTrapHandlerS (c : TrapCause) (pc : BitVec 64) (info : Option (BitVec 64))
    (ext : Option Unit) : rfF (trap_handler .Supervisor c pc info ext) := by
  va6r_auto2

theorem rfFExceptionDelegatee (e : ExceptionType) (p : Privilege) :
    rfF (exception_delegatee e p) := by
  rff_auto

end Weak
