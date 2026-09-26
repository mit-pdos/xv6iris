/-
MachCSL: the model's EAGER CSR check at User, as a plain `runRW` walk over the
user footprint's read set (lane U3-A; Rocq `UserCsr.v` §3).

Lane U1-X3's CSR facts (after AND-ELIM) walk the SHORT-CIRCUIT chain
(`uxrResultSc`) and state `execute` up to discarded reads (`URunSc`).  The
user loop's execute contract `UstExecOk` (UserStepLand, lane U3-L) is a plain
`runRW` equation for the model's own (eager) `uxaExecAs i`, so it needs the
EAGER walk.  That walk succeeds at U1-X3's pin `uxrPin` (the user
footprint's nine cells) for every number except the eleven of `uclEager`:
the nine stateen-1..3-gated numbers `0x10D..0x10F`/`0x60D..0x60F`/
`0x61D..0x61F` (the eager chain reads `mstateen1..3`/`sstateen1..3`, off the
footprint) and `0x747`/`0x757` (no Sail step, `uxr_ccr_zkr`).  This file:
`uclEager`, the default class and the `FS`-gated numbers of the eager chain at
`uxrPin`; `UclCsrTab` the named numbers; `UclCsr` the families.

Once the user loop consumes `URunSc` (see Xv6/UserClassifySc), these three
files are redundant and can go.
-/
import MachCSL.UExecCsrDflt

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## The eager numbers -/

/-- **The CSR numbers the eager `&&` breaks at the user footprint**: the
stateen-1..3-gated nine (they read `mstateen1..3`/`sstateen1..3`, off the
footprint) and `mseccfg`/`mseccfgh` (no Sail step, `uxr_ccr_zkr`). -/
def uclEager (n : Nat) : Bool :=
  Nat.beq n 0x10D || Nat.beq n 0x10E || Nat.beq n 0x10F || Nat.beq n 0x60D || Nat.beq n 0x60E ||
  Nat.beq n 0x60F || Nat.beq n 0x61D || Nat.beq n 0x61E || Nat.beq n 0x61F || Nat.beq n 0x747 ||
  Nat.beq n 0x757

/-! ## The default class and the `FS`-gated numbers at `uxrPin` -/

/-- The default class: the check at `uxrPin` is `CSR_Illegal` (U1-X3's
`uxr_ccr_dflt`, at the smaller pin). -/
theorem ucl_ccr_dflt (f : RegFile) (c : BitVec 12) (acc : CSRAccessType) (h : uxrDflt c = true) :
    runRead (uxrPin f) (check_CSR_result c Privilege.User acc) = some (CSRCheckResult.CSR_Illegal (), true) := by
  unfold check_CSR_result
  simp only [check_CSR, uxr_isAcc_dflt _ _ _ h, uxr_stateen_dflt _ _ _ h, uxr_excVirt_dflt _ _ _ h,
    pure_bind, Bool.false_and, Bool.and_false]
  kernel_rfl

/-- The `FS`-gated numbers: under `FS = 0` the check answers `false` (U1-X3's
`uxr_checkCSR_fs`, at the smaller pin). -/
theorem ucl_checkCSR_fs (f : RegFile) (acc : CSRAccessType) (hfs : _get_Mstatus_FS (f .mstatus) = 0#2)
    (c : BitVec 12) (hc : c = 1#12 ∨ c = 2#12 ∨ c = 3#12) :
    ∃ b, runRead (uxrPin f) (check_CSR c Privilege.User acc) = some (false, b) := by
  rcases hc with rfl | rfl | rfl
  · kernel_walk h : runRead (uxrPin f) (check_CSR 1#12 Privilege.User acc)
    rw [h]; simp [hfs]
  · kernel_walk h : runRead (uxrPin f) (check_CSR 2#12 Privilege.User acc)
    rw [h]; simp [hfs]
  · kernel_walk h : runRead (uxrPin f) (check_CSR 3#12 Privilege.User acc)
    rw [h]; simp [hfs]

end MachCSL
