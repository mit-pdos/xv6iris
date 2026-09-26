/-
MachCSL: the CSR check chain is read-only and total (lane AND-ELIM), except
at `mseccfg`/`mseccfgh` (`0x747`/`0x757`), whose `is_CSR_accessible` clause
EAGERLY reaches `currentlyEnabled Ext_Zkr` (no clause: `assert false`).

* `ro_check_CSR_priv`, `ro_stateen_allows_CSR_access`: every number, every
  privilege;
* `ro_is_CSR_accessible`, `ro_check_CSR`, `ro_is_CSR_exception_virtual`:
  every number but `0x747`/`0x757`, every privilege.

These are the side conditions of the check chain's short-circuit form
(`MachCSL/UExecCsrSc.lean`).
-/
import MachCSL.SailROModel

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

theorem ro_check_CSR_priv (c : BitVec 12) (p : Privilege) : SailRO (check_CSR_priv c p) := by
  unfold check_CSR_priv privLevel_to_CSR_privbits
  sail_ro

theorem ro_stateen_allows_CSR_access (c : BitVec 12) (p : Privilege) (acc : CSRAccessType) :
    SailRO (stateen_allows_CSR_access c p acc) := by
  unfold stateen_allows_CSR_access
  sail_ro

/-- Refute the `0x747`/`0x757` arm of a split dispatcher. -/
local macro "ro_csr_zkr" : tactic => `(tactic| (
  rename_i heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, -⟩ := heq
  contradiction))

theorem ro_is_CSR_accessible (c : BitVec 12) (p : Privilege) (acc : CSRAccessType)
    (h1 : c ≠ 0x747#12) (h2 : c ≠ 0x757#12) : SailRO (is_CSR_accessible c p acc) := by
  unfold is_CSR_accessible
  dsimp only
  split
  all_goals first | ro_csr_zkr | sail_ro

theorem ro_check_CSR (c : BitVec 12) (p : Privilege) (acc : CSRAccessType)
    (h1 : c ≠ 0x747#12) (h2 : c ≠ 0x757#12) : SailRO (check_CSR c p acc) := by
  unfold check_CSR
  exact SailRO.bind (ro_check_CSR_priv c p) fun _ =>
    SailRO.bind (ro_is_CSR_accessible c p acc h1 h2) fun _ =>
      SailRO.bind (ro_stateen_allows_CSR_access c p acc) fun _ => .pure _

theorem ro_is_CSR_exception_virtual (c : BitVec 12) (p : Privilege) (acc : CSRAccessType)
    (h1 : c ≠ 0x747#12) (h2 : c ≠ 0x757#12) : SailRO (is_CSR_exception_virtual c p acc) := by
  unfold is_CSR_exception_virtual
  dsimp only
  split
  case h_12 =>
    rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -, rfl⟩ := heq
    exact ro_check_CSR _ _ _ h1 h2
  all_goals exact SailRO.pure _

end MachCSL
