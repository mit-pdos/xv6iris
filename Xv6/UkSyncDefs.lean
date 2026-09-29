/-
**The `sync` program: what its walks are stated over** (Rocq `UkSync.v`
§0, the payment `sync_pay`, and `UCodeSync.v`'s catalog, as landed by
b23e6791f -- drift SY2; the walks are one function per file: `UkSyncStubs`
(the usys.S stubs `exit` and `sync`), `SpecSyncMain` / `ProofSyncMain`,
`SpecSyncStart` / `ProofSyncStart`).

    int main(void) { sync(); exit(0); }

THE PAYMENT /sync MAKES, AND WHEN (Rocq's sync design section 3).  The
process is handed `P` at its entry and owes its parent the payload `R` at its
exit; `syncPay P R` turns the one into the other, and it is spent in `main`
AFTER `sync()` returned -- the one point of the program at which the call's
effect is complete.  At a trivial payload it is free (`syncPay_triv`); the
union's round pays PEND at RAN with it (`UkSyncEntry`, `UshURoundSync`).

## Deviations from Rocq

1. **DU3**: sync's code is `ukCode γt User.Sync.code.byte` (Rocq
   `sync_code γt`), each instruction fact an evaluation of sync's text
   (`sync_uis`, Rocq `UCodeSync.uis_sync_<pc>`), as `UkSeccDefs`.
2. **Pre-hook shape** (drift lane D2-sync ruling): `sync_pay P R := P -∗ R`
   is b23e6791f's.  Rocq main's `sync_pay P Qr R := P -∗ Qr -∗ R`, the
   `ksync_leaf oQ` parameter and `hook_opt`/`Q_opt` (sync K4 6ec6feccd, A4
   a2417c11e) belong to the durability lanes (D2-dur / E) and are NOT ported
   here: the ecall at 0x36a is the CURRENT quiet leaf (`UK_SYS_P.quiet`, 22 a
   free number).
-/
import Xv6.UkStub
import Xv6.UkRunMem
import Xv6.UkSysP
import Xv6.User.SyncText

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open LeanRV64D LeanRV64D.Functions

set_option linter.unusedSectionVars false

/-- **Rocq `sync_pay`** (deviation 2: b23e6791f's, pre-hook). -/
abbrev syncPay {PROP : Type _} [BI PROP] (P R : PROP) : PROP := iprop(P -∗ R)

/-- **Rocq `sync_pay_triv`**. -/
theorem syncPay_triv {PROP : Type _} [BI PROP] (P : PROP) : ⊢ syncPay P iprop(True) := by
  unfold syncPay
  iintro -
  ipureintro; trivial

section Code
variable {GF : BundledGFunctors} [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat]

/-- **sync's catalog, once** (Rocq `UCodeSync.uis_sync_<pc>`). -/
theorem sync_uis (γt : GName) (pc : Nat) (rvc : Bool) (i : instruction)
    (h : ∃ i₀ n w, User.utextDecodeWith udrefU User.Sync.tree User.Sync.code.byte pc =
      some (rvc, i, i₀, n, w))
    (hpc : pc < 2 ^ 64) :
    ukCode (GF := GF) γt User.Sync.code.byte ⊢ uinstrIs γt (BitVec.ofNat 64 pc) rvc i := by
  obtain ⟨i₀, n, w, e⟩ := h
  exact uinstrIs_of_text γt User.Sync.textOk pc rvc i i₀ n w e hpc

/-- A two-word frame, opened (Rocq `ustack_2`; main never returns). -/
theorem sync_ustack_two (γd : GName) (sp : BitVec 64) :
    ustack (GF := GF) γd sp 2 ⊢
      (∃ w : BitVec 64, uword γd (sp.toNat - 8) w) ∗ (∃ w : BitVec 64, uword γd (sp.toNat - 16) w) := by
  unfold ustack ustackBody
  rw [show List.range 2 = [0, 1] from rfl]
  iintro ⟨-, H0, H1, -⟩
  isplitl [H0]; · iexact H0
  iexact H1


end Code

end Xv6
