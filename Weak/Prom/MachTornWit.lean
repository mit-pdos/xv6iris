/-
Weak/Prom: **TornWit — machine v2 admits a TORN aligned same-size word load that RVWMO forbids** (fidelity check of
advisor review `~/dev/weak-orch/promising/mini/review-R2.md` F3).

Claim: `loadOk` (Machine.lean:325–333) exempts a byte FORWARDED from the hart's own latest store (`fwdHit`,
Machine.lean:293) from the common read point (floor `max vpre (coh a)` instead of `max vpre (nonFwdMax …)`), so an
aligned word load may take byte 0 from the hart's own store and bytes 1–3 from a coherence-later store of another
hart.  RVWMO forbids this: the load value axiom (rvwmo.adoc, "Each byte of each load i returns the value written to
that byte by the store that is the latest in global memory order among the following stores: (1) Stores that write
that byte and that precede i in the global memory order (2) Stores that write that byte and that precede i in
program order") picks, per byte, the gmo-latest of a candidate set; for aligned same-size word stores to `X` the
candidate sets of the four bytes coincide, so all four bytes come from ONE store.

* `tornT` — the test (RefTests.lean `mk` style).  Image 0.
    hart 0: `sw a1,0(a2)` [a1 = 0x01010101, a2 = X]; `lw a0,0(a2)`
    hart 1: `sw a1,0(a2)` [a1 = 0x02020202, a2 = X]
  condition: hart 0's `a0 = 0x02020201`.
* `mach_torn : allowedMach tornT` — machine v2 has a valid complete run with that outcome (certificate replayed by
  the kernel, `certOk_sound`, MachCert.lean).
* `ref_torn : forbiddenRef tornT` — the reference forbids it (`forbid_sound`, RefCheck.lean).
-/
import Weak.Prom.MachCert
import Weak.Prom.RefTests

namespace Weak.Prom.Mach.TornWit

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref Weak.Prom.Ref.Lit
open PLabel

/-- THE TORN-WORD TEST (review-R2 F3).  ABI: a0 10, a1 11, a2 12. -/
def tornT : Test := mk [[sw 11 12, lw 10 12], [sw 11 12]]
  [[(11, 0x01010101), (12, X)], [(11, 0x02020202), (12, X)]] [] (r 0 10 0x02020201)

/-- The run: hart 0 promises its word at timestamp 1, hart 1 at timestamp 2; both fulfil; hart 0's `lw` answers
byte 0 with timestamp 1 (FORWARDED: `fwdHit`, floor `max vpre (coh X) = 1`, no write to X in `(1, 1]`) and bytes
1–3 with timestamp 2 (not forwarded, floor `nonFwdMax = 2`, no write in `(2, 2]`). -/
def cert_torn : List PEvt :=
  [.prom 0 ⟨4096, [1#8, 1#8, 1#8, 1#8], some 0, .plain⟩,
   .prom 1 ⟨4096, [2#8, 2#8, 2#8, 2#8], some 1, .plain⟩,
   .st 0 (LStore false false 4096 [1#8, 1#8, 1#8, 1#8] [.DReg 12] [.DReg 11]) (some 1),
   .st 0 (LInstr) none,
   .st 1 (LStore false false 4096 [2#8, 2#8, 2#8, 2#8] [.DReg 12] [.DReg 11]) (some 2),
   .st 1 (LInstr) none,
   .st 0 (LLoad false false 4096 [(1, 1#8), (2, 2#8), (2, 2#8), (2, 2#8)] [.DReg 12]) none,
   .st 0 (LRegW 10 [.DLdRes]) none,
   .st 0 (LInstr) none]

/-- MACHINE V2 ALLOWS THE TORN WORD. -/
theorem mach_torn : allowedMach tornT := certOk_sound _ cert_torn (by decide +kernel)

/-- THE REFERENCE FORBIDS IT. -/
theorem ref_torn : forbiddenRef tornT := forbid_sound _ (by decide +kernel)

/-- Non-vacuity: the reference has an execution of `tornT`. -/
theorem ref_torn_exec : allowedRef (anyOutcome tornT) := exists_sound _ (by decide +kernel)

end Weak.Prom.Mach.TornWit

#print axioms Weak.Prom.Mach.TornWit.mach_torn
#print axioms Weak.Prom.Mach.TornWit.ref_torn
#print axioms Weak.Prom.Mach.TornWit.ref_torn_exec
