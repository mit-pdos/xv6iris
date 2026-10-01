/-
**The pure fact that vmfault's success arm cannot fire for a process whose
lazy flag is off** (Rocq `iris/VmfaultQuiet.v`, commit 7cec90c7b;
NI-STRONG-INSTANCE R4).

`SpecVmfault`'s success arm (the one that allocates a page and inserts it
at `vpnOf va`) requires

    va.toNat < sz.toNat     and     get? P.um (vpnOf va).toNat = none.

A process with the lazy flag off carries `lazyFree P.um sz`: every page
below the rounded-up size is already mapped.  The fault address's page is
one of those live pages (`vmfaultVpnLive`), so the success arm is
contradictory (`vmfaultQuiet`): at `lazyFree` vmfault never reaches kalloc.

This is the fault arm of the in-logic strong instance -- a quiet
(non-syscall) round cannot allocate through vmfault.  No Iris, no ghost
state; nothing imports it yet (the fault row's discharge when the permit
sweep is done).

Design: `claude-notes/design/ni-strong-instance.md` (§0, §3 "The vmfault
fact").

## Deviations from Rocq

  * **The rounding.**  Rocq names the page `svpn_of (PGROUNDDOWN va)`; this
    tree's `SpecVmfault` names it `vpnOf va` (`MachCSL.KMap`, bits 12..38),
    which ignores the offset bits, so no rounding appears.
  * **"Live" is pointwise.**  Rocq states `vmfault_vpn_live` as membership
    in the set `live_pages (uint szv)`; this tree has no `livePages` set --
    `lazyFree` (`Xv6/UPtDefs.lean`) is stated pointwise over `Nat` keys,
    `k * 4096 < pgRoundUpN sz.toNat`, so `vmfaultVpnLive` states exactly
    that premise for `k = (vpnOf va).toNat`.
  * **No size bound.**  Rocq needs `uint szv <= 2 ^ 38` because its map is
    keyed by `mword 27` (the page number must not wrap).  Here the keys are
    `Nat` and `(vpnOf va).toNat * 4096 ≤ va.toNat` holds outright, so both
    theorems drop the premise (they are strictly stronger; a caller holding
    vmfault's `hsz` simply does not pass it).
-/
import Xv6.UPtDefs

namespace Xv6

open MachCSL

/-- **The fault address's page is live below the size** (Rocq
`vmfault_vpn_live`): `vpnOf va` is a page `lazyFree` covers. -/
theorem vmfaultVpnLive (szv va : BitVec 64) (hva : va.toNat < szv.toNat) :
    (vpnOf va).toNat * 4096 < pgRoundUpN szv.toNat := by
  have h : (vpnOf va).toNat = va.toNat / 4096 % 2 ^ 27 := by
    unfold vpnOf; simp [Nat.shiftRight_eq_div_pow]
  rw [h]; unfold pgRoundUpN; omega

/-- **THE QUIET FACT** (Rocq `vmfault_quiet`): at `lazyFree`, vmfault's
success arm -- `va` below the size and its page absent from the map -- is
impossible. -/
theorem vmfaultQuiet (um : RegMapF (BitVec 64)) (szv va : BitVec 64)
    (hlf : lazyFree um szv) (hva : va.toNat < szv.toNat)
    (hnone : Iris.Std.PartialMap.get? um (vpnOf va).toNat = none) : False := by
  have h := hlf _ (vmfaultVpnLive szv va hva)
  rw [hnone] at h
  exact Bool.false_ne_true h

end Xv6
