/-
**The quota's fit** (NI M3 quotas Q-1; design "M3 quotas" F4): the page
credits reserve `credTotal = NPROC * slotShare + NPIPE` pages, minted when
`userinit` seals the allocator's count; this file proves they fit the free
pool left at that point.

The boot's counts are exact in the specs: `kinit` frees `kinitPages`
(`SpecKinit`, 32732: `[end, PHYSTOP)` rounded), `kvmmake` draws
`kvmmakeCount` (`KvmDefs`, 166: its interior pages and the 64 kernel
stacks), `virtio_disk_init` draws 3 (its descriptor, avail and used rings),
and `userinit`'s `allocproc` at most `procPagetableNodes + 1` before the
mint.  `ProofMain` hands `userinit` `nb = kinitPages - kvmmakeCount - 3`.

Imports only definitional files.
-/
import Xv6.QuotaDefs
import Xv6.SpecKinit
import Xv6.KvmDefs
import Xv6.SpecProcPagetable

namespace Xv6

/-- **The free pages after the boot's draws**, when `userinit` runs:
`kinit`'s, less `kvmmake`'s and `virtio_disk_init`'s. -/
def freePagesAfterBoot : Nat := kinitPages - kvmmakeCount - 3

theorem freePagesAfterBoot_val : freePagesAfterBoot = 32563 := by decide

/-- **THE FIT** (design F4): every slot at full quota and the pipe cap fit
the free pool -- 64 · 427 + 50 = 27378 ≤ 32563 (slack 5185). -/
theorem totalFits : NPROC * slotShare + NPIPE ≤ freePagesAfterBoot := by decide

/-- What `userinit` is handed (`SpecUserinit`'s `hnb`): the credits, and
room for `allocproc`'s draws before the mint. -/
theorem userinit_nb_fits : credTotal + procPagetableNodes + 1 ≤ freePagesAfterBoot := by
  have := totalFits
  unfold credTotal procPagetableNodes
  have h : freePagesAfterBoot = 32563 := freePagesAfterBoot_val
  unfold NPROC slotShare ptW ptNodesMax uQpages execArgPages NPIPE at *
  omega

end Xv6
