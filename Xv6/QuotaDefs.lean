/-
**The memory quota's arithmetic** (NI M3 quotas Q-1; kernel
`verified-quota`, design `claude-notes/projects/noninterference.md` "M3
quotas design" F4).

The quota kernel bounds every process's break by `MAXUSZ` = 768 KiB
(`UPtDefs.uQuota`, 192 pages) and the live pipe buffers by `NPIPE` = 50.
`kalloc.c` is unchanged: the pool is partitioned in the PROOF, by page
credits (`KcredDefs`).  This file is the partition's arithmetic, derived
from the geometry rather than transcribed:

* `ptNodesMax` = 5: a table whose user leaves lie below `uQuota ≤ 2 MiB`
  has at most five interior pages -- the root, the two level-1 nodes at
  root index 0 (the user region) and 255 (`TRAMPOLINE`/`TRAPFRAME`), and
  the level-0 nodes below them at index 0 and 511
  (`UPtShape.pages_le_of_shapeQ`, the "five-interior-page lemma");
* `ptW` = 197: a table's WEIGHT, the most pages it may ever own (its
  interior pages and one data page per user page below the quota);
* `slotShare` = 427: one slot's share of RAM -- the trapframe page, TWO
  tables (`kexec` builds the new image's table while the old one is live;
  `proc_freepagetable(oldpagetable)` runs last), and `sys_exec`'s argument
  pages (`MAXARG` = 32, `kalloc`ed before `kexec` and freed after);
* `credTotal` = 64 · 427 + 50 = 27378: every slot at full quota plus the
  pipe cap.

The free count it must fit under is the boot's: `kinit` frees
`kinitPages` = 32732 pages, `kvmmake` draws `kvmmakeCount` = 166 (its
interior pages and the 64 kernel stacks), `virtio_disk_init` 3; what is
left when `userinit` mints the credits is 32563 (`QuotaFit.totalFits`,
slack 5185).

Imports only definitional files.
-/
import Xv6.SlotSupply

namespace Xv6

/-- `MAXUSZ / PGSIZE`: the pages of the largest break (`UPtDefs.uQuota =
uQpages * 4096`). -/
def uQpages : Nat := 192

/-- **The interior pages of a quota table** (the design's "5-interior-page
lemma", `UPtShape.pages_le_of_shapeQ`): with every user leaf below `uQuota
≤ 2 MiB` (one level-0 node's reach) and the two fixed pages at the top of
the address space, a table has the root, one level-1 and one level-0 node
on the user path (root index 0, then 0), and one of each on the top path
(root index 255, then 511). -/
def ptNodesMax : Nat := 1 + 2 + 2

/-- **A table's weight**: the pages it may ever own -- its interior pages
and a data page for every user page below the quota.  A table holds its
weight as pages plus credits (`UPtDefs.ptOwnRep`). -/
def ptW : Nat := ptNodesMax + uQpages

/-- `sys_exec`'s argument pages: `MAXARG` (`KexecDefs.MAXARG`, the
`argv[MAXARG]` array `sys_exec` fills with `kalloc`ed pages before `kexec`). -/
def execArgPages : Nat := 32

/-- **One slot's share of RAM**: the trapframe page, the live table's
weight, the weight of the table `kexec` builds while the live one stands,
and `sys_exec`'s argument pages. -/
def slotShare : Nat := 1 + 2 * ptW + execArgPages

/-- `param.h`'s `NPIPE` (`NFILE / 2`): the live pipe buffers `pipealloc`
admits (`li a4,49 ; blt a4,a5` at `pipealloc+0x3e`). -/
def NPIPE : Nat := 50

/-- **The pages the credits reserve**: every slot's share and the pipe cap. -/
def credTotal : Nat := NPROC * slotShare + NPIPE

/-- **A live process's spare credits**: the weight of the table `kexec`
builds beside the live one, and `sys_exec`'s argument pages.  The block's
core holds them (`FdTable.procPrivCoreNoctxAt`); a ZOMBIE's dormant space
keeps them (`ProcDefs.dormantSpace`). -/
def procSpare : Nat := ptW + execArgPages

/-- A slot's share splits as the trapframe, the live table, and the live
process's spare (`procSpare`). -/
theorem slotShare_split : slotShare = 1 + ptW + procSpare := by
  unfold slotShare procSpare; omega

end Xv6
