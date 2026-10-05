/-
**THE FS-EVENT LEDGER's RECEIPTS** (NI M3 private files; design of record
`claude-notes/projects/noninterference.md`, "M3 private files design
(2026-10-05)", findings F3/F7, rulings FS-R2/R3/R5).

Lane FS-0 lands the exhaustion receipt's NAME and threads it from the three
out-of-resources sites to the syscall posts: `fsFullRcpt γfs act why`,
"actor `act` was told, in the era whose file system is `γfs`, that table
`why` is full".  FS-0 carries it as the bare verdict (`True`); lane FS-1
anchors it in the era's fs-event ledger (a lower bound ending in
`Fev.full act why`) by changing THIS definition and the sites that make it,
and no statement that merely carries it.

It is keyed by the era's `FsNames`, not by a `WchG` name: the receipt rides
open's and mkdir's receipts (`SpecSysOpen.openReceiptCreate`,
`SpecSysMkdir.mkdirArms`), which the U tier states in sections with no
`WchG` instance (the allocator's ledger `fsReadyKmem.pend` is keyed the
same way).
-/
import Xv6.NiFs
import Xv6.FsBlocks

namespace Xv6

open Iris Iris.BI

/-- (NI M3 FS-0) **THE EXHAUSTION RECEIPT**: actor `act` found table `why`
full, in the era whose file system is `γfs`.  Persistent, so a post can
hand it out and keep it. -/
def fsFullRcpt {GF : BundledGFunctors} (_γfs : FsNames) (_act : BitVec 64) (_why : FsFull) :
    IProp GF :=
  iprop(True)

instance fsFullRcpt_persistent {GF : BundledGFunctors} (γfs : FsNames) (act : BitVec 64)
    (why : FsFull) : Persistent (fsFullRcpt (GF := GF) γfs act why) := by
  unfold fsFullRcpt; infer_instance

instance fsFullRcpt_timeless {GF : BundledGFunctors} (γfs : FsNames) (act : BitVec 64)
    (why : FsFull) : Timeless (fsFullRcpt (GF := GF) γfs act why) := by
  unfold fsFullRcpt; infer_instance

/-- FS-0's sites make the receipt from nothing (FS-1 replaces this by the
ledger append at each site). -/
theorem fsFullRcpt_intro {GF : BundledGFunctors} (γfs : FsNames) (act : BitVec 64) (why : FsFull) :
    ⊢@{IProp GF} fsFullRcpt γfs act why := by
  unfold fsFullRcpt; exact BI.true_intro

end Xv6
