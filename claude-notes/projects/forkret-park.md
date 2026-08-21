# forkret_park: retiring the last assumed Link

`LinkForkretPark.ForkretPark.forkret_park` is the one assumed-Link in the boot
cone, and the one assumption every proven process-side function carries
(`forkret`, `kfork`, `main`, `sys_fork`, `syscall`, `userinit`, `usertrap` --
see any `proof_coverage.py` run).  This file is the worklist for retiring it.

## The WP is already proved -- this is a resource problem, not a proof problem

`ProofForkretPark.v` proves the park (0 admits, 6 `Qed`) at one extra
precondition, `SpecForkretParkPaid.forkret_park_pkg`, and
`LinkForkretParkPaid.v` instantiates it against forkret's real contract.  What
has never existed is a CALLER that can pay that precondition.  So nothing here
is about discharging a weakest precondition; it is entirely about producing
resources for a process that has not run yet.

## What `forkret_park_pkg` costs, after `ForkretParkClose.v`

`iris/ForkretParkClose.v` (added 2026-08-21) reduces the package to a short
list.  `forkret_park_pkg_intro` proves it from:

* `kernel_text`, `wire_inv`, `kmap_at tramp_vpn tramp_ppn KP_rx` -- persistent.
* `pslot_used_at (un_pj N)` -- persistent, and ALREADY in allocproc's
  postcondition (`SpecAllocproc.v:192`).
* `ut_caps N` -- persistent (proved instance), and it already carries both
  `procs_inv` and the `is_kstack` the park takes as an argument.  So `procs_inv`
  is not a separate premise.
* the syscall environment `Rsys` -- persistent.
* `stack_own (KTR := KT1) (un_ks N + 4096) av` -- see below.
* `park_own N` -- the three exclusive resources, below.

`forkret_park_closer_intro` is the interesting half: the "residue closer" was
always described as the hard part, a wand that builds the trap loop's whole
kernel-side bundle for a fresh process.  It is not hard.  `forkret_yield` hands
it `ut_trap_parked` and `proc_priv_nopt`, the closer's own arguments hand it
`fd_slots FDSPARE` and `iref_slots IREFSPARE`, `ut_caps` and the syscall
environment are persistent -- and what is left is three resources.

## What is actually left

### 1. `stack_own (un_ks N + 4096) av` -- THREADING, not minting

`SpecForkretParkPaid.v`'s header calls this "a real hole in the chain".  It is
better than that: `SpecProcinit.v:260` ALREADY produces
`stack_own (kstack_va i + 4096) KSTACK_AV` for every slot.  The words exist
from boot.  What is missing is a home for the NPROC regions between procinit
and allocproc, plus an allocproc postcondition that hands one out beside the
`is_kstack` it already gives.  This is a contract change to allocproc and it
ripples through its cone, so it is a project rather than an edit -- but it is
plumbing, with no open question in it.

### 2. `park_own` -- three exclusive resources, in increasing difficulty

**`initproc ↦₈{un_dqi N} (un_ip N)` -- cheapest.**  Only userinit writes the
cell.  Every consumer downstream (`SpecKexit.v:256`, `SpecReparent.v:93`,
`SpecSyscall.v:190`) already takes it at an ARBITRARY `dfrac` and hands it
back, and `un_dqi` is a field the record's builder picks.  So persisting it
once after userinit (`DfracDiscarded`) makes every later copy free, and needs
NO downstream contract change -- only a producer-side change in userinit's
postcondition and in main's threading, since main currently carries the
exclusive BSS cell (`ProofMain.v`'s `Hinitproc`).  Do this one first.

**`bslots (un_bn N) 3` -- needs a lock, not a ghost update.**  The pool has
room (`BSLOTS = 1024`, `3 * NPROC = 192`), but the authority
`BioInv.bslots_auth` lives inside `bcache_res`, i.e. behind the bcache lock.
Minting three fragments is therefore a WP step in whoever allocates the child,
not something a bystander can do from persistent facts.

**`fileclose_bm (un_fn N) (un_us N)` -- THE DESIGN QUESTION.**  It unfolds
through `SpecFileclose.fileclose_bm` and `bitmap_res` to `fsblock` and
`free_pool`: exclusive, one per file system.  There is no second copy to give a
child.  So as long as it sits in `UsertrapRes.ut_own_nopt`, every process
holding a residue across user execution holds the block bitmap -- which
serializes user mode across all harts.  Either that is accepted, or the bitmap
moves behind the log's lock and leaves the residue.  This is an FS-cone
decision and it should be settled before the plumbing above is built on top of
it.

## Relationship to `syscall_env`

They are the same work.  `ProofSyscall.syscall_env` has no producer either, and
it is owed by exactly this closer.  The good news is that it is entirely
persistent, so it is on the free list above rather than the owed one.
