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

`iris/ForkretParkClose.v` reduces the package to a short list.
`forkret_park_pkg_intro` proves it from:

* `kernel_text`, `wire_inv`, `kmap_at tramp_vpn tramp_ppn KP_rx` -- persistent.
* `pslot_used_at (un_pj N)` -- persistent, and ALREADY in allocproc's
  postcondition (`SpecAllocproc.v:192`).
* `ut_caps N` -- persistent (proved instance), and it already carries both
  `procs_inv` and the `is_kstack` the park takes as an argument.  So `procs_inv`
  is not a separate premise.
* the syscall environment `Rsys` -- persistent.
* `stack_own (KTR := KT1) (un_ks N + 4096) av` -- see below.
* `park_own N` -- the TWO exclusive resources, below.

`forkret_park_closer_intro` is the interesting half: the "residue closer" was
always described as the hard part, a wand that builds the trap loop's whole
kernel-side bundle for a fresh process.  It is not hard.  `forkret_yield` hands
it `ut_trap_parked` and `proc_priv_nopt`, the closer's own arguments hand it
`fd_slots FDSPARE` and `iref_slots IREFSPARE`, `ut_caps` and the syscall
environment are persistent -- and what is left is two resources.

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

### 2. `park_own` -- two exclusive resources

**`initproc ↦₈{un_dqi N} (un_ip N)` -- DONE on the producer side (2026-08-21).**
Only userinit writes the cell.  Every consumer downstream (`SpecKexit.v:256`,
`SpecReparent.v:93`, `SpecSyscall.v:190`) already takes it at an ARBITRARY
`dfrac` and hands it back, and `un_dqi` is a field the record's builder picks
-- so discarding costs no caller anything.  `ProofUserinit.v` now runs
`word_pointsto_persist` immediately after the `sd a0,1796(a5)` at `+0x14`, and
`SpecUserinit.v`'s continuation returns `∃ v, initproc ↦₈□ v`.  `ProofMain.v`
and `LinkUserinit.v` needed no change at all.

PERSIST EARLY, NOT ON THE WAY OUT.  The first attempt discarded at the end of
the proof, which satisfies "return it persistently" but is useless where it is
wanted: userinit's OWN `forkret_park` call is at line 649 and the store is at
462, so persisting right after the store puts the fact in scope at the deposit
site for free.  An exclusive cell could not be shared with the parked process
at all.

STILL OWED FOR KFORK.  `SpecKfork.v` and `SpecSysFork.v` mention `initproc`
nowhere, and `ProofKforkB5.v:204` has only `#Htext`, `#Hpinv`, `#Hwl` in scope.
It has to be threaded from `SpecSyscall.v:190` through sys_fork to kfork --
premises, not resources, since the discarded cell duplicates freely.
WORTH CONSIDERING INSTEAD: now that it is persistent, move it INTO
`syscall_env` (also persistent).  That DELETES the `dqi`/`ip` parameters from
syscall's, kexit's and reparent's contracts rather than ADDING one to kfork's.

**`bslots (un_bn N) 3` -- needs a lock, not a ghost update.**  The pool has
room (`BSLOTS = 1024`, `3 * NPROC = 192`), but the authority
`BioInv.bslots_auth` lives inside `bcache_res`, i.e. behind the bcache lock.
Minting three fragments is therefore a WP step in whoever allocates the child,
not something a bystander can do from persistent facts.

**The block bitmap is GONE from the package -- the design question is
SETTLED.**  `fileclose_bm` used to be the third resource, and exclusive: as
long as it sat in `UsertrapRes.ut_own_nopt` every process holding a residue
across user execution held the block bitmap, serializing user mode across
all harts.  The bitmap now lives in the persistent `BitmapInv.bitmap_inv`
(a `fs_ready` conjunct; design/fs-bitmap.md), the residue no longer names
it, and `fclose_names` lost the fields that carried it.

## The two call sites

`forkret_park` is invoked in exactly two places, both
`iMod (FP.forkret_park γs γf (proc_addr j) ks rest pid V Hrest with
"Hks Hctx Hpriv Hfd Hirsp")`:

* `ProofUserinit.v:649` -- the first process, at boot.
* `ProofKforkB5.v:204` -- every process after that.

Both proofs are functors over `FORKRET_PARK`, and `LinkForkretPark.v` is the
single place the `Axiom` is supplied.  So widening `forkret_park_body` to carry
`forkret_park_pkg` means paying at exactly those two `iMod`s and nowhere else.

userinit's site is ALREADY the documented staging point -- its comment block
reads "STAGE (f)'S DEPOSIT SITE -- D1, THE HUMANS' SEAM", and three rows
(`Hfirst`, `Hpersist`, `Hfsinit`) are dropped there awaiting the same widening.
Anything new we deliver joins a queue that already exists.

One caveat for kfork's site: `ut_caps` is persistent but UNPACKED there.  Its
members arrive as separate premises (`#Htext`, `#Hpinv`, `#Hwl`, ...), so
reassembling the bundle is mechanical but not free.

## Relationship to `syscall_env`

They are the same work.  `ProofSyscall.syscall_env` has no producer either, and
it is owed by exactly this closer.  The good news is that it is entirely
persistent, so it is on the free list above rather than the owed one.
