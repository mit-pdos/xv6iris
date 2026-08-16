# Defects in the xv6 source found by the verification

A register of bugs in the kernel *being verified*, as opposed to gaps in the
proofs: an entry here means **the C code is wrong** and the stuck proof is the
symptom.  A fix's consequences for a contract are recorded with that contract,
not here.

## UNREACHABLE, BY THE CALLER'S GUARANTEE — `exec`'s `ustack[argc] = 0` would
## write one element past `ustack[MAXARG]`, but no caller can reach it

**Kept as a live entry even though nothing can trigger it**, because the
argument for safety lives entirely OUTSIDE `exec`: `sys_exec` guarantees a null
pointer within the first `MAXARG` elements of `argv`, so `argc < MAXARG` at the
loop's exit and the store is in bounds. `exec` itself does not establish that
and cannot — see below. Unreachability makes a defect safe, not correct (this
file's own rule), and a second caller, or a `sys_exec` that stopped scanning at
`MAXARG`, would make it live.

`kexec` declares `uint64 ustack[MAXARG]` (32 entries) and tests the bound
INSIDE the argument loop:

```c
for (argc = 0; argv[argc]; argc++) {
  if (argc >= MAXARG) goto bad;
  ...
  ustack[argc] = sp;
}
ustack[argc] = 0;                 /* argc can be 32 here */
```

The test only runs once `argv[argc]` is known non-null, so with **exactly 32
arguments** the loop's null-terminated exit is taken at `argc == 32` and the
store after it addresses `ustack[32]` — out of bounds by one element.  (33
arguments does hit `bad`, and 31 or fewer never gets near it; it is the exact
boundary that escapes.)

**Not exploitable as compiled**, which is why it has stayed invisible: gcc
reserved **33** slots for the array (264 B at `s0-368 .. s0-112`, read off the
frame map in `SpecKexec.v`'s header), so the extra store lands in the padding
inside kexec's own frame and clobbers nothing.  That is an accident of this
build, not a property of the source.

**How it surfaced, and where the guarantee now lives.**  The argv loop's exit
state `ProofKexecSeam.kxc_at_272` must publish a bound on `argc`, and the only
one derivable from the function's OWN tests is `argc <= MAXARG` — the loop head
`kxc_at_21a` has `c < 32`, and the null-terminated exit adds one to it without
re-testing.  Rather than carry that as slack, `SpecKexec` takes `na < MAXARG` as
a PREMISE and the exit state says `c < 32` outright; the argv loop threads the
premise for that one use.  So the contract now records exactly what `sys_exec`
promises, and a caller that cannot promise it is refused at the contract instead
of silently reaching the store.

The one-line source fix is to move the test above the loop's condition (or size
the array `MAXARG + 1`), which would let the premise go.

## UNREACHABLE, BY THE CALLER'S POSITION — `userinit` does not check
## `allocproc`'s result, and stores through the returned pointer

`userinit` is the only caller of `allocproc` that does not test for 0:

```c
p = allocproc();          /* returns 0 when every slot is in use */
initproc = p;
p->cwd = namei("/");      /* userinit+0x24: sd a0,336(s1) -- s1 = 0 */
```

With a full table the store addresses 336. `kfork`, the other caller,
tests and returns -1.

**Unreachable because of WHERE userinit runs, not because of anything it
checks**: `main` calls it once, on hart 0, before `scheduler()` starts, so
no process has ever been allocated and every one of the `NPROC` slots is
UNUSED. Unreachability makes a defect safe, not correct (this file's rule),
and a second caller — or a `userinit` moved after the first process exists —
would make it live.

**What it cost the proof, and why the answer was not a premise.** The store
has no points-to on the null path, so the WP is STUCK, not merely ugly: the
arm has to be refuted. Nothing in the proc table could express "some slot
is UNUSED" — `ProcGeom.pstate_lock` holds BOTH halves of the state mirror
exactly when `unclaimed st = true`, and `unclaimed UNUSED = true`, so no
fragment pinning a slot at UNUSED can live outside that slot's lock. The
answer is `ProcAvail.v`'s counted regime (design/proc-struct.md, "The proc
table's two regimes"): a caller holding `procs_avail (Some (S k))` refutes
the arm from `allocproc_post`'s own `⌜avail_zero op⌝`.

The one-line source fix is `if (p == 0) panic("userinit");`, which would let
the counted regime go — at the price of the relayout every source change
costs (xv6-bump-playbook.md), and of diverging from the pinned `XV6_REV`.

## FIXED UPSTREAM (`117c0e7`) — an unchecked `nlink++` could wrap a link
## count to zero, in `create`'s mkdir arm and in `sys_link`

`nlink` is a `short` on disk, so at its maximum the `sh` stored 0 and the
record became indistinguishable from a FREE inode while live directory
entries still named it -- silent on-disk corruption, no panic, no error
return.  The proof side found it because the link ledger (InodeRegion (L1)
`w <= nlink`, (L3) `type = 0 -> nlink = 0`) makes the wrapping store
*unprovable* rather than merely unsupported: `SpecIupdate.wp_iupdate_link`
wants `bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn0) + 1`, which at
the wrap reads `0 = 65536`.  The ledger refusing a corrupting store is the
ledger working.

The fix is `NLINK_MAX 32767` in `fs.h` and one test at each of the two
raising sites, each branching to the `fail:`/`return 0` path that already
unwinds exactly that state.  **Three things it settles for the proofs**, and
they are why the whole route was worth taking rather than carrying a gate:

* the bound is now a FACT OF THE CODE, so no premise has to thread it up to
  `wp_create_sconf_body` -- which is what the "no name for dp" objection made
  impossible (`projects/fs-sysfile.md`, D₀-b's stop).  The declined C5
  carrier (directory `nlink <= 1 + allocated count`, a COUNTING argument) is
  retired.
  **AMENDED (2026-08-14, the twelfth stop): "and no region invariant has to
  carry it" was WRONG, and the walk found it.**  The guard is a SIGNED test
  -- `short nlink`, `>= NLINK_MAX` compiled to `== 32767` -- while the
  ledger's premise is UNSIGNED, and the two differ at `bv_unsigned = 65535`,
  i.e. signed `-1`: it passes both of create's guards (`<> 0` at +0x2e,
  `<> 32767` at +0x36) and still wraps.  Nothing in the tree bounds
  `di_nlink` above (`ireg_link_ok` is a LOWER bound; `dinode_wf`,
  `inode_ok`, `ic_loaded` say nothing; the boot image obligation is (L3)
  again), so a RANGE invariant (L4) `bv_unsigned (di_nlink d) <= 32767` is
  still owed.  What the fix genuinely buys is that (L4) is now
  **preservable** -- §20.18's option 3 was right that it is "option 2 with
  the proof obligation stated".  Witness and the closing statement:
  `ProofCreateParts.cr_nlink_guard_leaves_the_wrap` /
  `cr_nlink_guard_closes_under_L4`; the priced four-file resolution is in
  `projects/fs-sysfile.md`'s twelfth-stop entry.
* **the guard is still a real two-way branch**: it refuses at 32767 and does
  not rule the value out, so create's walk pays a case split (and its taken
  arm) whether or not any invariant is ever added.
* attainability was, and stays, a separate question: 32767 links to one
  directory needs 32765 subdirectories, one inode each, so ialloc's A-FAIL
  fires first on the shipped geometry.  Unreachable makes a defect safe, not
  correct -- and `sys_link` on a regular file has no such argument at all.

## REFUTED CANDIDATE (2026-08-13) — create + concurrent unlink cannot bust
## the log: CROSS-TRANSACTION ABSORPTION covers namex's freeing iput

Raised while staging the create walk (the ledger does not compose across
nameiparent under per-op accounting), refuted the same day by the team:
for namex's per-level iput to FREE, some unlink must have driven that
inode's nlink to zero INSIDE create's op window (a pre-window unlink
removes the dirent, so the walk never reaches the inode) — and a commit
runs only at outstanding = 0, so that unlink's own iupdate of the SAME
inode block is still in the shared log header; namex's iupdate absorbs
against it (log_write's absorption scan is over lh, i.e. GROUP-wide).
The itrunc side adds nothing: bfrees touch only the bitmap block, which
the op's own budget prices once — whoever pays first, the other absorbs.
So no op exceeds its MAXOPBLOCKS reservation, begin_op's admission
arithmetic stands, and log.c:230's unreachable() stays unreachable.

What survives is a MODELING obligation, not a defect: the proof's ledger
must be able to SAY this — the freeing-iput's iupdate is absorbed because
"cached inode with nlink = 0" implies its inode block is in the group's
logged set.  Recorded as the re-model direction in
projects/fs-sysfile.md ("BLOCKER A, resolved").

## RULED REAL (user, 2026-08-15: "it looks like a real bug") — `sys_link`
## can append a link to an ORPHANED directory, and the link is then leaked
##
## FIX PREPARED: xv6-riscv `verified` branch commit f60ff58 ("sys_link:
## refuse to link into an unlinked directory") — create's guard verbatim,
## after the ilock(dp), routed to `goto bad` so the ip->nlink++ is undone.
## Kernel builds clean.  AWAITING: user pushes upstream, then the pin
## bump (every sysfile function AFTER sys_link shifts — relayout sweep
## per the playbook), then sys_link's walk gains the guard arm and the
## STRONG isdirempty invariant becomes true of the binary (discharging
## §20.6's itrunc row and F1.5d's plank; the grey name-conjunct
## alternative is superseded).

`sys_link` does `nameiparent(new, name)` -> `ilock(dp)` ->
`dirlink(dp, name, ip->inum)` with **no `dp->nlink == 0` re-check**.
`create` has exactly that check (`sysfile.c:262`) and `namex` has it too
(`fs.c:693`), but namex's fires under the WALKER's lock and sys_link
re-locks `dp` afterwards, so the guard does not cross the window:

    proc A: link("/x", "f")   -- nameiparent returns dp, nlink != 0, unlocked
    proc B: rmdir(dp's path)  -- dp is empty, so the rmdir succeeds;
                                 dp->nlink -> 0, but proc A's reference
                                 keeps it off the free list
    proc A: ilock(dp); dirlink(dp, "f", ip->inum)   -- appends to an orphan

`ip->nlink` was already incremented.  When `dp`'s last reference goes,
`iput` sees `nlink == 0` and `itrunc`s it, DISCARDING the `"f"` record
without decrementing `ip->nlink` — so `ip` is never freed.  A userspace
loop leaks one inode per iteration.

The fix is create's guard, verbatim, after sys_link's `ilock(dp)`:
`if (dp->nlink == 0) { iunlockput(dp); goto bad; }`.

**Why it matters to the proofs even though it is a leak and not a crash.**
It is the one trace that refutes *"an orphaned directory has no live
record but `"."` and `".."`"* — fs-icache.md §20.6's itrunc-row
obligation, §20.17.5's residue closure, and F1.5d's gate (fs-fragments.md
R9).  In the model the discarded record's `ilink ip` is STRANDED by
`dir_links_size_zero`, which is precisely §20.6's "makes those unfreeable
— a blocker on a reachable step".  Recorded with the amendment it forces
in projects/fs-fragments-campaign.md, "F1.5b's FIRST-CONSUMER VERDICT".

Fixing the C is never free: the image is pinned by `XV6_REV` in the top-level
`Makefile` and the tracked `kernel-rocq/*.v` dumps come from that revision, so
every proof naming an address moves. The procedure and the gate that must pass
first are in [`durable-notes.md`](durable-notes.md) §"Changing the kernel
SOURCE".

## How to tell a kernel defect from a spec problem

**The tell is scaffolding.**

- **When a contract needs an elaborate case split to describe a function that is
  total and has no panics, suspect the code**, not the specification. A total
  function should have a contract shaped like one.
- **When the case split exists only to say "and in this case the callee does
  something no caller wants", that is a bug report, not a design.**
- **Unreachability makes a defect safe, not correct.** "No current caller can
  reach it" is a reason not to panic about it; it is not a reason to build
  around it. Price the source fix first — it is often smaller than the
  scaffolding, and it makes every downstream obligation cheaper rather than
  more expensive.
- **An obligation you cannot discharge because the resource is owned by NOBODY
  may be telling you the same thing.** freeproc's `p->parent = 0` was
  unprovable because xv6 writes that cell without `wait_lock`, which its own
  `proc.h` says is required. Ask "is this a bug?" BEFORE designing a bundle to
  hold the resource — **modelling a bug makes it permanent in the spec.**

## Provably dead code, so the same ground is not re-covered

- **`bmap`'s `panic("bmap: out of range")`** is unreachable for any caller
  respecting `bn < MAXFILE`, and `writei` establishes that bound before looping.
- **`writei`'s `off + n < off` overflow test** is likewise dead given
  `off, n < 2^31`, which the callers' `uint` arguments guarantee.
- **`initlog`'s "too big logheader" panic** is compile-time dead and absent from
  the image entirely.

## Benign-but-load-bearing (2026-08-16): the no-crash orphan, and why ireclaim is not just crash recovery

Not a defect — a design consequence worth having on the record (user-derived,
from iput's tail).  Between `releasesleep(&ip->lock)` (fs.c:357) and the
re-`acquire`/`ref--` (:359-362), the freeing thread F holds a counted
reference to an entry whose inode it has already freed on disk.  `iget`
adopts any entry with `ref > 0` at the same `(dev, inum)` (:258), so a
concurrent `ialloc`+`iget` for the recycled inum bumps ref 1→2 and the slot
now serves TWO incarnations at once — safe (all ref moves under
`itable.lock`; `valid = 0` forces the newcomer's `ilock` to reload its own
claim), but the incarnation boundary exists only in the trace, never in
machine state.  This is the model's BORN-BEFORE-THE-ENTRY wall and
§17.6.1's mid-free referrer, read directly off the C.

The corner: F is preemptible in that gap (no spinlock held).  If the new
incarnation lives a WHOLE LIFE meanwhile (create → unlink → last close),
its final `iput` sees `ref == 2` — F's ghost — and SKIPS the free (:343);
F then decrements to 0.  Result: `type != 0, nlink == 0`, zero refs, zero
dirents — a fully-formed on-disk orphan with NO crash anywhere.  Bounded
in THIS kernel because `ireclaim`'s scan (:381) matches exactly that shape
at next boot; stock xv6 (no ireclaim) leaks it until fsck.  Consequences:
(1) ireclaim is load-bearing for steady-state semantics, not only crash
recovery — do not model it as crash-only; (2) any future strong invariant
of the form "nlink == 0 ∧ ref == 0 ⇒ type == 0 on disk" is FALSE of the
running kernel between F's ref-- and the next boot; state orphan-set
membership instead.

### The fix (candidate), and what it does and does NOT buy (probe, 2026-08-16)

CANDIDATE FIX for the no-crash orphan above: restructure iput to release
the in-core reference BEFORE freeing the disk inode --

    acquire(&itable.lock);
    int last = (ip->ref == 1 && ip->valid && ip->nlink == 0);
    uint dev = ip->dev, inum = ip->inum;   // CAPTURE BEFORE ref-- (mandatory)
    ip->ref--;
    release(&itable.lock);
    if (last)
      ifree(dev, inum);                    // bread(IBLOCK(inum)); itrunc-from-disk; type=0; iupdate

Verified sound (report-only probe) with TWO mandatory conditions:
(1) dev,inum captured before ref-- -- once ref hits 0 the slot may be
    recycled by a concurrent iget for a DIFFERENT inum, so ifree must
    touch only those two scalars, never ip.  (The naive `ifree(ip->dev,
    inum)` reads ip too late -- a real bug in the sketch.)
(2) ifree's itrunc reads the ON-DISK addrs (fresh bread), not in-core.
    Sound because a quiescent nlink==0 sole-ref inode has no writei in
    flight, so iupdate already flushed current addrs -- but this is a
    SEMANTIC argument, not the syntactic identity in-core itrunc enjoys.
    Note the unlink-while-open (POSIX) case: writes continue after
    nlink==0, but the final iput is the sole holder with none in flight.
The [ref--, ifree] gap leaves type!=0,nlink==0,ref==0: unreachable by
any iget (type!=0 blocks ialloc, nlink==0 blocks dirlookup), so
preemption is harmless; a crash there is an ordinary crash-orphan that
ireclaim recovers.  Same begin_op/end_op, same MAXOPBLOCKS budget.

WHAT IT BUYS: fixes this leak; makes "allocatable(inum) => no in-core
iref" TRUE and preservable (today false of the running kernel); demarks
incarnation boundaries in machine state.  Kills the create_fresh_ty
residue's CASE 1 (the pre-existing / stale-reference leg, fs-icache
§17.6.1).

WHAT IT DOES NOT BUY: it does NOT retire create_fresh_ty.  The axiom's
load-bearing attacker is CASE 2 -- a FRESH iget of the claimed inum
inside ialloc's own brelse->iget window -- which lives inside ialloc,
not iput.  The claim slot c and refcount r are decoupled ledger
components (IcacheRef.v:290-296,731-734); an outstanding iclaim carries
r=0 by definition, so a free reasoning through r never meets a c.  The
reorder relocates the wall from Case 1 to Case 2; only K-F2 (currency
into ialloc's window) or weakening SpecCreate reach Case 2.  After
C'-lite + boot-shelter + this reorder, the SOLE surviving model-
admissible attacker on the claim box is the fresh iget at the SpanL /
currency-gap site = exactly K-F2's territory.  GO as a kernel fix;
NO-GO as an axiom retirement.  Proof cost if taken: ProofIput cone
re-walk (the free fires post-ref--, REF-1 derivations move before it),
a new type=0 => iref-empty coupling in InodeRegion/IcacheRef, SpecItrunc
re-spec to disk-addr form; SpecIalloc/SpecIget/SpecCreate DO NOT move
(which is exactly why the axiom is untouched).  Pin bump + re-dump
(post-sys_link addresses relayout).
