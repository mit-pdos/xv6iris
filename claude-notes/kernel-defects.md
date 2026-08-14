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

* the bound is now a FACT OF THE CODE, so no premise has to thread it and no
  region invariant has to carry it -- which is what the "no name for dp"
  objection made impossible (`projects/fs-sysfile.md`, D₀-b's stop).  The
  planned L4 carrier (directory `nlink <= 1 + allocated count`) is retired.
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
