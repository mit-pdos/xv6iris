# Defects in the xv6 source found by the verification

A register of bugs in the kernel *being verified*, as opposed to gaps in the
proofs: an entry here means **the C code is wrong** and the stuck proof is the
symptom. **The register is currently empty** — every defect this effort found
has been fixed upstream, and a fix's consequences for a contract are recorded
with that contract, not here.

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
