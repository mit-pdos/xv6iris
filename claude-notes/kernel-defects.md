# Defects in the xv6 source found by the verification

A register of bugs in the kernel *being verified*, as opposed to gaps in the
proofs: an entry here means **the C code is wrong** and the stuck proof is the
symptom. **The register holds ONE CANDIDATE under review** — every earlier
defect this effort found has been fixed upstream, and a fix's consequences for
a contract are recorded with that contract, not here.

## CANDIDATE C1 — create's transaction can exceed its MAXOPBLOCKS reservation
## through nameiparent's frees (found 2026-08-13, staging the create walk)

Within create's single begin_op..end_op window, nameiparent's per-level
`iunlockput(parent)` can be the FREEING iput: concurrently unlink the child
then the (now empty) ancestor between namex's nlink guard and its iput, and
the free runs inside create's op — itrunc's bfrees absorb into the one
bitmap block, but each freed ancestor's iupdate logs a DISTINCT inode
block.  create's own mkdir chain already closes at zero slack
(CreateBudget.cr_budget_mkdir), so ANY such spend puts the op over
MAXOPBLOCKS.  begin_op's admission test (log.c:138) is sound only if every
op stays within MAXOPBLOCKS; under combined pressure the total can reach
LOGBLOCKS and `log_write`'s check — `unreachable("too big a transaction")`,
log.c:230 at pin 2691300 — fires, i.e. the unreachable() is reachable.
Proof-side consequence in projects/fs-sysfile.md ("BLOCKER A"): create is
unprovable under the landed honest contracts at every path length.
Pending human ruling; candidate fixes are upstream-shaped (bound or defer
namex's frees relative to the caller's op, or price walks into the
reservation), not spec-shaped.

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
