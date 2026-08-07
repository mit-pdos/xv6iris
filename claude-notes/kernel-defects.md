# Defects in the xv6 source found by the verification

A register of bugs in the kernel *being verified* — as opposed to gaps in
the proofs. Each entry records the mechanism, how it is reached, what is
observable, why the proof effort surfaced it, and what a fix would cost
here.

These are distinct from `claude-notes/projects/*.md` blockers, which are
about proof engineering. An entry here means **the C code is wrong**, and
the proof's inability to close is the symptom, not the disease.

A note on fixing any of them: the kernel image is pinned by `XV6_REV` in
the top-level `Makefile`, and the tracked `kernel-rocq/*.v` dumps come from
that exact revision. Editing `xv6-riscv/` moves symbol addresses, and every
proof that names one breaks — the README says so explicitly, and
`make xv6-rev-check` exists to catch drift. So "just fix the C" is never
cheap in this tree, and none of these entries should be fixed casually.

---

## D1 — `writei` releases a modified buffer without logging it

**Found:** 2026-08-06, proving `writei` (`fs.c`).
**Status:** OPEN. `writei` is specified and partly proven but deliberately
not linked; see [`projects/fs-inode.md`](projects/fs-inode.md) for the
proof-side detail.

### The code

```c
    if (either_copyin(bp->data + (off % BSIZE), user_src, src, m) == -1) {
      brelse(bp);          /* <-- no log_write(bp) */
      break;
    }
    log_write(bp);
```

### The mechanism

`copyin` (`vm.c`) walks the user buffer **one page at a time**, `memmove`ing
each chunk into the destination, and returns −1 at the first page it cannot
resolve (after `vmfault` also declines):

```c
  while (len > 0) {
    va0 = PGROUNDDOWN(srcva);
    pa0 = walkaddr(pagetable, va0);
    if (pa0 == 0) { if ((pa0 = vmfault(pagetable, va0, 0)) == 0) return -1; }
    n = PGSIZE - (srcva - va0);  if (n > len) n = len;
    memmove(dst, (void *)(pa0 + (srcva - va0)), n);   /* already committed */
    len -= n; dst += n; srcva = va0 + PGSIZE;
  }
```

So a −1 return does **not** mean "nothing was copied". It means "a prefix
was copied, then I gave up". `writei` then hands that buffer to `brelse`
without ever calling `log_write`, so the modification is in no transaction.

### What is observable

The buffer returns to the buffer cache holding bytes that are in no
transaction and on no disk. Consequently:

- a later `bread` of that block — from any process — hits the cache and
  returns the modified bytes;
- `commit()` never writes them, because the block is not in `lh.block[]`;
- if the buffer is recycled, or the machine crashes, the block reverts.

The block's contents therefore depend on buffer-cache state rather than on
the file system's committed state. Two reads of the same file can disagree
across an eviction, with no intervening write.

### How it is reached

From user space, with a buffer that starts in mapped memory and runs off
the end of it:

```c
    char *p = sbrk(0);           /* first unmapped address */
    write(fd, p - 64, 4096);     /* 64 mapped bytes, then a hole */
```

`copyin` copies the 64 reachable bytes into the block buffer, fails on the
next page, and `writei` releases the dirtied buffer unlogged. Nothing
privileged is required.

### Scope

Only the **user-source** path. `writei` is also called with `user_src = 0`
from in-kernel callers (`dirlink` and the `create`/directory paths); on
that arm `either_copyin` provably returns 0, the failure branch is dead,
and no defect arises. So the directory layer is unaffected.

### Why the proof found it

`SpecBrelse` demands `bio_locked`, which is `bio_held … bs bs bsd d` — the
buffer's traveling bytes must **equal** the payload's logical content.
That equality is the park swap's whole obligation, and it is what lets
`bread` promise that a cached block's bytes are the block's logical
content. Re-indexing the payload is `FsBlocks.fsblock_update`, which needs
`ghost_map_auth (fs_L γ)` — the log lock's authority, reachable only
through `log_write`.

`SpecEitherCopyin`'s user arm already models the truth honestly: it returns
`⌜r = 0 ∨ r = -1⌝` with the destination as `∃ dst_new` on **both**
outcomes. So at the `brelse`, the proof holds a buffer of unknown bytes
against a payload at the old content, and there is no step available that
reconciles them. The arm is not hard; it is false.

### What a fix would be

Add the missing `log_write(bp)` before the `brelse` on the failure path, so
the partial modification is committed rather than stranded. Note this makes
the file contain bytes that the return value does not count (`tot` is not
advanced on the break), which is odd but *consistent* — no cache/disk
divergence. The alternative — snapshotting and restoring `bp->data` — costs
a copy on every write.

### Why it is not fixed here

Editing `fs.c` moves every symbol address in the image (see the note at the
top of this file), and this machine has no riscv toolchain to rebuild the
ELF in any case. Modelling the anomaly instead was considered and rejected:
it would mean letting the escrow park bytes decoupled from the logical
content, which destroys `bread`'s postcondition — the promise every
FS-layer proof above it consumes — in order to describe a bug.

---

## Near-misses and non-defects

Recorded so the same ground is not re-covered.

- **`bmap`'s `panic("bmap: out of range")`** is unreachable for any caller
  respecting `bn < MAXFILE`, and `writei` establishes that bound before
  looping. Dead code, not a defect.
- **`writei`'s `off + n < off` overflow test** is likewise dead given
  `off, n < 2^31`, which the callers' `uint` arguments guarantee.
- **`initlog`'s "too big logheader" panic** is compile-time dead and absent
  from the image entirely (recorded in `projects/fs-log.md`).
