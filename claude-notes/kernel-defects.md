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
`make xv6-rev-check` exists to catch drift. **The procedure for doing it
anyway — and the gate that must pass first — is
[`../durable-notes.md`](durable-notes.md) §"Changing the kernel SOURCE";
read it before touching `xv6-riscv/`.** So "just fix the C" is never
cheap in this tree, and none of these entries should be fixed casually.

---

## D1 — `writei` releases a modified buffer without logging it

**Found:** 2026-08-06, proving `writei` (`fs.c`).
**Status:** **FIXED IN THE SOURCE, 2026-08-06** — `log_write(bp)` added
before the `brelse` on the failure path (upstream `fb0fed8 "fix writei
bug"`, cherry-picked onto the pinned rev as `7efd08f`; `XV6_REV` bumped and
the image re-dumped). See "How it was fixed, and what that cost" below, and
[`projects/fs-inode.md`](projects/fs-inode.md) for the proof-side detail.

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

### How it was fixed, and what that cost

The C now logs the partially-modified buffer before releasing it. The
alternative that was considered and REJECTED was modelling the anomaly
instead: letting the escrow park bytes decoupled from the logical content
would have destroyed `bread`'s postcondition — the promise every FS-layer
proof above it consumes — in order to describe a bug.

The full migration recipe is
[`../durable-notes.md`](durable-notes.md) §"Changing the kernel SOURCE".
In summary, the 6-byte change moved 46 symbols by +6 over
`[0x80003752, 0x80005420)` and cost ~30 proof files / ~130 edit sites,
almost all of them PC-relative immediates that no address grep can find.
The step that made it safe was proving the toolchain reproduced the pinned
image byte-for-byte BEFORE applying the fix.

### What the fix changes in the SPEC

Worth knowing before reading writei's contract: the partial bytes are now
COMMITTED rather than stranded in the cache. So writei genuinely modifies
the file beyond the range it reports having written, and the postcondition
cannot claim "everything outside `[off, off+tot)` is unchanged". It admits
a bounded disturbed region instead — at most one block past `off+tot`, with
unspecified contents, and `dist = 0` on every arm where no copy failed.

That is not a wart. The old code had the same anomaly, but *invisibly*, in
the buffer cache where no specification could see it; the fix moves it into
the logged state where it can be stated and reasoned about.

---

## D2 — `namei("..")` from a deleted directory: `sys_unlink` orphans the `".."` record

**Found:** 2026-08-12, designing the icache's link ledger
(`design/fs-icache.md` §20.8), while proving that "an inum a live directory
record names is an ALLOCATED inum" — the invariant `create` needs.
**Status:** OPEN. Not fixed; the model records it instead (see below).

### The code

`sys_unlink`'s directory arm (`sysfile.c`):

```c
  if(ip->type == T_DIR){
    dp->nlink--;
    iupdate(dp);
  }
  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);
```

`dp->nlink--` accounts for the `".."` record inside the child `ip`. But
the child is NOT truncated here: `iput` frees an inode only when its last
in-memory reference goes, so as long as anybody holds `ip` — a process
whose cwd it is, most obviously — the child's data blocks, and its `".."`
record, stay exactly as they were.

### The mechanism

Four stock system calls, no race required:

1. `mkdir /a`, `mkdir /a/b` — `b`'s data holds `"." -> b` and `".." -> a`;
2. a process `chdir /a/b`, so `b` has a live icache reference;
3. `rmdir /a/b` — `isdirempty(b)` passes, `a`'s record for `b` is zeroed,
   `a->nlink--`, `b->nlink--` reaches 0. **`b`'s `".."` record still names
   `a`, and `a`'s `nlink` no longer accounts for it.** `b` is not freed:
   the cwd holds a reference;
4. `rmdir /a` — `a` is empty now, `a->nlink--` reaches 0, nobody holds a
   reference, so `iput` frees it: `itrunc`, `type = 0`. `a`'s inum is on
   the free list.

### What is observable

From the deleted cwd, `namei("..")` -> `dirlookup(b, "..")` returns `a`'s
inum -> `iget` -> `ilock`, which breads a record whose `type` is 0 and
takes **`panic("ilock: no type")`** — a kernel panic reachable from
unprivileged user code.

And the quieter outcome is worse: if any `ialloc` re-claimed that inum in
between, `ilock` succeeds and the process's `".."` silently resolves to an
**unrelated inode** — a directory traversal into a file it was never
granted, with no error anywhere.

### Why the proof surfaced it

`design/fs-icache.md` §19.6 chartered the invariant as "`dir_ok`
strengthened from *covers* to *allocated*": every live directory record
names an inum whose region record has a nonzero type. That statement is
FALSE of xv6, at exactly this one record, and the counterexample above is
its refutation. The invariant is what `create` needs in order to prove that
a just-claimed inum has no foreign referrer, so the defect is not
incidental to the proof — it sits directly on the path.

### What the model does instead

The link ledger (§20.2) carries TWO colours per named inum: `ilink z`, a
record whose target's `nlink` pays for it, and `igrey z`, a record that
**nothing** pays for. At `dp->nlink--` the child's `".."` fragment is
CONVERTED, `ilink -> igrey`, so the ledger's (L1) cap falls on both sides
at once. A grey fragment carries no allocatedness — which is honest,
because in the trace above the target genuinely is not allocated — and
**every `igrey` fragment in a run is a witness to a reachable instance of
this defect.**

Both total repairs are dead for machine-reachability reasons, and it is
worth recording why (§20.9 (h)/(i)): keeping the ledger total would leave
`w >= 1` at the orphan's parent and BLOCK `iput`'s free of it, and scoping
the payload's fragments by the directory's own `nlink` would leave a
deleted cwd carrying none, so `dirlookup` from it — a reachable step —
would be stuck. A resource may not forbid a machine-reachable step; it only
wedges the proof.

### What a fix would cost

In the C, the honest fix is to make the child's `".."` stop naming the
parent at the moment the parent's `nlink` stops paying for it — either by
zeroing the `".."` record in `sys_unlink`'s directory arm (one `writei` of
16 zero bytes, before `dp->nlink--`), or by refusing `..` lookups in a
directory whose `nlink` is zero (a test in `dirlookup`, which then has to
be told the directory's record). Both are small.

In the PROOF, either fix retires the grey colour outright: `dir_links`
becomes single-coloured, and `create`'s one remaining gated case — *no
orphaned directory names the claimed inum* (§20.7's (b)) — becomes a
theorem. Until then that case is **unproven but not false**: it holds on
every trace that does not fire this defect.

Any C change here is subject to `durable-notes.md` §"Changing the kernel
SOURCE" — the pinned image, the reproducibility gate and the address
sweep — so it is not cheap even at 16 bytes.

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
