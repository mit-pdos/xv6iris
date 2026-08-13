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

## HOW TO TELL A KERNEL DEFECT FROM A SPEC PROBLEM

Read this before deciding a divergence is "just" something to model. It was
learned expensively on `kexec`.

**The tell is scaffolding.** `copyout` is total — no panics, any `dst`, any
length — yet its contract could not be applied by exec at all, because
`vmfault` underneath checked `ismapped` on the table it was HANDED while
calling `mappages` on `myproc()->pagetable`. That divergence was noticed, and
was explicitly ruled *not* a defect here on the grounds that it is unreachable
from exec (exec's pages are already mapped). What followed was an indexed,
two-armed `co_license` apparatus with its own module type, plus a
strengthening of `SpecWalkaddr`, plus a *predicted* strengthening of
`SpecUvmalloc` — all of it, in the end, machinery for describing one line of
wrong C. Upstream then fixed the source (`vmfault` takes the size and maps
into the table it was given), and the entire apparatus was deleted, leaving a
simpler contract than before AND a cheaper obligation on exec than the
workaround had.

So:

- **When a contract needs an elaborate case split to describe a function that
  is total and has no panics, suspect the code**, not the specification. A
  total function should have a contract shaped like one.
- **When the case split exists only to say "and in this case the callee does
  something no caller wants", that is a bug report, not a design.**
- **Unreachability makes a defect safe, not correct.** "No current caller can
  reach it" is a reason not to *panic* about it; it is not a reason to build
  around it. Price the source fix first — it is often smaller than the
  scaffolding, and it makes every downstream obligation cheaper rather than
  more expensive.
- The image is pinned by `XV6_REV`, so a source fix is not free (see the note
  at the top of this file, and the "Changing the kernel SOURCE" section of
  `durable-notes.md`). Price it; do not assume it is out of reach. Two xv6
  revision bumps landed during the kexec work and the proofs came through
  both, because `Code<F>.v` addresses are symbol-relative by design.


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

## D2 — `uart.c`'s `tx_lock` sleeplock is never initialized

**Found:** 2026-08-12, updating to upstream `ae96fd0` ("example of sleep
waiting for interrupt wakeup"), which rewrote the UART transmit path.
**Status:** OPEN, and it BLOCKS the boot wiring of the whole uartwrite cone.

### The code

`ae96fd0` replaced the transmit spinlock with a sleeplock, because the new
`uartwrite` has to hold it across a `sleep()`:

```c
 // for sending threads to serialize their writes
 static struct sleeplock tx_lock;
 static int tx_chan;

 uartinit(void) {
   ...
   WriteReg(IER, IER_TX_ENABLE | IER_RX_ENABLE);
-  initlock(&tx_lock, "uart");        /* deleted */
 }
```

Nothing calls `initsleeplock(&tx_lock, ...)`, in `uartinit` or anywhere
else. The old `initlock` call was deleted and no replacement was added.

### The mechanism

`tx_lock` is a file-static, so the loader zeroes it, and every field
`initsleeplock` would set is already the value it would set — `locked = 0`,
`pid = 0`, and the inner spinlock's `locked = 0` / `cpu = 0`. So the lock
*functions*: `acquiresleep` and `releasesleep` behave correctly.

What is NOT set is the two NAME fields. `initsleeplock` writes
`lk->name = name` and `initlock(&lk->lk, "sleep lock")`; here both stay
NULL. They are read only by the panic paths (`acquire`'s and `release`'s
`panic("acquire")`/`panic("release")` do not print the name, but `procdump`
and any diagnostic that walks a lock would), so the observable consequence
is a NULL dereference in a path that only runs after another bug has
already fired. **Benign in practice, and still wrong**: it is the only lock
in the kernel that reaches `acquire` uninitialized.

### Why the verification cares, and it cares a lot

The proof of a lock's name is not decoration here. `WpLock.lock_name lk s`
is `∃ p, lk->name ↦₈□ p ∗ p ↦ₛ□ s` — "the field points at the string" —
and it is a conjunct of `is_lock`; `SleepLock.sl_name` is the same for the
sleeplock's own field, and `is_sleeplock` requires both (its inner
spinlock's name is the literal `"sleep lock"`). With the fields at zero
the obligation is `(0 : mword 64) ↦ₛ□ s`, and address 0 is not in the
model's memory map. **`is_sleeplock` for `tx_lock` is therefore not merely
unproven, it is unprovable**, so `UartTxInv.is_txlock` is a premise no
caller can discharge — the same shape as `SpecIlock`'s `i_ref`
(`design/fs-icache.md`). The cone above it is stated and proved against
`is_txlock` regardless; closing this closes the cone.

### The two ways out

1. **Fix the C**: add `initsleeplock(&tx_lock, "uart")` to `uartinit`. One
   line, and it is what every other lock in the kernel does. Cost here is
   the standard image-shift bill (`durable-notes.md` §"Changing the kernel
   SOURCE") — and note this defect was found *during* a bump, so the bill
   would be paid on top of one already in progress.
2. **Make a lock's name optional**: index `is_lock` / `is_sleeplock` by
   `option string`, with `None` meaning "the name field is unconstrained",
   and add a `newlock`-from-zeroed-bytes lemma so an anonymous lock can be
   minted at boot. That is honest about what the C actually guarantees and
   needs no source change, but it is a wide mechanical sweep (~123 sites
   write a lock-name literal) and it weakens a fact every other lock in the
   tree really does enjoy.

(1) is the better engineering; (2) is the better model of *this* source.
Neither is cheap, and the choice is the maintainer's.

### Where it is assumed meanwhile

`iris/LinkTxLockInit.v`, one `Axiom` (`tx_lock_init`) handing back
`UartTxInv.is_txlock` for the transmitter token and the frozen DLAB fact —
exactly what the missing `initsleeplock` plus the usual newlock step would
give. It is deliberately a **different file** from `LinkUartwrite.v`, which
assumes uartwrite's contract for the unrelated reason that its proof is not
written: proving uartwrite does not fix D2 and fixing D2 does not prove
uartwrite, so keeping them apart is what stops either from hiding the other
in `Print Assumptions`.

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
