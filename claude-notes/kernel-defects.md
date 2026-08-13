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
**Status:** **FIXED IN THE SOURCE** by upstream `9da28f5` ("Fix kernel panic
and add test case"), which is cherry-picked onto the pinned `ae96fd0` in the
image this tree is proved against. The description below is the defect as
found; what the fix does and what it retires is
[§"What the fix does"](#what-the-fix-does-9da28f5) at the end of this entry.

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

### D2's THIRD outcome, found later and strictly worse than the other two (fs-sysfile S5h)

The two harms above are both suffered by the WALKER. There is a third, and
it is suffered by an innocent third party: **a stranger walking the dangling
`".."` can FREE an inode that a live `create` has already allocated.**

Take the trace above to step 5 and put a concurrent `create` in it. After
`rmdir /a` frees `a`'s inum, process Q runs `create("/f")`; `ialloc` finds
`a`'s inum free, `memset`s it, sets `dip->type = T_FILE`, `log_write`s,
`brelse`s — and is preempted **before its `iget`**. Now P walks `".."` from
its deleted cwd: `iget` mints a fresh entry (nothing references that inum:
`ialloc` has not `iget`ed yet), `ilock` breads a record whose `type` is
nonzero — no panic this time — and P's own `iput` then finds
`ref == 0 && valid && nlink == 0`, because `memset(dip,0,64)` left `nlink`
at zero. So iput takes the **free path**: `itrunc`, `ip->type = 0`,
`iupdate`. Q's inode is deallocated under it. Q resumes, `iget`s, `ilock`s,
and either panics on the type-0 record or — after a second racing `ialloc` —
proceeds to fill an inode a third process now owns. **The same inum is
handed to two callers, with no error anywhere.**

The window is `ialloc`'s `brelse`→`iget` gap, but P only has to FINISH
inside it; P can have started long before, so it is not a two-instruction
race in practice.

**A SECOND, SMALLER FIX KILLS THIS OUTCOME ON ITS OWN: hold the dinode
buffer across `ialloc`'s `iget`** — i.e. move the `brelse` after the
`return iget(dev, inum)`, or take the reference before releasing. Every
claim and every free is serialised by that block's buffer, so holding it
closes the window outright. It does not fix the walker's panic (that needs
D2's own fix) and it is even smaller than 16 bytes of `writei`.

**In the PROOF this is not a side note.** `design/fs-icache.md` §20.16
shows it is exactly why the model's claim token cannot be built: the
obligation `ireg_free_au` would have to discharge — *no claim is
outstanding at the inum I am freeing* — is FALSE on this trace, so no ghost
carrier of any shape can prove it, and §20's stage E is dead as chartered
until the kernel changes. This is the first defect in this file whose fix
the verification's own progress depends on.

### What the fix does (`9da28f5`)

Upstream took neither of the two repairs costed above. It fixes the defect
at the *walk* rather than at the record: a directory whose `nlink` has
reached zero is refused as a walk step, so the dangling `".."` is never
followed. Two guards, both immediately after the `ilock` that makes `nlink`
readable:

```c
  /* namex(), kernel/fs.c — after ilock(ip), after the type != T_DIR arm */
  if (ip->nlink == 0) { iunlockput(ip); return 0; }

  /* create(), kernel/sysfile.c — after ilock(dp), before the dirlookup */
  if (dp->nlink == 0) { iunlockput(dp); return 0; }
```

The first kills all three outcomes of the walker's trace at once: from a
deleted cwd the walk stops AT the cwd, so `dirlookup(b, "..")` never runs,
`a`'s inum is never `iget`ed, and neither the `panic("ilock: no type")`, nor
the silent resolution to a re-claimed inode, nor the third outcome above —
a stranger's `iput` freeing an inode a live `create` has already allocated —
can be reached. The second closes the companion hole `create` had directly:
a file created in a directory already unlinked would land in a disconnected
subtree.

**What it does NOT do is remove the dangling record.** `b`'s `".."` still
names `a` on disk, and `a`'s `nlink` still does not pay for it, so any
invariant stated over the *records* (rather than over what a walk can
reach) is still false at exactly that fragment. The bearing on the ledger is
therefore a live design question and not a mechanical deletion: the grey
colour models "a record nothing pays for", and such a record still exists —
what changed is that no reachable step consumes one. Whether `igrey`
retires, or narrows to an unreachable-by-construction case, is settled by
restating §20's (b) over reachability; see `design/fs-icache.md` §20 and the
GR-2 worklist. Do not assume the colour is simply gone.

## D3 — `uart.c`'s `tx_lock` sleeplock is never initialized

**Found:** 2026-08-12, updating to upstream `ae96fd0` ("example of sleep
waiting for interrupt wakeup"), which rewrote the UART transmit path.
**Status:** **FIXED IN THE SOURCE** by upstream `b7c25cf` ("initialize the
tx_lock sleeplock"), which is route (1) below verbatim -- one
`initsleeplock(&tx_lock, "uart")` at the end of `uartinit`.  It arrived in the
pinned image for free, as an intermediate commit on the way to the branch tip
`9da28f5`.  So the choice between the two routes below never had to be made,
and route (2) -- indexing `is_lock` by `option string`, a ~123-site sweep that
weakens a fact every other lock really does enjoy -- is retired unbuilt.

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

### Where it was assumed meanwhile

**This is now a retirement, not an assumption.** `uartinit` really does
initialize the lock, so `is_txlock` is provable where it was previously
unprovable, and `LinkTxLockInit.v`'s axiom should come out as soon as
`ProofUartinit` is replayed over the extra call -- see the GR-1c section of
`projects/fs-sysfile.md`.  What stood there meanwhile:

`iris/LinkTxLockInit.v`, one `Axiom` (`tx_lock_init`) handing back
`UartTxInv.is_txlock` for the transmitter token and the frozen DLAB fact —
exactly what the missing `initsleeplock` plus the usual newlock step would
give. It is deliberately a **different file** from `LinkUartwrite.v`, which
assumes uartwrite's contract for the unrelated reason that its proof is not
written: proving uartwrite does not fix D3 and fixing D3 does not prove
uartwrite, so keeping them apart is what stops either from hiding the other
in `Print Assumptions`.

(Upstream `b7c25cf` — "initialize the tx_lock sleeplock" — is the one-line
source fix, route (1) above. It is NOT in the pinned image: the blessed
kernel state is `ae96fd0` plus a cherry-pick of `9da28f5` only, and
`b7c25cf` is one of the five commits between them that were deliberately
skipped. Picking it up is a separate image bump with its own address sweep.)

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
