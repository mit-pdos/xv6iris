# A data race in xv6's `acquire` → `holding()` (benign, but not lock-protected)

Found 2026-10-11 by the W8-design spike (`notes/W8-design.md` §0 item 7, §7), while classifying every kernel
memory access of the verified image (`Xv6/KernelImage.lean`, xv6-riscv `b72cbac1`, branch `verified`).

## The code

xv6's spinlock (`kernel/spinlock.c`):

```c
int holding(struct spinlock *lk) {
  return lk->locked && lk->cpu == mycpu();
}
void acquire(struct spinlock *lk) {
  push_off();
  if (holding(lk)) panic("acquire");          // <-- called WITHOUT holding lk
  while (__sync_lock_test_and_set(&lk->locked, 1) != 0) ;
  __sync_synchronize();
  lk->cpu = mycpu();
}
void release(struct spinlock *lk) {
  if (!holding(lk)) panic("release");         // called by the holder: reads its own write, fine
  lk->cpu = 0;
  __sync_synchronize();
  __sync_lock_release(&lk->locked);
}
```

The compiled image (`Xv6/KernelImage.lean`):

| pc | instruction | what |
|---|---|---|
| `holding+0x0` (`0x80000bf2`) | `lw a5,0(a0)` | read `lk->locked` (plain load) |
| `holding+0x12` (`0x80000c04`) | `ld a5,16(a0)` | read `lk->cpu` (plain load) |
| `acquire+0x..` | `amoswap.w.aq a5,a5,(s1)` | take the lock |
| `acquire+0x..` | `sd a0,16(s1)` | `lk->cpu = mycpu()` (plain store, **no fence after the AMO**) |
| `release+0x..` | `sd zero,16(s1)`; `fence rw,w`; `sw zero,0(s1)` | clear `cpu`, then release `locked` |

## The race

CPU **B** calls `acquire(lk)` while CPU **A** holds `lk` (or is just taking or releasing it). B's `holding()`
performs two **plain loads** — `lk->locked` and `lk->cpu` — without holding `lk` and with no acquire ordering.
Concurrently A performs **plain stores** to `lk->cpu` (`sd a0,16(s1)` right after winning the AMO, and `sd
zero,16(s1)` in `release`). Nothing orders B's read against A's write: it is a **data race** on `lk->cpu`
(and, more mildly, a racy read of `lk->locked` against A's AMO/`sw`).

Under RISC-V's weak memory model (RVWMO), B's read of `lk->cpu` may return **any value A or an earlier holder
ever wrote there that is not yet overwritten in B's view**: A's pointer `&cpus[A]` before A's release is
visible, an older holder's pointer, or 0. (Under the old TSO-style machine model the same read is also racy;
the window is just narrower.)

## Why it is benign

`holding()` only compares the value with `mycpu()`, i.e. asks "is it **my** pointer?". B can never read its
**own** pointer `&cpus[B]`:

* every store to `lk->cpu` writes either 0 or the storing CPU's own `&cpus[c]`;
* B's own latest store to `lk->cpu` is 0 (its last `release` cleared it), and by per-location coherence B
  cannot read its own older store past its own newer one.

So for a non-holder `holding()` always returns 0, `acquire` never false-panics, and the outcome is correct on
every RVWMO execution. The existing verified proofs already rely on exactly this argument:
`lkCpu_read_not_mine` (`MachCSL/Lock.lean:18-22`, "a racy read by it never returns its own pointer").

## Why it matters anyway

1. **C11:** `lk->cpu` is a plain (non-atomic) field accessed concurrently by a writer and a reader — a data
   race, i.e. undefined behaviour under the C11 memory model. It works because gcc compiles it to single aligned
   8-byte `ld`/`sd`, which RVWMO makes single-copy atomic. A different compiler or optimisation could legally
   break it. (Upstream xv6 has the same pattern.)
2. **Our plan was wrong about it.** The roadmap (and the W13 I/O census) classified the read of `lk->cpu` at
   `holding+0x12` as protected by its own lock. It is not: for a non-holder it is a racy read of a
   **not-yet-published** plain store. The pin table already marks it `PResidue` (`Weak/KernelPins.lean:255`).
3. **Consequence for the proof:** W8's access-discipline export cannot say "every observed foreign write
   reached the reader through a lock handoff" for this byte. The pinned export (`xv6AccessDisc`, W8-design §1)
   therefore **exempts the lock-layer words** from that clause and covers them by a separate lock-word rule
   (`lockWordDiscAt`), whose only consequence used downstream is the "never my own pointer" fact above. The
   final robustness argument (W11 `badSeg`, W13 (K)) must route `lk->cpu` reads through that rule.

## Possible fix in xv6 (not applied; the verified branch is the object of study)

Make `lk->cpu` an atomic accessed with relaxed loads/stores (`__atomic_load_n(&lk->cpu, __ATOMIC_RELAXED)`,
`__atomic_store_n(..., __ATOMIC_RELAXED)`): same machine code on RISC-V, no C11 undefined behaviour. Or drop
the `holding()` check from `acquire` (it only detects self-deadlock).
