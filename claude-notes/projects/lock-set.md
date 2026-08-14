# The per-CPU held-lock set, and the lock ORDER

The design and its phase-1 landing are in
[`design/kernel-proofs.md`](../design/kernel-proofs.md) §Spinlocks and in
`LockSet.v`'s own header. This file is what is LEFT.

**Audit the C at `XV6_REV`, not at whatever `xv6-riscv/` is checked out to.**
That directory is gitignored and is a build input pinned by the top-level
Makefile; a clone left behind reads as a plausible but different kernel, and
locking is exactly where revisions diverge — the pinned revision has the
modular `sleep_prepare`/`sleep()` API, `uartputc_sync` under `tx_lock`, no
`panicking` flag, and no `^P` from the console. `make xv6-rev-check` is the
one-line check; it is silent when the checkout is right. (If it says the pin
is missing, the clone's `origin` is stale against `XV6_URL` — `git fetch` then
succeeds against the wrong remote and the pin stays an unknown object.)

## Where it stands

Phase 1 is in: every hart owns `cpu_locks S`, a held-lock set tied to
`lk->cpu` by co-ownership of that field, maintained by acquire and release.
It is **hidden** — it rides inside `IntrDefs.cpu_hart` under
`cpu_locks_any := ∃ S, cpu_locks S`, and no contract in the tree mentions it.
So it currently proves nothing to a caller; it is the substrate.

## WHERE IT STANDS: the substrate is LANDED AND PROVEN, the clients are not

`cpu_own` carries the held set as an index, and the acquire/release pair is
proved against it.  Building clean: `LockRank.v`, `LockSet.v`, `WpLock.v`,
`WpSconfLock.v`, `CpuOwn.v`, `IntrDefs.v`, `SpecAcquire.v`, `SpecRelease.v`,
`SpecHolding.v`, `ProofAcquire.v`, `ProofRelease.v`, `ProofHolding.v`.

What that establishes, machine-checked rather than argued:

- the **whole-cell `lk_cpu_res` collapse** is sound.  `lk_stake`,
  `lk_cpu_half`, `lk_cpu_rest`, the fixed 1/2 fraction and the two exchange
  wands are DELETED; the lock invariant owns `lk->cpu` at `DfracOwn 1` in
  every state and the read leaves are state-blind for free;
- the **rank-keyed set** works end to end: `lkcpu_take_exchange` mints
  `lk_in i (lock_rank s)` from the caller's premise, where the predecessor had
  to derive freshness from the cpu cell;
- **`CpuOwn.cpu_own_locks_swap`** is the right replacement for the deleted
  existential accessor `cpu_own_locks_acc`: it takes the authority out at a
  set the caller NAMES and puts back a DIFFERENT one, which is what an
  acquisition actually does.

### The premise is NON-MEMBERSHIP for now, not the order

acquire takes `lock_rank s ∉ lks`, not `locks_below lks (lock_rank s)`.  It is
all either obligation needs (minting the fragment; refuting the holder), and it
lands first deliberately.  The bridge to the order form is already in place and
unused: `LockRank.locks_below`, `locks_below_not_elem`,
`LockSet.cpu_locks_insert_below`, `LockSet.cpu_locks_not_in_below`.  Phase 3 is
a premise swap at two sites.

**The known complication for the order phase** is `iput`: it calls
`acquiresleep` while holding `itable.lock`.  That is NOT an order inversion --
`"sleep lock"` (6) is above `itable` (2), and acquiring upward is what the rule
permits.  The hazard is that `acquiresleep` may SLEEP, and `sched`'s
`if (mycpu()->noff != 1) panic("sched locks")` forbids sleeping with another
spinlock held.  The C is safe for a reason outside the lock layer entirely --
`ip->ref == 1` means nobody else can have the inode locked, so the wait loop
never runs -- so proving it needs the icache REF-1 exclusivity theorem
(`design/fs-icache.md`) to reach a non-blocking `acquiresleep` variant.  Owed
either way once `sleep`/`sched` get lock-set-aware contracts.

### `panic_wp_any` STAYS in acquire's contract

The claim that exposing the set kills acquire's `if(holding(lk)) panic` arm is
**false as things stand**, and it was asserted here before the machine saw it.
The refutation needs the held-set FRAGMENT in scope where `holding`'s read
decides its `phi`, and `WpSconfLock.wp_ld_lkcpu_lockopen_gen`'s view premise is
handed only `lock_auth γl st` and the caller's token:

```coq
    (forall st : lock_state, ⊢ lock_auth γl st -∗ T -∗ ⌜phi (lk_cpu_val st)⌝) ->
```

`lk_cpu_frag` is not persistent, so exposing it means borrowing and returning
it inside the invariant open -- a leaf signature change plus a `SpecHolding`
variant concluding `a0 = 0`.  Separate piece of work; do not plan around it
being free.

## WHAT IS LEFT: propagating the premise to the ~50 acquire call sites

~100 files still fail, and they are almost all LOCK CLIENTS.  This part is NOT
mechanical: each lock-holding region must NAME the set it actually holds,
read off the C.  Two shapes:

- **balanced** (acquire and release in the same function): thread `lks`
  unchanged.  This is most of them and it is safe.
- **asymmetric or region-crossing**: the set differs mid-body, and threading
  `lks` unchanged TYPECHECKS while stating something false.  A green build does
  not certify these.  Known instances:
  - `ProofAllocproc` -- allocproc RETURNS holding `p->lock` ("return with
    p->lock held", proc.c).  `SpecAllocproc` says `lks ∪ {[rank "proc"]}`,
    `ProofAllocproc` says `lks`; they disagree, which is the good outcome.
  - `ProofKexit` -- the `wait_lock` -> `p->lock` -> `release(wait_lock)` ->
    `sched()` region, i.e. the non-LIFO case.
  - `ProofKwait` -- three nesting levels (`wait_lock` + per-proc lock).
  - `ProofIput`, `ProofVirtioDiskRw`/`RwB`, `ProofAcquiresleep`, `ProofBread`,
    `ProofSleep`, `ProofPipewrite`, `ProofPrintk` -- lock held across a region
    boundary; threaded unchanged pending review.
  - `SpecKerneltrap` -- threaded a variable where it should be `∅`, to match
    `IntrDefs`' handler precondition `cpu_hart 0 false p ∅`.
  - `UsertrapRes.ut_res` -- existentially quantifies `lks`, which is the shape
    this phase exists to remove.

Done so far, as the pattern for the rest: `ProofSched`'s swtch seam is
`{[lock_rank "proc"]}` (both directions -- `∅` occurs only in the scheduler
loop between `release` and the next `acquire`, which is exactly where
`intr_on()` sits), and `ProofBrelse.brelse_tail` is `{[lock_rank "bcache"]}`
(`n = 1` says exactly one acquire).

## The audit: xv6 never holds two spinlocks of the same NAME

Checked over every `acquire`/`sleep_prepare`/`sleep`/`wakeup`/`acquiresleep`
site in `xv6-riscv/kernel/` at `XV6_REV`. Three families have more than one
instance — **`"proc"`** (NPROC of them), **`"pipe"`** (one per pipe),
**`"sleep lock"`** (the inner spinlock of every `struct sleeplock`) — and no
execution holds two members of any of them at once:

- `"proc"`: `wakeup`/`kkill`/`allocproc`/`scheduler` take one `p->lock` at a
  time. `kexit` finishes `wakeup(p->parent)` BEFORE `acquire(&p->lock)`
  (proc.c:353 vs :355) — which it must, since this revision's `wakeup` scans
  the WHOLE table and no longer skips `myproc()`. `kwait` holds `pp->lock` but
  not its own. `sleep_prepare`/`sleep` acquire only the caller's own `p->lock`.
- `"pipe"`: every pipe entry point touches exactly one pipe.
- `"sleep lock"`: `lk->lk` is held only inside
  `acquiresleep`/`releasesleep`/`holdingsleep`, which call only
  `sleep_prepare`, `sleep`, `wakeup` and `myproc` — none of which touches a
  sleeplock. Two *sleeplocks* ARE held at once (`sys_unlink` holds `dp` and
  `ip`), but their inner spinlocks never overlap. The sleeplock ORDER is a
  separate discipline and is out of scope here.

**Consequence: an order on the FAMILY NAMES alone is enough.** The
lock-pointer tiebreaker is never exercised, so it can be left out of the
index rather than carried and never used — see "the shape of the index".

## The order

Every pair of spinlocks xv6 ever holds simultaneously, as edges `a → b`
("`a` held while `b` is acquired"):

| edge | where |
| --- | --- |
| everything `→ pr → uart` | **`panic()` acquires `pr.lock`** — this revision deleted the `panicking` flag, so `panic` is `printk("panic: ")` + `printk("%s\n")` + self-jump, and `printk` holds `pr.lock` across `consputc` → `uartputc_sync` → `acquire(&tx_lock)`. Panic sites under a held lock are everywhere (`bget` under `bcache`, `log_write` under `log`, `sleep_prepare`/`sched` under `proc`, `free_desc` under `virtio_disk`, `iget` under `itable`, and `acquire`/`release`'s own arms under an arbitrary set) |
| `cons → uart` | `consoleintr`'s echo `consputc` under `cons.lock` |
| `log → bcache` | `log_write` holds `log.lock`, calls `bpin` |
| `itable → sleep lock` | `iput` holds `itable.lock`, calls `acquiresleep` |
| `{cons, log, itable, sleep lock, pipe, time, virtio_disk, wait_lock} → proc` | every `sleep_prepare` and `wakeup` call site (both acquire `p->lock`) |
| `proc → nextpid` | `allocproc` holds `p->lock`, calls `allocpid` |
| `proc → kmem`, `wait_lock → kmem` | `allocproc`→`kalloc`, `freeproc`→`kfree` (the latter under `wait_lock` too, from `kwait`) |

It is acyclic. One total extension, which is what the rank table should be:

```
0 ftable · 1 itable · 2 log · 3 bcache · 4 cons · 5 sleep lock · 6 pipe
7 time · 8 virtio_disk · 9 wait_lock · 10 proc · 11 nextpid · 12 kmem
13 pr · 14 uart
```

**`uart` is the TOP and nothing is acquired under it**: `uartputc_sync` holds
`tx_lock` only across the LSR spin and the THR write; `uartwrite` calls
`sleep_prepare(&tx_chan)` BEFORE taking `tx_lock` and `sleep()` after
releasing it; `uartintr` takes no lock at all (it `wakeup`s and calls
`consoleintr` bare). So there is no `uart → cons` and no `uart → proc` edge in
either direction but the one through `pr`.

`unreachable()` — new at this revision, and the reason the split matters — is
NOT `panic`: it does a raw store to an undecoded device address and spins,
taking no lock. Sites that use it (`sched`'s three checks, `pop_off`,
`end_op`'s `log.committing`) impose no order constraint. Only `panic` does.

## The shape of the index

**`cpu_own n eb p C b M` with `M : gmap nat (mword 64)` — rank ↦ the address
held at that rank.** The rank comes from the name the lock already carries:
`is_lock γ lk (s : string) R` holds `lock_name lk s`, so a total
`lock_rank : string → nat` (the table above; anything unlisted maps to 0,
which is conservative — such a lock may then be acquired only from `M = ∅`)
gives every existing lock its rank with **no new parameter on `is_lock`,
`newlock`, `lock_inv` or any of the eight lock leaves**. `is_kmem`,
`procs_inv`, `is_tickslock` already pin `s`, so they are correct as written.

Why a `gmap nat` and not a `gset` of `(rank, address)` pairs:

- The audit says the address component is inert, so a pair set carries a field
  no premise ever reads.
- **`set_solver` does not work over `gset (mword n)`** (see the durable notes)
  and every side condition has to go by named lemma. With `nat` KEYS the
  ordinary stdpp `dom`/`map_Forall` automation works, and the `mword` appears
  only as a VALUE, where no `EqDecision`/`Countable` instance is consulted.
- Freshness comes free: the order premise `∀ r ∈ dom M, r < rank` already
  gives `rank ∉ dom M`, so the insert's side condition no longer needs
  `LockSet.cpu_locks_fresh`'s cpu-field derivation. Keep the field
  co-ownership anyway — it is what release needs to clear `lk->cpu`, it is
  what makes "`lk->cpu = &cpus[i]`" and "`lk ∈ hart i`'s set" one fact, and it
  is what kills the panic arm below.
- Two locks of the same family can then never be co-held, a restriction the
  audit says xv6 satisfies. If that ever stops being true, the change is
  local: the key becomes `nat * mword 64` under the lexicographic order and
  every premise-discharge site stays a `vm_compute`.

The camera becomes a `gmap_view nat (mword 64)` (fragment
`gmap_view_frag r (DfracOwn 1) lk` = "I hold `lk` at rank `r`", exclusive at
`r`, and agreement reads `M !! r = Some lk`) in place of the
`auth (gset_disj (mword 64))` of phase 1.

## What it buys

Write `M ≺ r` for `∀ q ∈ dom M, (q < r)%nat`.

- **acquire** gains `⌜M ≺ lock_rank s⌝` and returns `M` extended at that rank.
  Trivial at `M = ∅`, which is most of the ~50 call sites; elsewhere a
  `vm_compute` on the rank table. A function that acquires while `∀M`-generic
  carries the premise on its own contract — and that premise, one per
  function, IS the locking discipline written down.
- **`b = true` gets `M = ∅`**, beside the `n = 0 ∧ eb = true` it already
  carries. Then `sie_arm true`'s `cpu_hart 0 true p` says "a hart with
  interrupts enabled holds no spinlock", the theorem the whole abstraction
  exists for.
- **ACQUIRE'S PANIC ARM GOES DEAD, and that is the big prize.**
  `design/kernel-proofs.md` currently records the arm as REAL because "a
  non-holder knows nothing about `lk->cpu`". With `M` exposed that stops being
  true: `M ≺ lock_rank s` gives `lk ∉ M`, and `lk_stake` says the half of
  `lk->cpu` pinned at `cpus_ptr i` is held only by hart `i`'s set — so
  `lk->cpu ≠ cpus_ptr i` (`cpus_ptr_inj`), so `holding(lk) = 0` and the
  `jal panic` arm is unreachable. **That retires `panic_wp` from every acquire
  call site**, which is most of the 169 files still threading `PanicStub.v`'s
  credential ([`panic.md`](panic.md)). Do this sweep BEFORE the panic splice,
  not after.
- **`sched()` becomes provable rather than asserted.** The C checks
  `if (mycpu()->noff != 1) panic("sched locks")`; the index states the
  semantic version — a swtch happens only at `M = {proc ↦ &p->lock}`.

## Why the index must be the SET, not a bound

A single stored bound — even a tight max, with the pre-acquire bound stashed
in the `locked` token and restored at release — is not maintainable, and the
counterexample is `kexit`:

```
proc.c:347  acquire(&wait_lock);      M = {wait_lock}
proc.c:355  acquire(&p->lock);        M = {wait_lock, proc}   token records "wait_lock"
proc.c:360  release(&wait_lock);      M = {proc}              NON-LIFO
            sched();                  -> swtch, never returns
proc.c:460  <scheduler> release(&p->lock);
proc.c:441  <scheduler> intr_on();     requires M = ∅
```

Releasing a NON-max lock leaves the token's recorded bound stale, so the
scheduler's `release(&p->lock)` restores `wait_lock` instead of `⊥` and
`intr_on()` is then unprovable. With the map it is just
`{wait_lock, proc} → {proc} → ∅`. This is the ONLY non-LIFO release left in
the tree — the old `sleep(chan, lk)`, which released the caller's lock while
holding `p->lock`, is gone at this revision — but one is enough, and it feeds
the one place the emptiness theorem is consumed.

State the premises with `≺` anyway: it reads exactly as well in a contract as
a scalar comparison would.

## Delete on the way

`IntrDefs.cpu_locks_any`, `CpuOwn.cpu_own_locks_acc`, and the `Slk` plumbing
in `ProofAcquire`/`ProofRelease` — with the index exposed, callers name the
map. `IntrDefs.cpu_priv` STAYS: the map travels with the cells across every
SIE seam either way, and bundling is what stops a leaf taking one and
stranding the other. Note one seam carries a NON-EMPTY map: `sched`'s park
hands `{proc ↦ &p->lock}` across `swtch` from the process context to the
scheduler context on the same hart. That is sound because the set is
per-HART, not per-thread — and it is the reason it must be.

## Two things to know before touching this

- **A `gset`/`gmap` with an unconditional insert and a membership tie is
  INCONSISTENT** (insert `lk` twice, delete once, read `lk ∈ ∅`). Phase 1's
  insert is conditional because its side condition is discharged from the
  `lk->cpu` cell; after the sweep it is discharged from the order premise.
  Never make it unconditional.
- **`set_solver` does not work over `gset (mword n)`** — see the durable
  notes. This is the reason the key type is `nat`.
