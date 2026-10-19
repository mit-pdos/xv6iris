# W10-P0(a) — the P-WFENCE census of the kernel image

Route-P spike P0(a) (`notes/weak-allocproc-routeP-design.md` §3.4, §5 row P0).  Slot w2, 2026-10-19.  Census
only: no Lean, no builds.  Image: `Xv6/KernelImage.lean` (xv6-riscv `b72cbac1`, 8 814 instructions, the objdump
text in its comments); fence and AMO facts: `Weak/LockFacts.lean` (`fenceCensus`, `amoCensus`, machine-checked);
custody classes: `Xv6/AccessDiscipline.lean` `custAt :271` (lockw, pub, dynamic lockw, pte, racy, hart, free);
racy readers: the 18-site census of `notes/W10-6m-census.md` §1/§3.  The C source of `origin/verified` was used
for orientation only; every verdict was read off the binary.

## 0. Verdict

**P-WFENCE, as the design states it, FAILS.**  The design expects the only foreign-readable plain stores that are
not WCrel to be the `lk->cpu` stores and `initlock`.  The census finds three more groups.

1. **`ip->ref` (4 sites, a real counterexample).**  The four stores that change the reference count of an inode
   other harts may already hold are `iget+0x58`, `idup+0x1c`, `iput+0x22` and `iput+0x8a`.  Each is FIFO-after
   two unfenced stores:
   - the `lk->cpu = me` store of the same `itable.lock` acquire (`acquire+0x28`);
   - the `sw zero` of the hart's most recent release (`release+0x1a`).

   Other harts read `ip->ref` without a lock at `ilock+0xe` and `iunlock+0x1c`.  The waits-for cycle
   (E5)→(E1)→(E3)→(E4) of design §3.4 is closed by an RVWMO-consistent GF.  §4.3 builds it from ordinary
   `namex` traffic, with no special timing.  In that GF, `noStuckP` has no FIFO member.
2. **PTE stores (5 sites: `walk+0x90`, `mappages+0x60`, `uvmunmap+0x46`, `freewalk+0x42`, `uvmclear+0x14`).**
   These are in the exempt class `pte` and are not WCrel.  In fact they are CHAINED: the owning hart has custody,
   and custody is handed off by `p->lock` or at process creation.  The export, however, does not certify this.
   So P-WFENCE needs the same GF-level PTE custody fact as Q-6M-PTE (a).
3. **The `lk->cpu` stores (`acquire+0x28`, `release+0x12`) are acyclic, but not for the design's reason.**  The
   design's premise (b) says their FIFO-earlier stores are only `push_off`'s per-cpu words.  That is false: the
   FIFO-earlier stores include the previous release's `sw zero` and anything stored since (§4.1).  They are
   cycle-free by a READER-side argument instead.  Their only racy reader is `holding+0x12` inside a non-holder's
   `acquire`, and after that read the reader issues only own-stack accesses and failed AMOs on the same lock word
   until its winning `.aq` AMO.

`initlock` (`+0x0a`, `+0x0e`) behaves as expected: nothing reads it before publication.  `started` (`main+0xb0`)
and the release `sw zero` (`release+0x1a`) are WCrel.

**Strict WCrel sites in the whole image: 5** (`release+0x1a`, `main+0xb0`, `virtio_disk_rw+0x192` avail idx,
`virtio_disk_rw+0x19e` notify [MMIO], `virtio_disk_intr+0x6a` `b->disk = 0`).  Everything else is not WCrel,
because the text has only seven fences (`LockFacts.fenceCensus`), and `acquire` has none (its `amoswap.w.aq`
is the image's only AMO).

## 1. Columns and method

**Store sites.**  Every `sb/sh/sw/sd` in the text (compressed forms included): **1 331**.  There are no
`fsd`/`fsw`.  The one AMO (`acquire+0x1c`) is an exclusive write (it lands at once under P) and is not a FIFO
store.

**Width.**  8 B: 1 102; 4 B: 148; 1 B: 47; 2 B: 34.

**Target class.**  A class is assigned per site from three things: the base register (`sp`/`s0` are the frame; all
41 `s0`-based stores are frame stores, including `printk`'s va-area `s0+8..+56`), the base's provenance in the
disassembly, and the function.

**Foreign-readable?**
- **RACY**: another hart (or the walker) can read the store's value with no sync path.  These are exactly the
  bytes of the exempt custody classes read at the 18 census sites: lock words (`holding+0x0`, `holding+0x12`,
  plus the failed `amoswap`), `started` (`main+0x16`), `ip->ref` (`ilock+0xe`, `iunlock+0x1c`), PTEs (9 software
  walks plus the hardware walker), and disk-written RAM (4 sites, whose sources are DMA writes, not hart stores).
- **chained**: readable by another hart only through lock co, the `started` hop, or a creation/hand-off chain.
  Design §3.4 says such a source is landed before the chain's acquire is realized, so no (E5) edge arises.
- **no**: per-cpu cells, read by no other hart.
- **MMIO**: not RAM.  Not buffered under P (design §1, I/O row).

**WCrel.**  On EVERY backward path from the store within its function, a fence with `pw`∧`sw` (`fence rw,w`,
`fence rw,rw`, or `fence` = iorw,iorw) is met before:
- any store,
- any `jal` (a callee is assumed to store),
- the function entry.

An AMO is passed through, because it is not a FIFO store.  All five WCrel sites run with interrupts off (release
under `push_off`, boot, `vdisk_lock`, the trap handler), so no `kernelvec` frame can land between the fence and
the store.

**Unfenced FIFO-earlier set** (used in §4): the hart's stores issued after its most recent `pw`∧`sw` fence and
before the site.  Rule 4 does not order these before the site, so they are exactly the (E1) edges that are not
gmo-backward.

The census was produced by a scratch Python pass over the image (CFG per function, call = store); it is not
committed.

## 2. Headline counts

| class | sites | foreign-readable? | WCrel |
|---|---:|---|---:|
| stack (`sp`/`s0` frame; 189 functions; `kernelvec` 17) | 953 | chained (a process's kernel stack migrates under `p->lock`) | 0 |
| stack via an escaped pointer (`argint`/`argaddr`/`argfd`/`stati`/`dirlookup` `*poff`/`namex` name/`printint` buf/`pipealloc` `*f0,*f1`/`sys_exec` argv/`kexec` ustack/`alloc3_desc` idx) | 23 | chained | 0 |
| proc fields (`p->state/chan/killed/xstate/parent/sz/pagetable/ofile/cwd/root/seccomp/pid/context`; `p->lock`, `wait_lock`, owner) | 54 | chained | 0 |
| trapframe (`_trampoline` 31, `usertrap`, `syscall`, `prepare_return`, `kfork`, `kexec`, `forkret`) | 49 | chained | 0 |
| `swtch` context save (`p->context` from `sched`, `c->context` from `scheduler`) | 14 | chained / no | 0 |
| per-cpu (`push_off` noff/intena, `pop_off`, `scheduler` `c->proc`/`c->intena`, `sched` intena) | 8 | **no** | 0 |
| lock-protected globals (`cons`, `kmem` + freed page `r->next`, `nextpid`, `ticks`, `first`) | 15 | chained | 0 |
| buffer cache (headers under `bcache.lock`; data and `b->valid`/`b->disk` under the buf sleeplock / `vdisk_lock`) | 29 | chained (and device-read via DMA) | 1 |
| inode fields (sleeplock / `itable.lock`; not `ref`) | 25 | chained | 0 |
| log (`log.lock`, committing hand-off) | 14 | chained | 0 |
| file (`ftable.lock`, ilock for `off`, fresh files in `sys_open`) | 14 | chained | 0 |
| pipe (`pi->lock`) | 5 | chained | 0 |
| fresh, unpublished objects (`pipealloc` pipe and file fields) | 12 | chained | 0 |
| sleeplock fields (`lk->lk`) | 7 | chained | 0 |
| generic copy loops (`memset`/`memmove`/`strncpy`/`safestrcpy`/`copyinstr`), none on a live racy byte (PT pages are zeroed before they are linked; freed pages are `free`) | 9 | chained | 0 |
| boot, hart 0 before `started` (`devsw`, `kernel_pagetable`, `procinit`, `initproc`, `binit` lists, `disk` pointers and `free[]`) | 23 | chained (pub hop) | 0 |
| virtio driver state (`disk.free[]`, `info[].status/b`, `used_idx`; `vdisk_lock`) | 6 | chained | 0 |
| device-read RAM (descriptors, `ops` headers, avail ring, avail idx) | 21 | device, chained via the avail-idx publication + drain fences | 1 |
| MMIO (UART 9, halt device `0xe000000` 1, PLIC 6, virtio regs 17) | 33 | n/a | 1 |
| lock name (`initlock+0x08`) | 1 | chained | 0 |
| **lock words** (`initlock+0x0a,+0x0e`; `acquire+0x28`; `release+0x12,+0x1a`) | 5 | **RACY** | 1 |
| **publication** (`main+0xb0`) | 1 | **RACY** | 1 |
| **racy `ip->ref`** (`iget+0x58,+0x78`; `idup+0x1c`; `iput+0x22,+0x8a`) | 5 | **RACY** | 0 |
| **PTE** (`walk+0x90`, `mappages+0x60`, `uvmunmap+0x46`, `freewalk+0x42`, `uvmclear+0x14`) | 5 | **RACY by class** (exempt in `chainOkAt`); chained in fact | 0 |
| **total** | **1 331** | | **5** |

## 3. The WCrel sites

| pc | site | store | fence before |
|---|---|---|---|
| `0x80000cfa` | `release+0x1a` | `sw zero,0(s1)` (`lk->locked = 0`) | `release+0x16` `fence rw,w` (adjacent, `LockFacts.relAdj`) |
| `0x80000f7e` | `main+0xb0` | `sw a4,0(a5)` (`started = 1`) | `main+0xac` `fence rw,w` |
| `0x80005c86` | `virtio_disk_rw+0x192` | `sh a5,2(a4)` (avail idx) | `+0x186` `fence` (iorw,iorw) |
| `0x80005c92` | `virtio_disk_rw+0x19e` | `sw zero,80(a5)` (QUEUE_NOTIFY, MMIO) | `+0x196` `fence` |
| `0x80005d92` | `virtio_disk_intr+0x6a` | `sw zero,4(a0)` (`b->disk = 0`) | `+0x3e` `fence` (also on the loop's back edge) |

## 4. The RACY-class stores that are not WCrel (14 sites)

### 4.1 `lk->cpu`: `acquire+0x28` `sd a0,16(s1)`, `release+0x12` `sd zero,16(s1)` — cycle-free (reader side)

**Unfenced FIFO-earlier set of `acquire+0x28`.**  This is NOT only `push_off`'s per-cpu words.  On every path it
contains:
- `push_off+0x20`/`+0x36` (per-cpu);
- the frames of `acquire`, `push_off`, `mycpu` and, if the lock is held, `holding` (stack);
- the caller's stores back to its most recent `fence rw,w`.  That fence is always a release's `+0x16`, so the set
  ALWAYS contains that release's `sw zero` (`release+0x1a`, lockw) and its `pop_off+0x1c`.  It can also contain
  proc, inode, buffer and other stores, and other locks' `acquire+0x28` when locks are nested.

So the premise of design §3.4 (b) is false.

**Unfenced FIFO-earlier set of `release+0x12`.**  The whole critical section, including the same lock's
`acquire+0x28`.

**Why there is still no cycle.**  The only foreign reader of a `lk->cpu` byte is `holding+0x12` (callers:
`acquire+0x12`, `release+0xc`, `sched+0x14`).  Only from `acquire` is it a non-holder, so only there is the read
racy (the other two read the hart's own value).

Suppose a cycle `land w′ →E3 r →E4 e →E5 land w →E1 land w′` exists, where `e` is that read.
- If `r` is po-after B's winning `amoswap.w.aq` X on the same lock L, then X reads A's release `sw zero`.  A's
  `fence rw,w` orders `w′` (FIFO-before `w`, which is before the release) before that store.  So
  `w′ <gmo X <gmo r`, which contradicts `r <fr w′`.
- So `r` lies between `e` and X.  The only events there are:
  - `holding`'s tail and `mycpu` (own stack, `tp`);
  - the `panic` arm (MMIO halt);
  - failed `amoswap`s on `L.locked`.
- A failed AMO is an E3 target of `w′` only if `w′` is a plain store to `L.locked` FIFO-before `w`.  Hart A has
  none: its `amoswap` on L drained any such entry (the `sbOverlaps` guard), and its own release `sw zero` is
  FIFO-after `w`.

Hence no cycle passes through a `lk->cpu` store.  This is static, but it is a fact about the READER's code after
`holding+0x12`, not about the writer's fences.  `noStuckP`'s (E1) case must use it in that form.

### 4.2 `initlock+0x0a` `sw zero,0(a0)`, `initlock+0x0e` `sd zero,16(a0)` — as expected

**Callers.**  All callers run at boot on hart 0 before `started`, except two that run later:
- `initlog`, inside `fsinit` from the first process's `forkret`; its lock is reached by other harts only through
  `fork`;
- `pipealloc`, on a fresh `kalloc` page that is published through `f->pipe` and the fd table.

**Reads.**  No racy read can reach these lock words before their publication chain does.  `initlock+0x08`
(`lk->name`) is not a lock word (`lockWordsByte` is bytes `+0..3` and `+16..23`).

### 4.3 `ip->ref` — **the exception**

| pc | site | store | racily readable? | unfenced FIFO-earlier racy-class stores |
|---|---|---|---|---|
| `0x8000300c` | `iget+0x58` | `sw a5,8(s1)` (`ref++`, cached inode) | yes (`ref ≥ 1`: other holders exist) | `acquire+0x28` on `itable.lock`, then nothing (loop of loads); before that, the last `release+0x1a` |
| `0x80003338` | `idup+0x1c` | `sw a5,8(s1)` (`ref++`) | yes | same |
| `0x800034f6` | `iput+0x22` | `sw a5,8(s1)` (`ref--`) | yes when `ref > 1` | same |
| `0x8000355e` | `iput+0x8a` | `sw a5,8(s1)` (`ref--` after `itrunc`) | yes: between `release` `+0x66` and `acquire` `+0x82`, an `iget` of the same `(dev, inum)` can take `ref` 1→2 | same (`acquire` at `+0x82`) |
| `0x8000302c` | `iget+0x78` | `sw a5,8(s3)` (`ref = 1`, recycled slot) | class racy, but no holder exists (`ref` was 0), so no racy read | — |

**GF 1 (the `lk->cpu` variant).**
- A runs `iget`: `amoswap.aq` on `itable.lock`, then `w′ = sd lk->cpu = &cpus[A]` (`acquire+0x28`), then
  `w = ref++` (`iget+0x58`), then `release`.
- B already holds a reference to the same inode, for example the root or cwd, or a directory both harts are
  walking in `namex`.  B runs `ilock(ip)`, whose `e = ilock+0xe` reads `ref` = A's `w`.  Then B runs
  `iunlockput` → `iput` → `acquire(itable.lock)` → `holding`.  There `+0x0` reads `locked = 1` (A's AMO) and
  `r = holding+0x12` reads the OLD `lk->cpu`, i.e. the 0 of the previous `release+0x12`.

RVWMO allows this: `w <gmo e` (rfe), and `e <gmo r` (B's `acquiresleep` `.aq` lies between; this is not needed
either way).  `r <gmo w′` (fr), while A's `w′ <po w` are two plain stores to different addresses with no fence
and no dependency, so they are unordered.  The gmo order `amoswap_A < w < e < r < w′ < release_A` satisfies
every axiom (the AMO's `.aq` orders only what comes after it).  This is precisely the [OWN.64] read
("a non-holder never reads `&cpus[x]`").

**GF 2 (the release variant, with no `lk->cpu` involved).**
- A: `iunlockput(dp)` → `releasesleep` → `release(dp->lock.lk)`, whose `w′ = sw zero` (`release+0x1a`, after
  its fence) → `iput(dp)` → `acquire(itable.lock)` (`amoswap.aq`; no fence) → `w = ref--` (`iput+0x22`).
- B, holding a reference to `dp`, runs `ilock(dp)`: `e = ilock+0xe` reads A's `w`.  Then `acquiresleep` →
  `acquire(dp->lock.lk)` → `r = holding+0x0` (or a failed `amoswap`) reads `lk.locked = 1`, the co-predecessor of
  `w′`.

RVWMO allows this: `fence rw,w; sw` followed by a later `amoswap.aq` and stores does NOT order the `sw` before
them.  No rule covers `[W];po;[AQ-AMO]`, and `rl` is not set.  So `w <gmo w′` is legal and
`w < e, r < w′` is consistent.

**The P walk on either GF.**
1. `e` (`rd` arm) waits for `land w` (E5).
2. `land w` waits for `land w′`, the FIFO (E1).
3. `land w′` waits until every GF reader of its co-predecessor is realized, including `r` (E3: the `land` arm of
   the gate).
4. `r` waits for `e`, which is po-earlier (E4).

This is a deadlock: no FIFO member exists, so `noStuckP` is false in both GFs.

Fixing the writer side is impossible without a kernel change (a fence before `ref++`).  The reader-side argument
of §4.1 also does not apply, because `ilock`/`iunlock` continue into arbitrary code.

### 4.4 PTE stores — chained given custody

| pc | site | store |
|---|---|---|
| `0x8000103e` | `walk+0x90` | `sd a5,0(s2)` (link a fresh PT page; the page was zeroed by `memset` while still `free`) |
| `0x800010e2` | `mappages+0x60` | `sd a5,0(a0)` |
| `0x800012a6` | `uvmunmap+0x46` | `sd zero,0(s1)` |
| `0x8000141a` | `freewalk+0x42` | `sd zero,0(s1)` |
| `0x80001514` | `uvmclear+0x14` | `sd a5,0(a0)` |

**Kernel table.**  Written in `kvmmake` on hart 0 and published by `main+0xb0`, which is WCrel.

**User tables.**  Written only by the owning process's kernel code: `kfork`/`kexec` on unpublished tables, and
`growproc`/`uvmunmap`/`uvmclear` on the running process.  A foreign walker or software walk reads them only
after the `p->lock` hand-off (scheduler release `fence rw,w` → acquire), so the reads are chained and no (E5)
edge arises.  The export does not certify this (`pte` is exempt in `chainOkAt`).  P-WFENCE therefore inherits
Q-6M-PTE (a), GF-level PTE custody from the realized prefix.  Walker A/D write-backs are exclusive pairs, not
FIFO stores.

## 5. What this means for route P

- **Every RACY source other than `ip->ref` and PTE is safe.**  `holding+0x0` and failed AMOs read the AMO (lands
  at once), `release+0x1a` (WCrel) or `initlock` (unpublished).  `holding+0x12` reads `lk->cpu` (§4.1, reader
  side).  `main+0x16` reads `main+0xb0` (WCrel).  The device reads the avail idx (WCrel) and, after it, chained
  ring and descriptor bytes, with the drain fences before the notify.
- **The obstruction is the two `ip->ref` reader sites (`ilock+0xe`, `iunlock+0x1c`).**  Their values matter only
  to `blez` → `unreachable`.  The export already carries the value fact (`racyValOk`: `ref ∈ [1, 2^31)`), and
  W10-6m §3.3 routes them by T (the taint dies at `blez`).

The cheapest repair keeps P's FIFO and gives the gate's `rd` arm ONE exception.  At these two pcs the read may
be replayed at the member's latest landed value (`≥ 1` by `racyValOk`), not at GF's source.  That removes their
(E5) edges, and with them the cycle in GF 1 and GF 2.  The cost is that "values agree by construction" no longer
holds at two pcs, so the walk has to carry a two-site T datum.  That is the per-site value datum P wanted to
retire, restricted to two value-insensitive racy reads.

The alternatives:
- (b) a NAMED premise excluding these GFs: WEAKER, not faithful, because GF 1 and GF 2 are RVWMO behaviours;
- (c) a kernel change (`ref` read under `itable.lock`): out of scope.

Owner question for the next plan revision: **Q-P-WFENCE-REF** — (a) the two-site `rd` exception (recommended;
it is FAITHFUL and changes only the walk's datum, not the machine) / (b) named premise / (c) kernel change.

**Spec marks.**  GF 1 and GF 2 are allowed by RVWMO and riscv.cat: rule 4 (a fence orders only its pred → succ
sets), rule 5 (`.aq` orders the AMO before what follows, not what precedes it), the load value axiom, and
coherence.  They are forbidden by P's FIFO plus gate.  So P without the repair is STRONGER than RVWMO on xv6's
GF set.  The census changes nothing about RVWMO, Sail, Zifencei or the PMAs.

**Machine-checking.**  The WCrel column depends only on `LockFacts.fenceCensus` and the CFG.  A
`decide +kernel` leaf over `textPcs` for "the WCrel stores are exactly these five" is feasible (S–M).  The class
and foreign-readable columns are semantic (base provenance, custody), so this spike records them as a note.

## 6. Appendix — every non-stack store site, by function

`+off/width`; `ᵂ` = WCrel.  The 953 frame stores (`sp`/`s0`) are not listed one by one.  They are 946 `sd`
(prologue saves, spills, context) and 7 narrow locals.  The largest counts are `printk` 33, `kexec` 25,
`filewrite` 17, `piperead` 17, `kernelvec` 17 and `dirlookup` 16.

| function | sites (class: +off/width) |
|---|---|
| `consoleread` `8000017a` | prot: +82/4 +ea/4 |
| `consoleintr` `800002c8` | prot: +66/4 +70/1 +c8/4 +120/4 +146/4 +152/1 +15a/4 |
| `consoleinit` `80000434` | boot: +30/8 +3a/8 |
| `printint` `80000490` | stack-esc: +34/1 +54/1 |
| `unreachable` `80000860` | mmio: +c/1 |
| `uartinitone` `80000896` | mmio: +a/1 +14/1 +1c/1 +22/1 +28/1 +30/1 +3e/1 |
| `uartwrite` `8000091e` | mmio: +6a/1 |
| `uartputc_sync` `800009ac` | mmio: +4e/1 |
| `kfree` `80000a96` | prot: +48/8 +4a/8 |
| `kalloc` `80000b7e` | prot: +26/8 |
| `initlock` `80000bd8` | lockname: +8/8 ; **lockw: +a/4 +e/8** |
| `push_off` `80000c1e` | percpu: +20/4 +36/4 |
| `acquire` `80000c58` | **lockw: +28/8** |
| `pop_off` `80000c98` | percpu: +1c/4 |
| `release` `80000ce0` | **lockw: +12/8** +1aᵂ/4 |
| `memset` `80000d18` | generic: +14/1 |
| `memmove` `80000d78` | generic: +20/1 +56/1 |
| `strncpy` `80000e26` | generic: +1e/1 +32/1 |
| `safestrcpy` `80000e6c` | generic: +24/1 +2a/1 |
| `main` `80000ece` | pub: +b0ᵂ/4 |
| `walk` `80000fae` | **pte: +90/8** |
| `mappages` `80001082` | **pte: +60/8** |
| `kvminit` `8000121e` | boot: +10/8 |
| `uvmunmap` `80001260` | **pte: +46/8** |
| `freewalk` `800013d8` | **pte: +42/8** |
| `uvmclear` `80001500` | **pte: +14/8** |
| `copyinstr` `80001724` | generic: +40/1 +b2/1 |
| `procinit` `80001898` | boot: +7a/4 +92/8 |
| `forkret` `800019ae` | prot (`first`): +28/4 ; trapframe: +48/8 |
| `freeproc` `80001b0e` | proc: +14/8 +22/8 +26/8 +36/4 +46/1 +4a/8 +4e/4 +52/4 +56/4 |
| `allocproc` `80001b72` | prot (`nextpid`): +86/4 ; proc: +8a/4 +9a/4 +a2/8 +ae/8 +c8/8 +d0/8 |
| `userinit` `80001c72` | boot: +14/8 ; proc: +1c/8 +24/8 +2a/4 +2e/8 |
| `growproc` `80001cb4` | proc: +36/8 |
| `kfork` `80001d16` | proc: +38/8 +9e/8 +ac/8 +b8/8 +ce/8 +e8/8 +100/4 ; trapframe: +50/8 +52/8 +54/8 +58/8 +6a/8 |
| `scheduler` `80001e38` | percpu: +2c/8 +6c/8 +82/4 +86/8 ; proc: +68/4 |
| `sched` `80001eec` | percpu: +7a/4 |
| `yield` `80001fa8` | proc: +16/4 |
| `sleep_prepare` `80001fd4` | proc: +1a/8 |
| `sleep` `80002010` | proc: +1a/4 |
| `wakeup` `80002040` | proc: +44/8 +4e/4 |
| `reparent` `800020a6` | proc: +3e/8 |
| `kexit` `800020fc` | proc: +46/8 +5c/8 +70/8 +94/4 +9a/4 |
| `kkill` `800021b6` | proc: +42/4 +64/4 |
| `setkilled` `80002222` | proc: +12/4 |
| `kwait` `80002270` | proc: +60/8 |
| `swtch` `800024b6` | context: +0 +4 +8 +a +c +10 +14 +18 +1c +20 +24 +28 +2c +30 (all /8) |
| `prepare_return` `80002560` | trapframe: +36/8 +40/8 +4c/8 +52/8 |
| `clockintr` `800025d4` | prot (`ticks`): +40/4 |
| `usertrap` `800026b0` | trapframe: +2e/8 +9c/8 |
| `argint` `80002936` | stack-esc: +10/4 |
| `argaddr` `80002952` | stack-esc: +10/8 |
| `syscall` `80002996` | trapframe: +46/8 +4e/8 +6a/8 |
| `sys_sbrk` `80002a7e` | proc: +54/8 |
| `sys_seccomp` `80002c06` | proc: +20/8 |
| `binit` `80002c34` | boot: +34/8 +38/8 +54/8 +56/8 +68/8 +6a/8 |
| `bread` `80002cba` | buf: +4c/4 +90/4 +94/4 +98/4 +9e/4 +d2/4 |
| `brelse` `80002dc2` | buf: +30/4 +38/8 +3c/8 +4a/8 +54/8 +5a/8 +5c/8 |
| `bpin` `80002e46` | buf: +1c/4 |
| `bunpin` `80002e7a` | buf: +1c/4 |
| `balloc` `80002eae` | buf: +3c/1 |
| `iget` `80002fb4` | **racy: +58/4** +78/4 ; inode: +6e/4 +72/4 +7c/4 |
| `bfree` `8000305e` | buf: +46/1 |
| `bmap` `800030ca` | inode: +32/4 +5a/4 ; buf: +a6/4 |
| `ialloc` `800031e2` | buf: +94/2 |
| `iupdate` `8000329e` | buf: +36/2 +3e/2 +46/2 +4e/2 +54/4 |
| `idup` `8000331c` | **racy: +1c/4** |
| `ilock` `80003352` | inode: +60/2 +68/2 +70/2 +78/2 +7e/4 +96/4 |
| `itrunc` `80003440` | inode: +2c/4 +38/4 +8c/4 |
| `iput` `800034d4` | **racy: +22/4 +8a/4** ; inode: +70/4 ; buf: +b6/2 |
| `stati` `800036fe` | stack-esc: +a/4 +e/4 +14/2 +1c/2 +24/8 |
| `writei` `8000381e` | inode: +c4/4 |
| `dirlookup` `8000393a` | stack-esc: +c0/4 |
| `namex` `80003a2a` | stack-esc: +13c/1 |
| `write_head` `80003c70` | buf: +26/4 +3c/4 |
| `initlog` `80003d9a` | log: +2c/4 +30/4 +3c/4 +54/4 +6c/4 |
| `begin_op` `80003e1c` | log: +70/4 |
| `end_op` `80003ea8` | log: +20/4 +34/4 +50/4 +58/4 +112/4 |
| `log_write` `80003fca` | log: +64/4 +78/4 +a8/4 |
| `initsleeplock` `80004102` | sleeplk: +1e/8 +22/4 +26/4 |
| `acquiresleep` `80004138` | sleeplk: +38/4 +40/4 |
| `releasesleep` `8000418c` | sleeplk: +18/4 +1c/4 |
| `filealloc` `80004232` | file: +44/4 |
| `filedup` `80004290` | file: +20/4 |
| `fileclose` `800042d6` | file: +20/4 +40/4 +44/4 |
| `fileread` `800043fe` | file: +52/4 |
| `filewrite` `800044cc` | file: +b8/4 |
| `pipealloc` `8000460a` | stack-esc: +10/8 +14/8 +1c/8 +24/8 ; fresh: +38/4 +3c/4 +40/4 +44/4 +56/4 +5c/1 +62/1 +68/8 +70/4 +78/1 +80/1 +88/8 |
| `pipeclose` `800046d2` | pipe: +18/4 +42/4 |
| `pipewrite` `80004730` | pipe: +ca/4 +d8/1 |
| `piperead` `8000484c` | pipe: +c8/4 |
| `kexec` `80004970` | stack-esc: +254/8 +272/8 ; trapframe: +2a0/8 +2f0/8 +2f6/8 ; proc: +2e0/8 +2e4/8 |
| `argfd` `80004cca` | stack-esc: +3c/4 +44/8 |
| `fdalloc` `80004d24` | proc: +3c/8 |
| `create` `80004d64` | inode: +b4/2 +b8/2 +be/2 +13a/2 +146/2 |
| `sys_close` `80004fa4` | proc: +2c/8 |
| `sys_link` `80005022` | inode: +60/2 +100/2 |
| `sys_unlink` `80005146` | inode: +c4/2 +14c/2 |
| `sys_open` `800052c6` | file: +80/4 +84/4 +88/8 +98/1 +a4/1 +140/4 +148/2 |
| `sys_chdir` `800054c4` | proc: +54/8 |
| `sys_chroot` `80005544` | proc: +54/8 |
| `sys_exec` `800055c4` | stack-esc: +76/8 +c2/8 |
| `sys_pipe` `800056d0` | proc: +8c/8 +9c/8 +c4/8 |
| `plicinit` `8000581e` | mmio: +e/4 +10/4 +12/4 |
| `plicinithart` `8000583a` | mmio: +1c/4 +2a/4 |
| `plic_complete` `80005890` | mmio: +1a/4 |
| `free_desc` `800058b6` | devread: +2e/8 +36/4 +3a/2 +3e/2 ; driver: +46/1 |
| `virtio_disk_init` `8000592c` | mmio: +66 +6c +70 +86 +8a +a0 +116 +11a +120 +12e +134 +13e +144 +14a +170 (all /4) ; boot: +ca/8 +d0/8 +d8/8 +14c +150 +154 +158 +15c +160 +164 +168 (/1) |
| `virtio_disk_rw` `80005af4` | driver: +4a/1 +14c/1 +172/8 +1e8/8 ; stack-esc: +4e/4 +76/4 ; devread: +e2/4 +e4/4 +e8/8 +f6/8 +100/4 +106/2 +10e/2 +11a/8 +128/4 +134/2 +13c/2 +15a/8 +162/4 +166/2 +16a/2 +182/2 +192ᵂ/2 ; buf: +16e/4 ; mmio: +19eᵂ/4 |
| `virtio_disk_intr` `80005d28` | mmio: +2a/4 ; buf: +6aᵂ/4 ; driver: +7c/2 |
| `_trampoline` `80006000` | trapframe: 31 × /8 (`+c`…`+72`, `+7a`: user registers into `p->trapframe`) |
