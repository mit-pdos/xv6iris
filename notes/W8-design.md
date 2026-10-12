# W8-design: W8's export, how it is fed, and where it reaches a root (read-only spike, 2026-10-11)

Item: plan rev 27 §C "W8-design" (`notes/weak-allocproc-plan.md:2247-2279`), deliverables (1)–(5), D24 (`:3047-3054`),
[OWN.36] (lane W-COH ✓ → W-DMA0 ✓ → W8 ledger → M1 → W-RSV), [R23.1] (class (i) has a DYNAMIC owner), with review
R24's suggestions folded in (`notes/weak-allocproc-plan-review-R24.md`): [R24.s1] (only the static part of (i) can split
off), [R24.s2] (three buckets), [R24.s3] (test (f3′) before (f2)), [R24.s4] (the example), [R24.s6] (the initial owner
map).  Every cite is at the tip of `../xv6iris-weak-w2`.  No Lean was edited and nothing was built.  Every option below
is FAITHFUL to RVWMO/Sail/Zifencei/PMAs unless it is marked otherwise.  The memory-model specs are SILENT on how a proof
states or feeds ownership; only option (T) in §7 changes what the published theorem assumes.

## 0. Result

1. **Export (D24), pinned in §1.**  It is a PURE per-state predicate `xv6AccessDisc σ` on `MState`, the `mmOk` idiom.
   It holds no ghost ledger, so the "existential inside `mmOk`" problem of (r1) does not arise.  It is built from three
   ingredients, all derived from `σ`:
   - **(f3′) the dynamic owner.**  Proc `j`'s owner at time `t` is the hart `h` whose `cpus[h].proc` word equals
     `&proc[j]` at `t`.
   - **The lock holder.**  It is the alternation fold over the lock word's history.  Byte values alone are enough,
     because TsoMem does not record the exclusive bit.
   - **The static carves.**  `stack0`/`cpus` per hart (`Xv6/BootCarveHart.lean:81,84`).

   The predicate's W11-facing core is **(iii+) `chainOkAt`**: every foreign HART entry that a hart has observed (its
   foreign-source `coh` stamp, `MachCSL/TsoMem.lean:354-356`, reset at own stores `:361-363`) is SYNC-CHAINED to that
   hart.  A sync chain is a release by the author after the entry, followed by lock hand-offs, ending in an acquire by
   the observer.  This one clause covers (i) static and dynamic, (ii) and (iii) for every cross-hart rf edge into a
   read.  The plan's (iii) follows from it as a corollary, and the [R23.1] "third shape" is its single-lock instance.
2. **Ledger file/lane.**  The ledger is ghost-only, in `memModelAt` (`MachCSL/Resources.lean:951-956`) and in the
   context layer.  `MState` and `Lang.lean` are unchanged, so W4's `SimRel` and W2a's `rmem`
   (`Weak/PfStepTsoMem.lean:57-71`) are untouched.  The lane is serial MachCSL, before W-RSV, as ruled; the overlap is
   `Resources.lean`, the load rules and `WpLock.lean`.
3. **(β) covers almost nothing.**  A ledger-free and feed-free export covers only what `mmOk` already says.  A small
   MachCSL "reserved-region" change, with no ledger, covers `PPerCpu` (3 sites) and the lock layer's own words
   (`lk->locked`, `lk->cpu`; what [W13c] needs).  It does **NOT** cover `stack0`, so [R24.s1]'s "static part
   (`PPerCpu` + `stack0`)" does not split off.  `stack0` is written through generic rules inside the shared proofs of
   the BOOT and BOTH buckets (§2, §4).  (iii) is not β-coverable either.
4. **Feeding (the deciding finding).**  **No (f2) and no (f3) feed exists for any class except the lock-layer words and
   `cpus[h]`.**  Custody is invisible to the memory rules:
   - `wp_s_sd` takes a bare `wordPointsTo … (DFrac.own 1)` plus `kctxL` (`MachCSL/WpSmodeRules.lean:369-378`).
   - The points-to is a context-free history points-to plus a key (`MachCSL/Ctx.lean:430-432`).
   - `stackOwn` is address-only cells (`MachCSL/KCtx.lean:256-257`).
   - `KCtx` has no stack↔proc link (`:620-642`).
   - Lock payloads are opaque `R : CtxId → IProp` (`MachCSL/Lock.lean:357`) and are moved to the holder's own context
     at acquire (`:369-384`).
   - The context layer's clean keys are TSO-sound only: `ctx_absorb` (`MachCSL/CtxLaws.lean:479-480`) and
     `ctxStamped_raise` (`:577`).

   (f3′) works as an EXPORT form but not as a FEED (§3.2).  The (f2) doors `procHeld`/`stackOwn`/`swtch` are counted in
   §3.3 and are not sufficient.  The only generic candidate is a NEW option, **(f2-ctx) "chain-carrying contexts"**:
   L–XL and **unverified**, touching 11 MachCSL files and 19 `Xv6/` files that use the TSO-leaky laws.  Otherwise the
   feed is **(f1)**: ≈ 2.15k load/store rule applications in 309 `Xv6/` files, plus spec changes for every function
   that takes a buffer.  That is XL.  **By the plan's rule (`:2292-2294`, D24) this RE-OPENS [OWN.36]**, giving owner
   question Q-W8-feed in §7.
5. **Root.**  (r1) is not available.  The predicate is xv6-specific (lock registry, proc/kstack addresses), so it
   cannot enter MachCSL's generic `mmOk`.  An existential registry inside `mmOk` would let the chain run through a
   non-lock word (§5).  Changing `xv6TracePure`'s text (`Xv6/SystemSlot.lean:135-136`) contradicts the [OWN.9]
   precedent.  So the root is **(r2)**: a sibling root `Xv6.xv6DiscAdequacy_closed` (name free) on the W3 pattern.
   The cost is at most the W3 twins (1,795 lines, §5) plus `roots.txt`/`baseline.json`/`tcb` entries, and is likely
   lower, because no PowerOn hook is needed (**unverified**).
6. **Sizes** (§6):

   | Option | Size | Scope |
   |---|---|---|
   | W8-β′ | M | ≈ 0.8–1.5k lines |
   | W8 under (f2-ctx) | L–XL | ≈ 5–8.5k lines, 2–4 full-cone rebuilds |
   | W8 under (f1) | XL | ≈ 10–15k lines, ≥ 320 files |
   | (T) trusted premise | S | weaker |

7. **New finding for W11/W13 (K): the plan's (iii) is FALSE at `holding+0x12`.**  `acquire` calls `holding` (call
   graph in §2).  A NON-holder therefore reads `lk->cpu` (`Weak/KernelPins.lean:255`, `PResidue`), and that write is
   the holder's PLAIN, still-unpublished `sd`.  The read stamps the reader's foreign-source `coh` (TsoMem.lean:354-356),
   which is a `violationHart` instance (`Weak/WeakRobust.lean:100-107`).  The export therefore exempts lock-layer bytes
   from (iii+) and covers them by `lockWordDiscAt` instead.  [W13c]'s "(ii) covers `lk->cpu` under ITS OWN lock"
   (`plan :2299-2301`) does not hold for this non-holder read.

## 1. The export statement (Lean-ready; `Xv6/AccessDiscipline.lean`, names grep-checked free)

```lean
/- Xv6/AccessDiscipline.lean — W8's export (pure, per reachable MachCSL state). -/
import Xv6.ProcGeom
import MachCSL.KCtx
namespace Xv6.AccessDiscipline
open MachCSL

/-! ## σ-derived reads "as of just before timestamp t" (histories are latest-first, TsoMem.lean:78-80) -/

/-- The byte at `a` as of just before `t`: the latest entry with `e.t < t`. -/
def byteBefore (σ : MState) (a : PAddr) (t : Nat) : Option (BitVec 8) :=
  (σ.mem[a]?).bind fun H => (H.find? fun e => decide (e.t < t)).map HEnt.v

/-- The little-endian `n`-byte word at `pa` as of just before `t`. -/
def wordBefore (σ : MState) (pa : PAddr) (n : Nat) (t : Nat) : Option (BitVec (8 * n))
  -- assemble `byteBefore σ (pa + j) t`, j < n (as `FlatMem.readBytes`, TsoMem.lean:177)

/-- (f3′) [R24.s3]: the hart running proc `j` at `t` — `cpus[h].proc = &proc[j]`
(`aCpuProc`, KCtx.lean:526; `procAddr`, Xv6/ProcGeom.lean:46).  At most one hart by `cpuProcDiscAt`. -/
def kOwnerAt [KernelGeom] (σ : MState) (j : Nat) (t : Nat) : Option CPU :=
  (List.finRange NCPU).find? fun h => wordBefore σ (aCpuProc h) 8 t = some (procAddr j)

/-- One step of the lock-word alternation (mirror of `altStep`, Weak/WeakGhost.lean:570, on byte values:
from FREE a nonzero write installs its author; from HELD a zero write frees, a nonzero one — a spinner's failed
AMO, `wordPin` Lock.lean:49-51 — changes nothing). -/
def lkStep : Option CPU → HEnt → Option CPU
  | none,   e => if h : e.tid < NCPU then (if e.v = 0 then none else some ⟨e.tid, h⟩) else none
  | some c, e => if e.v = 0 then none else some c

/-- The holder of the lock whose word's low byte is `b`, as of just before `t`. -/
def lkHolderAt (σ : MState) (b : PAddr) (t : Nat) : Option CPU :=
  (((σ.mem[b]?).getD []).reverse.filter fun e => decide (e.t ≠ 0 ∧ e.t < t)).foldl lkStep none

/-! ## The custody map (xv6-specific, σ-derived; static carves from the image) -/

/-- The custody classes. `proc j` is process-owned memory that migrates with the process: `kstack_j`,
proc `j`'s trapframe page and `p->context`, its user pages — owner `kOwnerAt`, and `p_j->lock`'s holder
while `j` is not running (fork's `uvmcopy`/trapframe copy run under `np->lock`). -/
inductive Cust where
  | hart  (h : CPU)        -- stack0_h (bhStackLo), cpus[h] (bhCpuLo): BootCarveHart.lean:81,84
  | proc  (j : Nat)        -- dynamic owner [R23.1]
  | prot  (b : PAddr)      -- protected by the lock word at b (registered bytes, W9b table)
  | lockw (b : PAddr)      -- the lock layer's own words: lk->locked, lk->cpu (Lock.lean:1-30, :590-597)
  | ro                     -- read-only after boot publication (text: W3; rodata; boot-published globals)
  | free                   -- no W8 claim
  deriving DecidableEq

/-- The lock words at `σ` (static image locks + sleeplocks' inner spinlocks + pipe locks reachable from the
open-file table — σ-readable). -/
def xv6LockWord (σ : MState) (b : PAddr) (t : Nat) : Prop
/-- Custody of byte `a` as of `t` (kstack pages read off the kernel page table's KSTACK(j) leaves,
`kstackVa` Xv6/SpecProcinit.lean:66; trapframe/user pages off proc j's fields and page table). -/
def custAt [KernelGeom] (σ : MState) (a : PAddr) (t : Nat) : Cust

/-- The end of the boot era: the timestamp of hart 0's release store to `started`
(`KernelSyms.«started» = 0x8000a400`, Xv6/KernelImage.lean:17915); `σ.top + 1` if none yet. -/
def bootEnd (σ : MState) : Nat

/-! ## The W11-facing core: (iii+) every observed foreign hart entry is sync-chained -/

/-- A sync path from (author `A`, entry time `t`) to hart `B` before `τ`: a non-empty sequence of hops
`(b_k, r_k, a_k)` — a zero write to lock word `b_k` by the hop's releaser at `r_k`, the fold installing the
next hart at the acquire write `a_k` — with `t < r_0`, the releaser of hop 0 = `A`, the releaser of hop k+1 =
the acquirer of hop k (`a_k < r_{k+1}`), the last acquirer = `B`, last `a_k < τ`; OR the boot hop: `A = 0`,
`t ≤ bootEnd σ`, and `B`'s acquire load of `started` saw it (σ: `B`'s coh/rv at `started`). -/
def syncPath (σ : MState) (A : CPU) (t : Nat) (B : CPU) (τ : Nat) : Prop

/-- (iii+): hart `j`'s foreign-source coherence stamp at `a` (TsoMem.lean:354-356; reset to 0 at own stores,
:361-363) names an entry that is sync-chained to `j`.  DMA authors are exempt (`e.tid < NCPU`, mirroring
`violationHart`, Weak/WeakRobust.lean:100-107); lock-layer bytes are exempt (§0 item 7; `lockWordDiscAt`). -/
def chainOkAt [KernelGeom] (σ : MState) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
    e.t = (σ.hr j).coh a → (hA : e.tid < NCPU) → e.tid ≠ hartAgent j →
    (∀ b, custAt σ a e.t ≠ .lockw b) →
    syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1)

/-! ## The lock layer (the plan's (ii) lock part: wlpAt / wlpAlt / lk->cpu) -/

/-- Every post-registration write to a lock word is a whole-word 0 or 1, a 0 only by the current holder
(`lockWordAt`, Lock.lean:53-56); every `lk->cpu` entry is 0 or the writer's own `&cpus[w]`, written by the
holder (`lkCpuAt`, Lock.lean:18-22). -/
def lockWordDiscAt [KernelGeom] (σ : MState) : Prop

/-- `PPerCpu` (β′): `cpus[h]`'s bytes are written only by `h` after power-on. -/
def cpuStaticAt [KernelGeom] (σ : MState) : Prop :=
  ∀ (h : CPU) (a : PAddr) (H : Hist) (e : HEnt), custAt σ a e.t = .hart h → σ.mem[a]? = some H →
    e ∈ H → e.t ≠ 0 → e.tid = hartAgent h

/-- `c->proc` moves only under the target proc's lock: `:= &proc[j]` while `h` holds `p_j->lock`,
`:= 0` while `h` holds the lock of the proc it named (Xv6/SpecScheduler.lean:11,13). -/
def cpuProcDiscAt [KernelGeom] (σ : MState) : Prop

/-- (v) user text (W5d-G G7): entries on proc `j`'s executable user pages precede its owner's
last `fence.i` (`σ.itv`). -/
def utextDiscAt [KernelGeom] (σ : MState) : Prop

/-- **W8's export.** -/
def xv6AccessDisc [KernelGeom] (σ : MState) : Prop :=
  chainOkAt σ ∧ lockWordDiscAt σ ∧ cpuStaticAt σ ∧ cpuProcDiscAt σ ∧ utextDiscAt σ

end Xv6.AccessDiscipline
```

**The root ((r2), §5), mirroring `xv6TextAdequacy_closed` (`Xv6/LinkTextAdequacy.lean:26-31`):**

```lean
theorem xv6DiscAdequacy_closed {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m)
```

**How each consumer reads it.**

- **W11 (i) `badSeg`.**  `badSeg` is "the source message is WCplain and unpublished at the log by a foreign hart"
  (`plan :2311-2314`).  It is refuted at the realizing TsoMem run.  At the post-state of the read, `coh j a` equals
  the read's foreign source.  The read moves the floor only up (`cohOk`), so the latest visible entry is at or above
  the old stamp.  `chainOkAt` then gives a release by the author after the entry, and that store is WCrel on the pf
  log.  Fixing it there needs the static release-site fact (`fence rw,w; sw`, W9a), and `R`'s log identification
  carries it.
- **W11 (ii) `protReg`.**  `wlpAt`/`wlpAlt` (`Weak/WeakGhost.lean:543-545, 699-701`) are read off `lockWordDiscAt`
  through `rhist`.  `wprotAt` (`:1040-1044`) is needed only for the registered bytes that W11 still kills with
  `csHyps`.  The cross-hart kill into process-stack reads uses a NEW `chainHyps` arm instead: a `csChained`
  generalised to `syncPath` hops (`Weak/WeakRvwmoGlue.lean:424-437`).  This is the [R23.1] "third shape";
  `csHyps`' `wprotAt` side condition (`:421-422`) is false for stack bytes, because they are written WITHOUT
  `p->lock`.
- **(iv)** is a STATIC table, not a σ-clause.  The 182 `PCall`/`PResidue` sites and the 58 `own` witnesses are
  classed as chained / lock-layer / ro / audited-racy (W9b), and `KernelPins.lean`'s `--check` is the audit.
- **(v)** is `utextDiscAt`.

**[R24.s4] example**, checkable against the table:

1. Hart A runs P.  `sched`'s prologue pushes `ra`/`s0`–`s2` on `p->kstack`.
2. `swtch` takes A into its scheduler, which runs `c->proc = 0; release(&p->lock)` (SpecScheduler.lean:13-15).
3. Hart B runs `acquire(&p->lock)`, sets `c->proc = p` (`:11`), and `swtch`es into P.
4. `sched+0x7e..+0x86` (`KernelPins.lean:549-553`) LOAD the words A pushed.  This is the cross-hart rf edge into a
   `PStack` read.  `chainOkAt` gives the single hop: A's zero write to `p_j->lock`, then B's acquire write.
   `cpuProcDiscAt` pins `kOwnerAt` to A before the hop and to B after it.
5. The same shape occurs at `kernelvec+0x28..` (`:1671-1673`) after a `yield` from `kerneltrap`.

**[R24.s6] initial owner map.**

- `stack0_h`: owned by `h` from power-on, through the per-hart carve (BootCarveHart.lean:81).
- `cpus[h]`: owned by `h` from power-on (`:84`).
- `kstack_j`: `kOwnerAt` is `none` until the first `c->proc := &proc[j]`.  Its boot-era writes are by hart 0, from
  `proc_mapstacks` → `kalloc`/`kfree` junk fills.  Other harts reach them only through the `started` hop
  (`e.t ≤ bootEnd σ`) of `syncPath`.

## 2. The 1,034 `PStack` sites in three buckets [R24.s2]

**Method.**

1. Function starts were collected from the image dump.  Sources: the `<fn+0xoff>` references in the objdump comments
   of `Xv6/KernelImage.lean`, the `KernelSyms` table (`:17702-`), and the pin table's own `-- fn+off` comments.
2. The call graph comes from every `jal`/`j <fn>` target.  The indirect transfers were resolved by hand:
   - `uservec+0x9a jalr t0` → `usertrap`;
   - `syscall jalr a4` → every `sys_*`;
   - `fileread`/`filewrite jalr a5` → `consoleread`/`consolewrite` (devsw);
   - `uartintr jalr a5` → `consoleintr` (the rx callback);
   - `forkret`'s `jalr` → `userret`;
   - `argraw jr a5` is a switch table;
   - `start` → `main` is by `mret`.
3. Roots:
   - BOOT: `_entry`, `start`, `main`, `scheduler`.
   - PROC: `usertrap`, `forkret`.
   - INTR: `kernelvec`.  It counts as BOTH, because `scheduler` enables interrupts on `stack0`
     (SpecScheduler.lean:6), and process context enables them on `p->kstack`.
4. A function reached only from BOOT is BOOT; only from PROC is PROC; from both, or from INTR, is BOTH.  The pin
   entries were counted per `-- fn+off` comment.  The script lives in the session scratchpad; it is reproducible
   from these rules.

**Buckets.**

| bucket | fns | sites | functions (sites) |
|---|---|---|---|
| **BOOT** (`stack0` only: static) | 26 | **82** | proc_mapstacks 10, procinit 8, freerange 6, binit 6, iinit 5, virtio_disk_init 4, initsleeplock 4, userinit 3, kvmmake 3, uartinitone/uartinit/trapinithart/trapinit/timerinit/start/printkinit/plicinithart/plicinit/kvmmap/kvminithart/kvminit/kinit/igetroot/fileinit/consoleinit 2 each, _entry 1 |
| **PROC** (`p->kstack` only: dynamic) | 115 | **747** | kexec 31, pipewrite 27, sys_exec 23, readi 23, consolewrite 21, writei 18, filewrite/balloc 17, uvmalloc/fileread/fileclose/dirlookup 15, vmfault/ialloc 14, copyout/consoleread 13, … (full list reproducible) |
| **BOTH** (handled as dynamic) | 41 | **192** | printk 22, kernelvec 17, mappages 9, consoleintr 9, walk 8, uvmunmap 8, wakeup 7, uartputc_sync 7, iget 6, sched 5, kerneltrap 5, freewalk 5, proc_pagetable/proc_freepagetable/printint/kfree/devintr/allocproc 4, yield 3, virtio_disk_intr 3, uvmfree/uvmcreate/uartintr/release/push_off/plic_complete/myproc/kalloc/idup/holding/freeproc/acquire 3, prputc/pop_off/plic_claim/mycpu/memset/initlock/cpuid/consputc/clockintr 2 |
| **DEAD** (never called in this image) | 3 | **13** | procdump 9, memcpy 2, memcmp 2: no `jal`/`j` target anywhere |

Total 82 + 747 + 192 + 13 = 1,034, matching the census line `KernelPins.lean:23`.

**Refinement (a guard, not a graph fact).**  `yield` (3 sites) and `sched` (5) are reached from the BOTH function
`kerneltrap` only when `myproc() != 0`, that is, in process context.  With that refinement PROC = 755 and BOTH = 184.

**`allocproc` is BOTH.**  It is called by `userinit` on hart 0's `stack0` and by `kfork` on the caller's
`p->kstack`.  This confirms the plan's "the target runs on both".

**Related counts.**

- The 58 `own = true` witnesses are the store-side dual: PROC 46, BOTH 11 (printk 10, freeproc 1), DEAD 1 (procdump).
- `PPerCpu` has 3 sites: `myproc+0x1e`, `sched+0x2a`, `sched+0x54` (`:476,546,548`).  All three are static
  (`cpus[tp]`), whatever bucket their function is in.

**Consequence.**  Only the 82 BOOT sites plus `PPerCpu` are static.  The 192 BOTH sites are static when the hart runs
on `stack0` and dynamic when it runs on `p->kstack`, and their proofs are shared.  So a static-only feed cannot
cover them.

## 3. Feeding (deliverable (4))

### 3.1 Why no class is generically re-establishable: the rules never see custody

A memory rule's whole input is the instruction, the hart's `kctxL`, `pcIs`, and a bare cell `wordPointsTo a n (own 1) w`
(`wp_s_sd`, `MachCSL/WpSmodeRules.lean:369-378`; `wp_s_ld :334`).  That cell is the context-free gen_heap history
points-to `a ↦ₕ{dq} (e :: H)` plus a key at the ambient context (`ctxByte`, `MachCSL/Ctx.lean:430-432`).  None of
these says WHO is entitled to the byte:

- **Stacks.**  `stackOwn` is a list of plain cells under `sp` (`KCtx.lean:256-257`).  `KCtx` records `proc` but has no
  stack↔proc link (`:620-642`).  When the cells are lent to a callee (`memmove`/`copyin`/`argint` into a caller's
  frame), the callee sees only `wordPointsTo`.
- **Lock-protected bytes.**  The payload is an opaque `R : CtxId → IProp` (`Lock.lean:357`), moved to the WINNER'S own
  context at acquire (`lock_pay_take :369-384`, via `ctx_move`, a `CtxMorph`, `CtxLaws.lean:54`).  At a store, a
  `proc[3].state` cell is indistinguishable from an owned one.
- **Contexts are not a custody substitute.**  The running context's bound rises to ANY view receipt of its hart
  (`ctx_absorb`, `CtxLaws.lean:479-480`, used by `acquire` at the AMO's whole-log position, `WpLock.lean:1141,1345`).
  A stamped context's bound rises to any store-order receipt (`ctxStamped_raise :577`, the lock hook
  `Lock.lean:400-438`).  A CLEAN key therefore records "some acquire happened since", not "synchronised with the
  writer".  That is sound for TSO and not for RVWMO; the SpecAcquire note `Xv6/SpecAcquire.lean:96-103` says so
  explicitly.

So a predicate such as "writer = custodian" cannot be re-established by a memory rule.  That is true even for the
static `stack0_h`, whose writers include every BOOT/BOTH function using the generic `wp_s_sd`.  The fact can only be
supplied where custody is known.

### 3.2 (f3′) — TESTED [R24.s3]: a valid EXPORT form, not a FEED

**It is well-defined from σ.**

- `c->proc = p` is written AFTER `acquire(&p->lock)`, and `c->proc = 0` BEFORE `release`, both under the lock
  (SpecScheduler.lean:9-15).  So at most one hart names `&proc[j]` at any log time.  The order is A: `c->proc := 0` <
  A: release < B: acquire-write < B: `c->proc := p`, because a hart's stores enter the log in program order
  (`MState.store` appends at `top+1`, Lang.lean:151-156).
- The boot-era exemption is σ-definable (`bootEnd`).
- So `kOwnerAt` and `cpuProcDiscAt` (§1) are sound export clauses.  The writer-is-owner fact they encode is true for
  xv6:
  - no hop on a slot's lifetime writes `kstack_j` bytes (R24 `:46-48`);
  - `kstack` pages are never freed (`Xv6/SpecProcinit.lean:11`).

**It is not re-establishable without feeding.**  A store by hart `h` into `kstack_j` must show
`kOwnerAt σ j = h`.  For that, the rule would need "the writer holds a `kstack_j` cell ⇒ `c->proc = &proc[j]`".  No
authority states this: `cpuCells` ties `c->proc` to `k.proc` (`KCtx.lean:556-560`), but nothing ties `k.proc` to the
cell's address, and the lent-cell case reaches functions whose specs know nothing about stacks.

**Verdict.**  (f3′) fixes the export's vocabulary.  The (f3) feed fails for both the dynamic AND the static stacks.

### 3.3 (f2) at the named doors — counted, and not sufficient alone

| door | definition | `Xv6/` uses (files) | `MachCSL/` uses (files) |
|---|---|---|---|
| `procHeld` | abbrev `Xv6/SchedCtx.lean:1590` of `procHeldAt :663-668` (`locked (Γ.lock j) h ∗ pstateWhole ∗ procPub ∗ zsElem`) | 50 (13); `procHeldAt` 30 (5) | 0 |
| `stackOwn` | `KCtx.lean:256` | 273 (93); `stack_cells` 125 (69) | 58 (16); `stack_cells` 38 (9) |
| `swtch` payload | `wp_swtch_body`, `Xv6/SpecSwtch.lean:35-58`; `swtch_loads`' `stackOwn` IN/OUT, `Xv6/ProofSwtch.lean:140,142` | `wp_swtch` 3 (3); `wp_s_ld_sp` 2 (1) | `wp_s_ld_sp` 1 (1) |
| lock layer | `wp_acquire`/`wp_release`/`wp_initlock`; `locked`; `lkFresh` (birth, `Lock.lean:727`) | 39 (36) / 35 (33) / 14 (14); 422 (129); 72 (29) | `WpLock.lean` 2,625 lines, `Lock.lean` 830 |

**Why wrapping these doors does not feed (i)/(ii).**  Once a protected or owned cell leaves its wrapper (`procHeld`
destructured, `stack_cells` opened), it is used through the generic rules: 634 `wp_s_sd`, 839 `wp_s_ld`, … in `Xv6/`.
A wrapper type that survived to the rule would force a wrapped rule variant at every such application.  That is
(f1).

**What does feed from the lock layer.**  The lock's OWN words are a different case.  `lk->locked` and `lk->cpu` live
in the lock invariant as `wordCell`s with `lockWordAt`/`lkCpuAt` already proved per lock (`Lock.lean:590-597`), and
are touched only by WpLock's own rules.  So `lockWordDiscAt` is (f2)-feedable.

### 3.4 (f2-ctx) — NEW: chain-carrying contexts (the only generic candidate; L–XL, **unverified**)

**The change.**  Refine the CLEAN key so that it carries a sync chain: keep the per-context invariant "every
foreign-HART entry `t ≤ bound ξ` has a `syncPath` to ξ's hart".

**It is maintained at the context laws:**

- `ctx_unstamp` (`CtxLaws.lean:552`): concatenate the releaser's chains with its release → acquire hop.
- `ctx_move` (`:848`, domination): chains are inherited.
- `ctx_park`/`ctx_resume` (`:760,788`, swtch): the `p_j->lock` hop, supplied at the 3 `wp_swtch` sites.

**It requires these restrictions:**

- `ctx_stamp` (`:520`) stamps at `max bound dirty`, not at the arbitrary top receipt `W`.
- `ctx_absorb` only at chained receipts: in `acquire` that means the release stamp `T`, not the AMO position `t`
  (`WpLock.lean:1141-1143` already derives `T ≤ t`).
- `ctxStamped_raise`/`lockHook_llb` only at chained receipts.
- DMA-authored keys get their own "device key" arm, exempt from chains.

**What it buys.**  A load rule can then establish `chainOkAt` at its post-state GENERICALLY, from the key it already
consumes.  It needs no custody and no `Xv6/` site feed at loads or stores.  Thread migration (dirty keys authored on
A must be justified on B at resume) and lock transfers are both covered by the hops.

**Files.**

- MachCSL, 11 files (8,477 lines): `Ctx.lean`, `CtxLaws.lean`, `Lock.lean`, `WpLock.lean`, `SwtchCtx.lean`,
  `KCtxMove.lean`, `CtxBox.lean`, `LockBornHook.lean`, `WpDma.lean`, `WpDmaCtx.lean`, `WpSmodeLwKey.lean`.  These are
  `CtxLaws.lean` plus the 10 files that use the transport/leaky laws.  Add the load rules' internals.
- `Xv6/`, 19 files (15,496 lines) that use the laws directly: `IcacheTable`, `IputLockedB`, `ProofScheduler`,
  `IcacheBootTable`, `IcacheInvRef`, `BcacheInv`, `SleepLockDefs`, `ProofForkretPark`, `ProofIdup`, `SpecAcquire`,
  `ForkretRecord`, `ProofBrelse`, `IgetScan`, `BcacheLock`, `ProofIunlock`, `SpecReleasesleep`, `DiskInvDefs`,
  `SpecRelease`, `ProofVirtioDiskIntr`.  Of these:
  - `ctx_absorb` 6 uses (3 files), `ownCtx_floor_view` 8 (4), `ctxStamped_raise` 5 (2), `lockHook_llb` 13 (10),
    `ownCtx_key_vis` 3 (2);
  - transports `ctx_unstamp` 1, `ctx_park` 3, `ctx_move` 5, `lock_pay_*` 3.
- Up to 43 more files use `ctxFloor` (108 uses), whose meaning would change.

**Risk R-ctx (the gate).**  The TSO-leaky uses are DESIGNED to mint floors above the releaser's own view:
`SpecRelease.lean:164-169` ("a payload row `ctxFloor ξ tl` ABOVE the releaser's own view … how the buffer cache's
lock payload carries the floor its next holder needs"), `BcacheLock.lean:132`, `SpecAcquire.lean:96-103` ("any
store-order receipt the caller held BEFORE the call … cash into `ctxFloor curCtx tl`").  Each must be re-justified by
a chain or by the device-key arm:

- the bcache/icache/sleeplock floors;
- the virtio completion floors in `DiskInvDefs`/`ProofVirtioDiskIntr`.

Whether every one can be re-justified is **unverified**.  If any needs a cross-lock fact the TSO proof never tracked,
that part of (f2-ctx) falls back to (f1).

### 3.5 (f1) — per-site custody feed (XL; re-opens [OWN.36])

**What gets edited.**

- Every store application in `Xv6/` must justify `custAt` = writer: `wp_s_sd` 634, `wp_s_sw` 118, `wp_s_sb` 42,
  `wp_s_sh` 34, plus ≈ 60 specialised (`_au`, `_mint`, `_proc`, `_noff`, `_intena`, `_zero_release*`, …).
- Every load at the 1,219 unpinned sites (1,034 + 3 + 182) must do the same: `wp_s_ld` 839, `wp_s_lw` 245, `wp_s_lbu`
  50, `wp_s_lh` 40, `wp_s_lhu` 21, `wp_s_lwu` 3.
- In total ≈ **2,153** applications of the plain load/store rules in **309** `Xv6/` files.  Add the M-mode and
  user-cycle rules.

**New reasoning.**

- A `KCtx` stack-region link, carried through `procinit`, `allocproc`, `scheduler`, `sched`, `swtch`, `forkret`,
  `kernelvec`, and the `uservec` sp loads.
- Page custody at `kalloc`/`kfree`/`uvm*`/`pipe*`/`exec`.
- Payload footprints for the 12 spinlock classes (`"kmem"`, `"proc"`, `"itable"`, `"pr"`, `"ftable"`, `"cons"`,
  `"pipe"`, `"nextpid"`, `"bcache"`, `"log"`, `"time"`, `"virtio_disk"`, as counted from `k.locks` side conditions)
  plus the sleeplocks.
- Spec changes for every buffer-taking function, because a lent stack cell's custody must cross the call.

**Cost.**  It is not "one rebuild".  By the plan's rule (`:2292-2294`), this is the XL outcome that RE-OPENS the lane
decision.

## 4. (β) — what a ledger-free export covers (deliverable (3), [R24.s1])

- **Strictly ledger-free and feed-free.**  Nothing beyond what `mmOk` already states (`Resources.lean:779-785`).  No
  writer of any byte is recorded anywhere a root can read.
- **β′: no ledger, with a small MachCSL "reserved region" change.**  The state interpretation holds half of each
  reserved byte's points-to.  A generic rule's own-1 cell then cannot name a reserved byte, because gen_heap validity
  forbids it.  Reserved bytes are written only by dedicated rules whose custody is structural.  This covers two things:
  - `cpus[h]`.  Its cells sit in `kctx cpu`'s `cpuCells cpu` (`KCtx.lean:556-560`), and its stores already go through
    dedicated rules (`wp_s_sd_proc` 3, `wp_s_sw_noff_lend` 2, `wp_s_sw_intena` 2, `wp_s_lw_noff` 4).  This yields
    `cpuStaticAt` and the 3 `PPerCpu` sites.
  - The lock layer's words, registered at lock birth (`lkFresh`, `Lock.lean:727`; `lock_pay_born`, `:488`) and
    released at the cancellable lock's reclaim.  This yields `lockWordDiscAt`, which W13 (K)'s `ioSegPinned`
    precondition needs ([W13c], `plan :2299-2301`).
- **Not covered: `stack0`.**  It is written by the generic rules in the BOOT bucket's 26 functions and in the 41
  BOTH-bucket functions, whose proofs are shared with `p->kstack` (§2).  Reserving `stack0` breaks those proofs.
- **Not covered: (iii)/(iii+).**  It is global and custody-dependent.
- **Consequence: W8 does NOT split as "(i)/(iii) an `Xv6/`-only parallel item".**  The split that exists is
  **W8-β′** (`cpuStaticAt` + `lockWordDiscAt`; M; MachCSL-side; serial MachCSL lane because it edits
  `Resources.lean`/`Lock.lean`/`KCtx.lean`) and **W8 proper** (`chainOkAt`, `cpuProcDiscAt`, `utextDiscAt`; fed by
  (f2-ctx) or (f1)).

## 5. Root (deliverable (5))

- **(r1) is not available as specified.**
  - `mmOk` is MachCSL-generic (`Resources.lean:779-785`), while `xv6AccessDisc` names the xv6 lock registry and the
    kstack/proc/cpus addresses.
  - A MachCSL-generic variant `∃ reg, chainOk σ reg` inside `mmOk` (text unchanged) is unusable.  W11 needs every
    registered word's zero writes to be WCrel at the release site.  An existential `reg` admits non-lock 0/1 words,
    whose zero writes are WCplain, and σ records neither class nor pc.
  - Adding a conjunct to `xv6TracePure` (`Xv6/SystemSlot.lean:135-136`) changes the root's text, against [OWN.9]'s
    precedent ("existing root statements and baseline untouched").
- **(r2) — RECOMMENDED: `Xv6.xv6DiscAdequacy_closed` (§1).**
  - It runs on the W3 pattern: `MachCSL/PowerText.lean` 734, `Xv6/BootSharedText.lean` 250,
    `Xv6/SystemBootEraText.lean` 196, `Xv6/SystemAdequacyText.lean` 580, `Xv6/LinkTextAdequacy.lean` 35, for **1,795**
    lines in total.  Add entries in `tools/ci/roots.txt` (W3's is at `:19`), `tools/audit/baseline.json` (`:63`
    pattern) and `tcb/expected.json`.
  - W8's facts sit in the state interpretation, not in a PowerOn-recorded window (`PowerText.lean:9-30`), so the twin
    likely needs only the final extraction, not the PowerOn hook.  Expected below W3's cost (**unverified**).
  - W3's 1,795 lines is the upper bound.  The registry agreement (MachCSL ghost registry ⊆ `xv6LockWord σ`) is a
    small `Xv6/` invariant inside the twin.

## 6. Sizes

| item | lines | files | rebuilds | lane |
|---|---|---|---|---|
| **W8-β′** (`cpuStaticAt`, `lockWordDiscAt`; reserved regions + lock registry) | ≈ 0.8–1.5k | ≈ 6–8 MachCSL (`Resources`, `Lock`, `WpLock`, `LockBornHook`, `KCtx`, the cpu-cell rule file) + ≤ 30 `Xv6/` (`lkFresh` 29 files if lock birth's modality changes; ≈ 11 cpu-cell rule uses) | 1 full cone (MachCSL 78k + `Xv6` ≈ 0.66M lines) | serial MachCSL |
| **W8 proper under (f2-ctx)** | ≈ 3–5k core + `AccessDiscipline.lean` ≈ 0.5–0.8k + root twin ≤ 1.8k → **≈ 5–8.5k** | 11 MachCSL + 19–62 `Xv6/` + 5 twin files | 2–4 full cone | serial MachCSL, before W-RSV (shares `Resources.lean`, the load rules, `WpLock.lean`) |
| **W8 proper under (f1)** | **≈ 10–15k** (≈ 2.15k site edits + 3–6k new custody reasoning + export/root ≈ 2.5k) | ≥ 320 | many | re-opens [OWN.36] |
| **(T)** trusted premise | S (statement + W11 plumbing) | ≈ 2–3 | 0 | any |

Plus, in every case: W11 gains a `chainHyps` kill arm (a `csChained` generalisation over `syncPath`, M,
**unverified**), and W9b's table classifies the 182 + 58 sites (as planned).

## 7. Owner question Q-W8-feed (spec-first)

**Spec.**  RVWMO, riscv.cat, Sail, Zifencei and the PMAs say nothing about how a proof states or feeds ownership.
Every form of W8's export is a fact about xv6's code and leaves the published quantifier unchanged.  What is at stake
is cost, the lane, and one assumption.

**Background.**  [OWN.36] ruled W8 serial "on the one-rebuild cost".  W8-design shows that one-rebuild feeds exist only
for the lock-layer words and `cpus[h]` (W8-β′).

**Options:**

- **(a) (f2-ctx) chain-carrying contexts.**  L–XL, generic, serial MachCSL before W-RSV, as ruled.  Gate: a
  read-only S check of the ≈ 35 TSO-leaky uses in the 19 `Xv6/` files (R-ctx, §3.4) before the worker starts.  If
  any use resists, fall back to (b) for that part.  **FAITHFUL** (proof-internal; machine and theorem unchanged).
- **(b) (f1) per-site custody.**  XL, ≥ 320 `Xv6/` files, many rebuilds.  **FAITHFUL**.
- **(c) (T) "xv6 access discipline" as a named trusted premise** of T-alloc-RVWMO (the statement `xv6AccessDisc` at
  every reachable state), audited informally by the pin table.  S.  **WEAKER** (an unproved program property in the
  trusted base, beside `ioResidueGmo`/`gzFetch`/`sailCycleOrder`).

**Recommendation.**  (a), behind its S gate, with W8-β′ landing first.  It is independent of the gate and unblocks W13
(K)'s `lk->cpu` precondition.

**Also reported (W11 text, no gate).**  §0 item 7: the plan's (iii) is false at `holding+0x12` for a non-holder
acquirer.  The export exempts lock-layer bytes.  W11's `badSeg` refutation must route `lk->cpu` reads through
`lockWordDiscAt` (the value is only compared with `mycpu()`; `lkCpu_read_not_mine`, Lock.lean:18-22), not
through (iii).

## 8. Unverified points (each marked where used)

- (f2-ctx) soundness and Xv6 fallout (R-ctx).
- The `chainHyps` arm.
- That (r2)'s twin needs no PowerOn hook.
- `custAt`'s σ-derivability for pipe locks and user pages (open-file table and page-table walks at σ).
- That `xv6LockWord` enumerates every spinlock xv6 creates.
- W8-β′'s cpu-cell rule census: ≈ 11 uses counted by rule name.  A proof that stores `c->proc`/`noff`/`intena`
  through the plain `wp_s_sd`/`wp_s_sw` would also need an edit.
