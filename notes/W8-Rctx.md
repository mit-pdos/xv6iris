# R-ctx: the read-only gate of W8 (f2-ctx) (2026-10-12)

Item: plan rev 29 §C "R-ctx" (`notes/weak-allocproc-plan.md:1210-1221`, `:2610-2624`, `:2658-2660`), [OWN.37],
`notes/W8-design.md` §3.4 (`:341-388`).  Read-only: no Lean was edited and nothing was built.  Every cite is at the
tip of `../xv6iris-weak-w3`.  The plan names the deliverable `notes/W8-Rctx.md` (`:2659`); this brief names it
`notes/R-ctx.md`, so it is written here.

What was checked: each use of a TSO-leaky context law in the 21 files.  For each one I asked whether its TSO-only
visibility step can be replaced by a release→acquire chain that the context already carries, by the device-key arm,
or by the `pte-key` arm (`pteDiscAt`).  Verdict codes:

- **CHAINED**: replaceable by a release→acquire chain the proof already moves.
- **DEVICE-KEY** / **PTE-KEY**: covered by the device-key or `pte-key` arm.
- **NEEDS-X**: the chain exists in the program, but the proof only carries it once change X is made.
- **RESISTS**: falls back to (f1).

## 0. Result

1. **F0 — the invariant R-ctx was asked to check against cannot be maintained as written.**  The invariant is "every
   foreign-HART entry `t ≤ bound ξ` has a `syncPath` to ξ's hart" (`W8-design.md:343-344`).  It already fails at
   one ordinary lock hand-off, so it fails before any `Xv6/` use is reached (counterexample in §1).  It is
   maintainable once the chain bound is per author: a vector bound, kept beside the scalar TSO bound (§1).
   **Every CHAINED/NEEDS-X verdict below is relative to that per-author bound.**  Under the scalar form as written,
   every cross-hart row RESISTS, and (f1) becomes the whole of W8.  This is a proof-internal design correction.
   FAITHFUL: the machine and the theorem are unchanged.
2. **With the per-author bound, no use RESISTS.**  For every TSO-only step there is a program-level release→acquire
   chain through a lock whose payload the proof already moves: `p->lock`, `lk->lk`, `bcache.lock`, `itable.lock`,
   `ftable.lock`, `vdisk_lock`, or the `started` boot hop.  The other cases are device-authored or PTE bytes.  But
   **five things must be added** that the TSO proof never tracked:
   - **(X1)** Every `topLb` re-floor at a hook (`lockHook_llb`, `ctxStamped_raise`) becomes a floor the releaser's
     own context already has.  This works because each such stamp is either the releaser's own store or deposit (its
     own component is free), or was chained to it through the same lock.
   - **(X2)** A new box row in `MachCSL/CtxBox.lean:1117-1121`: "every live key's stamp ≤ `max tp td`".  It covers a
     reference minted at a stamp its holder is not yet chained to (`bget`'s race with a parker, §2 row 22).
   - **(X3)** A birth key for the payload stamp of a lock born after boot, in `lkFresh`/`isLock`.
   - **(X4)** A device-only absorb for the virtio watermark.
   - **(X5)** The `ACQUIRE_LLB`/`ACQUIRESLEEP_*LLB` "cash any `topLb`" surface is withdrawn.  Its consumers re-route
     through (X1)/(X2).
3. **Count.**
   - The 21 files hold **21 code uses** of the named laws, plus **10 definitional surfaces** that expose the leak.
     The other plan/W8-design counts (`ctx_absorb` 6, `lockHook_llb` 13, …) include prose mentions.
   - **4 direct leaky sites lie OUTSIDE the 21**: `IputParts.lean:461`, `ProofAcquiresleep.lean:809` (via
     `kctx_floor_of_view`, `MachCSL/KCtxMove.lean:295-303`), and `StartedInv.lean:198,344`.
   - **31 more `Xv6/` files** consume the hook/llb surfaces (§5).
   - There is **one more post-boot lock birth**: the `"log"` lock at `ProofInitlog.lean:434`, sealed in the first
     `forkret`'s `fsinit`.  This corrects [R25.3]'s "`lock_pay_born` … the only lock born after boot"
     (`plan :1215`).
4. **The `swtch` handoff row is CHAINED, and the hop is NOT at `wp_swtch`.**  All 8 transports in
   `Xv6/ProofSwtch.lean` are same-hart moves.  The cross-hart step is the `p->lock` payload's `lock_pay_intro` →
   `lock_pay_take` (§3).  `W8-design.md:350`'s "supplied at the 3 `wp_swtch` sites" should read "at the `p->lock`
   payload hop".
5. **Walker row**:
   - Kernel table: PTE-KEY.
   - User table: CHAINED as owned stores, modulo one spec question (§4, Q-R2).
6. **Size (§6).**  W8 (f2-ctx) ≈ 6.5–9.5k lines (was ≈ 4–6.5k), across 12 MachCSL files and ≈ 52 `Xv6/` files plus
   the twin, 3–4 full-cone rebuilds.  **(f1) fallback list: empty** if F0's per-author bound is adopted.  If it is
   not, every row falls to (f1) (XL ≈ 10–15k).

## 1. F0: the scalar chain invariant fails at one hop

**Counterexample.**  The plan's restrictions are applied throughout.  Hart C stores to `y` at log position 5 and
never releases anything.  Hart A runs context ξA with bound 0, stores to `x` at 10 (a dirty key, `dirtyOk`,
`MachCSL/Ctx.lean:259-260`), and releases lock L:

1. `lock_pay_intro_hook` (`MachCSL/Lock.lean:441-460`) runs `ctx_stamp`.  It stamps ξL at `max B W`
   (`MachCSL/CtxLaws.lean:526-529`).  Even "`max bound dirty`" is ≥ 10.
2. Hart B acquires L.  Its absorb at the release stamp T, not the AMO position (`MachCSL/WpLock.lean:1141-1143`),
   and `ctx_unstamp` at T (`MachCSL/Lock.lean:375`, `CtxLaws.lean:552-568`) give B's context a bound ≥ 10.
3. C's entry at 5 is now a foreign-hart entry ≤ bound with no `syncPath` from C.  The invariant is false.

**The fix.**  The chain is per author.  A path from (h, t) is also a path from (h, t′) for every h-authored t′ < t,
so each author's chained entries form a prefix.  The faithful representation is therefore a vector bound,
`chain ξ : CPU → Nat`, joined at each hop.  Two invariants hold:

- "every h-entry `t ≤ chain ξ h`, h ≠ hart(ξ), has a `syncPath` to hart(ξ)";
- causal closure: `chain ξ h ≥ t` ⇒ `chain ξ ≥` the vector h released after t.

The cheapest form keeps the scalar TSO bound (`ctxFloor`, `Ctx.lean:179-180`) for visibility, unchanged.  It adds the
vector beside it, consulted only by clean keys (`keyAt`, `Ctx.lean:187-188`) and by the load rule that establishes
`chainOkAt`.  A per-key certificate set is the alternative.  It is equivalent but heavier.

**Consequence for this gate.**  A minted floor is "chained" iff, at the mint, the minter's vector already covers the
entries the floor will key.  §2 checks exactly that.

## 2. The per-use table (the 21 files)

`→ X` marks the change that a NEEDS-X row needs (§0 item 2).

| # | site | what the use relies on (TSO step) | verdict |
|---|---|---|---|
| 1 | `Xv6/ProofScheduler.lean:998` `ctx_unstamp` | `cpuCtxFree`'s save-area context, stamped at T = 0 at boot with `viewLb h 0` (`SchedCtx.lean:1582-1584`, minted only at `BootCarveHart.lean:310-347`).  Cells are `.bss` image bytes (t = 0) | **CHAINED** (trivially: stamp 0, same hart, image entries exempt, `e.t ≠ 0`, W8-design `:148`) |
| 2 | `ProofScheduler.lean:1000` `kctx_move_in` | same-hart `ctx_move` (`KCtxMove.lean:306-315`) | **CHAINED** (inherit) |
| 3 | `ProofForkretPark.lean:250` `ctx_move` | newborn ξc (`ctx_fresh`, bound 0, `ForkretRecord.lean:37-66`) takes the record rows on the creator's hart | **CHAINED** (inherit).  The child's cross-hart start is the `np->lock` hop (row 31) |
| 4 | `ProofForkretPark.lean:253` `ctx_park` | newborn parked under the creator, same hart (`CtxLaws.lean:760-785`) | **CHAINED** (inherit) |
| 5–9 | `ProofSwtch.lean:251,253` `kctx_move_in`; `:268,270,274` `kctx_move_out` | same-hart `ctx_move` (`KCtxMove.lean:306-327`) | **CHAINED** (inherit) — §3 |
| 10 | `ProofSwtch.lean:248` `kctx_resume_tok` (→ `ctx_resume`) | resume the target ξt from under the running context on the same cpu (`SwtchCtx.lean:280-291`) | **CHAINED** (inherit; ξt arrived through the `p->lock` hop) — §3 |
| 11 | `ProofSwtch.lean:276,293` `kctx_cross` (→ `ctx_park`) | the caller parked under the target's context, same cpu (`SwtchCtx.lean:304-316`) | **CHAINED** (inherit) — §3 |
| 12 | `PipeBirth.lean:303` `lock_pay_born` | `ownCtx_new` + `ctx_move` + `ctx_stamp` (`Lock.lean:463-500`).  The first AMO reads `initlock`'s PLAIN 0 (no release precedes it).  Under TSO the AMO's view ≥ top gives the birth stamp | **NEEDS-X → X3**: the chain exists via the creator's lineage.  The handle reaches other harts only by transport: `isLock`'s `lkFloor curCtx lo/lc`, `Lock.lean:604-606`, CtxMorph `:610-617`, along chained moves (fork's `np->lock`, migration's `p->lock`).  Add `lkFloor curCtx Tb` for the payload stamp to `lkFresh`/`isLock` (`Lock.lean:727-729`); `lock_pay_take` uses it at the first acquire.  Same for the `"log"` lock (`ProofInitlog.lean:434` → `LockBornHook.lean:123,30`) |
| 13 | `ProofBrelse.lean:97` `lockHook_llb` | `releasesleep(&b->lock)` re-floors the `lk->lk` payload at the park stamp T′, held only as `topLb T′` (`BcacheInv.lean:1154-1163`).  T′ is `boxPark`'s raised stamp (`CtxBox.lean:1876-1882`, deposit at `max T (max K W)`, `:162`) | **NEEDS-X → X1**: the box's entries are the parker's own stores (own component) or entries it took at checkout with floor ≥ the old stamp (`CtxBox.lean:1770-1775`), so its vector covers T′.  `ctxDeposit` must stamp at bound⊔dirty, not the view K.  Chain = `lk->lk` hop to the next `acquiresleep` |
| 14 | `BcacheLock.lean:132` `lockHook_llb` | `release(&bcache.lock)` re-floors `bcacheResAt`'s slot `tl ≥` every row's `td` (`BcacheInv.lean:723-736`).  `td` was raised by `refDecr` past the releaser's view (`CtxBox.lean:1617-1621`) | **NEEDS-X → X1**: each `td` is a decrementer's own park stamp (covered) or a stamp it reached through `bcache.lock` lineage, so the releaser's vector ≥ all `td`.  Chain = `bcache.lock` hop |
| 15 | `IputLockedB.lean:109` `lockHook_llb` | `iput`'s `releasesleep(&ip->lock)` at `Tc = max Tp offRows` (`IcacheBox.lean:853-855,916-934`) | **NEEDS-X → X1**: `Tp` is its own park.  Off-box rows were parked under `ip->lock` by earlier holders (`OffBox.lean:14-27`) and are chained via the `ip->lock` lineage.  Chain = `lk->lk` |
| 16 | `ProofIunlock.lean:253` `lockHook_llb` | `iunlock`, same as row 15 | **NEEDS-X → X1** (as row 15) |
| 17 | `IcacheTable.lean:682` `ctxStamped_raise` | the `itable.lock` hook raises to the inode box's L1 row receipt `tb` (`:670-680`) | **NEEDS-X → X1**: the icache twin of row 14 (`itable.lock` lineage) |
| 18 | `IcacheTable.lean:694` `ctxStamped_raise` | raise to a live slot's `ip->ref` stamp `tst`.  Every `ref` write is under `itable.lock` by the holder (idup/iget/iput) | **NEEDS-X → X1**: the writer released `itable.lock` after the write, so the releaser's vector covers `tst`.  Chain = `itable.lock` hop |
| 19 | `IgetScan.lean:326` `ownCtx_floor_view` | cashes the row 18 floor `tst` into `viewLb` for the exact `ip->ref` read (`:322-330`) | **CHAINED** (consumption).  The read's source is the `tst` entry: no newer write while `itable.lock` is held.  Chained iff row 18 is |
| 20 | `ProofIdup.lean:318` `ownCtx_floor_view` | same, in `idup` (`:312-322`) | **CHAINED** (as row 19) |
| 21 | `IcacheInvRef.lean:232` `ownCtx_floor_view` (in `ownCtx_key_topLb :226`) | key → `topLb`: the generator of the receipts rows 13–18 re-floor | **CHAINED** (consumption).  Under the vector bound the key's vector replaces the `topLb` |
| 22 | `SpecAcquire.lean:108-120` (+ gen `:146-159`) `wp_acquire_llb_body` | "any `topLb tl` held BEFORE the call is under the AMO, so cash `ctxFloor curCtx tl`" (`:96-103`; `acqPost`, `WpLock.lean:76-79`) | **RESISTS as a LAW → per consumer NEEDS-X → X2/X5**.  The `bget`/`filedup` race: a reference minted under `bcache.lock` at a PARK stamp is not yet chained to its holder (`SpecAcquiresleep.lean:117-127`, "a reference minted before the sleeplock was taken"; `bufEscrow_take`'s `hKt`, `BufEscrow.lean:376-380`).  Chain: `lk->lk` (the parker released it) gives `Kp ≥ tp`, and the holder's `bcache.lock` floor gives `≥ td`.  So `hKt` follows once the box row X2 is added.  The row is invariant: parks set `tp := T`, L1 deposits set `td := T`, keys are minted at T (`CtxBox.lean:1117-1121,1548-1562`) |
| 23 | `SpecAcquire.lean:47-61` `∃ K, viewLb cpu' K` | a machine view receipt (`:18-20`) | **CHAINED** (harmless).  It is a TSO machine fact; it leaks only where it is absorbed (`ctx_absorb`/`ctx_unstamp`/`ctxAbsorbLb`), and those are tabled |
| 24 | `SpecRelease.lean:170-181` `wp_release_hook_body` | the hook surface (`:157-169`) | **NEEDS-X → X1**: the hook's `topLb tl` becomes the releaser's own floor (the definitional change) |
| 25 | `SpecReleasesleep.lean:84-107` `wp_releasesleep_gen_hook_body`; `SleepLockDefs.lean:239-250` `slBody_hook` | the hook, lifted through the sleeplock body | **NEEDS-X → X1** (statement follows row 24) |
| 26 | `BcacheInv.lean:950` `bcacheRes_fold_in`, `:1207` `bufSlp_fold_in` | pure folds `Rin ξ ∗ ctxFloor ξ tl ⊢ R ξ` | **CHAINED** (no mint; the floor's vector comes from rows 13/14) |
| 27 | `IcacheBootTable.lean:677` `newlockAt_llb` | the `itable.lock` born on hart 0 with the hook at `tl` | **CHAINED** (boot hop: `tl ≤ bootEnd`, `started` deposit/absorb, `StartedInv.lean:25-35`) |
| 28 | `ProofVirtioDiskIntr.lean:334` `ctx_absorb` | the handler's post-fence view `F` becomes `ctxFloor curCtx F` and rides the `vdisk_lock` payload (`:323-338`, `DiskInvDefs.lean:4797-4811`) | **DEVICE-KEY, NEEDS-X → X4**.  `diskWm γ n F` concerns device-written `used`/completion records (`DiskInvDefs.lean:1328-1330`).  The absorb must raise only the device component; a scalar absorb at `F` would raise every hart's |
| 29 | `ProofVirtioDiskIntr.lean:299` `ownCtx_key_vis` | cashing `diskPayFl` at the handler's fence (`:276-321`) | nr > 0: **DEVICE-KEY**.  nr = 0: **CHAINED** (boot hop: base = `virtio_disk_init`'s memset on hart 0, `DiskInvDefs.lean:4741-4750`, lock born at `MainFs.lean:316`) |
| 30 | `DiskInvDefs.lean:4751` `diskPayFl`, `:4812` `diskPayWm` | the payload row's carrier | **DEVICE-KEY** (follows rows 28/29) |
| 31 | `ForkretRecord.lean:37` `ctx_fresh`; `SpecAcquire`/`SpecRelease` payload moves | context birth at bound 0 | **CHAINED** (no foreign entries) |

**Totals.**

- CHAINED: 18 rows.  1–11 and 31 are same-hart transports or births; 19–21, 23 and 26 are consumption or pure folds;
  27 is the boot hop.
- DEVICE-KEY: rows 28–30 (29 is DEVICE-KEY at nr > 0, CHAINED at nr = 0).
- NEEDS-X: rows 12–18, 22, 24–25 (row 28 also needs X4).
- RESISTS: none at the program level.  Row 22 RESISTS as a generic law and is withdrawn by X5.

Under the scalar invariant as written, rows 3, 12–18, 22, 24, 25, 27, 28 and the §3 handoff all RESIST.  This is
F0.

## 3. The `swtch`-handoff row: CHAINED via the `p->lock` hop

- The two `wp_swtch` sites are `ProofSched.lean:604` (sched → scheduler: An = `some cpu`, Ao = `none`) and
  `ProofScheduler.lean:671` (scheduler → proc: An = `none`, Ao = `some cpu`).
- All of `ProofSwtch.lean`'s transports run on ONE cpu: rows 5–11.
- The migratable proc record (`procCtxAt`, `ctxParked ξp ξl`, `SchedCtx.lean:1199-1200`) rides `p->lock`'s payload
  (`procSlotsAt :1321-1323`, `procLockResAt :1527-1533`).

The sequence:

1. Hart A's scheduler releases `p->lock`.  `lock_pay_intro` moves the record into ξL and stamps it
   (`Lock.lean:386-398`).
2. Hart B's scheduler acquires `p->lock`.  `lock_pay_take` (`:369-384`) unstamps ξL at the release stamp and moves
   the record into B's scheduler context.
3. `kctx_resume_tok` resumes ξp from under it.

This is one hop on `p->lock`.  It covers A's stack pushes in `sched` (the [R24.s4] example) and A's dirty keys in ξp.
`wpNext` migrations go through the same lock (`yield` → `sched`).  It is expressible because the hop sits on the lock
layer, not in `ProofSwtch`.

## 4. The walker row

- **Kernel table: PTE-KEY.**  The A/D write-back `swp_update_and_write_pte_kpt` (`MachCSL/WpPtWalk.lean:455-470`)
  takes no key; it acts on the `kptOn` invariant, whose entries are A/D variants (`MachCSL/KptInv.lean:1-10`).  The
  walk's `read_pte` (`:52-60`) stamps the foreign-source `coh` (`MachCSL/TsoMem.lean:354-359`) outside any chain.
  Exempt by `Cust.pte`, covered by `pteDiscAt`.  This also covers `Xv6/TransPt.lean`'s kernel-side TLB hit
  (`:10-13`).
- **User table: CHAINED as owned stores.**  `swp_update_and_write_pte_own` (`MachCSL/WpPtWalkOwn.lean:501-515`)
  writes owned `ctxBytes`, stamping a dirty key at the running context (`:13-17`).  Migration carries it over
  `p->lock`.  This holds only if RVWMO orders the implicit A/D store before the hart's later release (Q-R2).

## 5. Fallout outside the 21 files (for W8's file list)

- **Direct leaky sites:**
  - `IputParts.lean:461` and `ProofAcquiresleep.lean:809` (`kctx_floor_of_view`, `KCtxMove.lean:295-303`: absorb a
    `viewLb` into a floor).
  - `StartedInv.lean:198` (`ctxDeposit`) and `:344` (`ctxAbsorbLb`): the boot hop, CHAINED, but they must take the
    restricted forms.
  - `IputParts`'s `tl` is `iput`'s own park, so it is covered by its own component.
  - `ProofAcquiresleep`'s is row 22's cash.
- **Consumers of the hook/llb surfaces (31 files):** IputLockedA, IputEntry, IputParts, LinkAcquire, IputLocked,
  LinkAcquiresleep, ProofAcquire, ProofAcquiresleep, ProofIput, BufEscrow, BreadScan, BreadDefs, IlockMain,
  ProofIlock, ProofBread, SpecAcquiresleep, IgetRecycle, IgetTail, IputLockedC, IgetHit, LinkIget, IputTail,
  LinkRelease, LinkReleasesleep, LinkIdup, ProofBunpin, ProofIget, ProofRelease, ProofReleasesleep, SpecBrelse,
  StartedInv.  Many `Link*` files are pass-through.
- **MachCSL internal leaky sites (already in the 11 files):**
  - `WpLock.lean:1141,1345`: absorb at the AMO's `t`, which must become the stamp `T`.
  - `Lock.lean:375,430`.
  - `KCtxMove.lean:299`.
  - `CtxBox.lean:104,162,1329,1742,1938`.

## 6. Resulting W8 (f2-ctx) size and fallback list

**Additions on top of the plan's W8 (f2-ctx) (`plan :1984-1993`, `:2633-2638`):**

| addition | where | approx. lines |
|---|---|---|
| F0: per-author chain vector + causal closure beside the scalar bound | `Ctx.lean`, `CtxLaws.lean`, `Lock.lean`, `WpLock.lean`, `KCtxMove.lean` | +1–1.5k |
| Box stamps/registers lifted to join-vectors, plus row X2 | `CtxBox.lean` (2,131 lines) | +0.5–1k |
| X1: hooks re-floored from the releaser's own vector (rows 13–18, 24–25) | `Xv6` | — |
| X3: birth key | `Lock.lean:727`, `LockBornHook`, `PipeBirth`, `ProofInitlog` | — |
| X4: device-only absorb | `ProofVirtioDiskIntr`, `DiskInvDefs` | — |
| X5: withdraw the llb cash | the 31 files of §5 | — |
| X1 + X3–X5 together | the `Xv6` files above | +1–1.5k |

**Totals:**

- **≈ 6.5–9.5k lines** (was ≈ 4–6.5k; the β′ twin is unchanged).
- **12 MachCSL files**: the 11 plus `KCtxMove`'s `kctx_floor_of_view`, already listed, and `WpPtWalkOwn` only if
  Q-R2 needs it.
- **≈ 52 `Xv6/` files** (21 + 31).  The remaining `ctxFloor`-only files (`plan :1991`, "up to 43") overlap these
  and change only if the scalar floor's meaning changes.  It does not under the beside-the-scalar form.
- **3–4 full-cone rebuilds.**
- Still serial MachCSL before W-RSV.

**Fallback (f1) list:**

- **Empty** if F0's per-author bound is adopted.
- **Everything** (rows 3, 12–18, 22, 24, 25, 27, 28, the handoff) if the scalar invariant `W8-design.md:343-344` is
  kept.  That is the XL ≈ 10–15k outcome, ≥ 320 files.

## 7. Open questions (spec-first; non-blocking for this read-only item)

- **Q-R1 (F0, for the plan/owner).**
  - *Spec:* RVWMO/riscv.cat define happens-before per event (`rfe`/`ppo` with fence cumulativity).  A per-author
    prefix is exactly what a chain of release→acquire hops carries.  Sail, Zifencei and the PMAs are silent on how a
    proof represents it.
  - *Options:*
    - (a) a per-author vector bound beside the scalar TSO bound (cheapest; FAITHFUL);
    - (b) per-key chain-certificate sets (FAITHFUL, heavier);
    - (c) keep the scalar form, so (f1) everywhere (FAITHFUL, XL);
    - (d) (T) trusted premise (WEAKER).
  - *Recommend:* (a).  It re-sizes W8 (f2-ctx) per §6.  The plan text at `:2603-2607` and W8-design `:343-344` need
    the per-author wording.
- **Q-R2 (user-table walker arm).**  What do RVWMO + Svadu (ADUE = 1, `SpecStart.lean:29,40`) say about the ordering
  of a hardware A/D update relative to the same hart's later `fence rw,w; sw` release?
  - If it is ordered (it is an implicit memory access performed in program order, as the TSO model treats it), the
    user arm is CHAINED (FAITHFUL).
  - If it is not, user-PTE entries need the `pte-key` arm too.  That is a `Cust.pte` extension to proc page tables:
    FAITHFUL, and STRONGER only in documentation.
  - I could not settle this from the tree.  It needs the privileged-spec text.
- **Q-R3 (cosmetic, plan).**
  - `plan :1215`'s "`lock_pay_born` … the only post-boot lock birth" misses the `"log"` lock (`ProofInitlog.lean:434`,
    via `kctx_newlockAt`).
  - `W8-design.md:350` places the `p->lock` hop at `wp_swtch`; it is at `lock_pay_take` (§3).
