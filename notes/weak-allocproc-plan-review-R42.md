VERDICT: NOT SATISFIED

# Review R42 of `notes/weak-allocproc-plan.md` (rev 46): W8 (pte-ghost) [OWN.57], the six new owner questions, F-X, E1′

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git/jj, no subagents). The brief's focus is narrow:
rev 46's NEW item **W8 (pte-ghost)** (`:2268-2298`): is it sound, executable against the tip, and honestly sized? Plus the six new owner
questions (`:5075-5193`), F-X (`:2261-2267`) and the E1′ informed note (`:5194-5201`). Every cite below was read at the working-copy tip of
`../xv6iris-weak`. S4 IS MERGED there (`Xv6/AccessDiscipline.lean:219` `xv6AccessDisc := chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt`;
`custAt_notEx :264`, `chainOkAt_of :300`). Kernel source: `~/dev/xv6-riscv/kernel/{kalloc,vm,proc,fs,virtio_disk}.c`. Sail:
`model/Lean_RV64D/LeanRV64D/{Step,Vmem}.lean`. The running briefs (W5d-G G2–G5 w1, W13 (W) w3, W9a inc. 2 w5) are not touched.

**Sign-off: NO.** There are FOUR required changes, none of them shrinking. **The window-closing idea is SOUND.** Reading freed-ness off
`kmem.freelist`'s byte history, with EVERY hop of the walk restricted, does close the freewalk/freeproc window for every page-table page
of every freeable table (verified case by case below), and the export stays a pure predicate of `σ`. **The SECOND BRIDGE as written is not
executable, though.** `kmemHeadOk` lives in the lock-protected `kmemRes`. Its only consumer is `kpt_readAU`, a page walk that runs on ANY
hart at ANY time, and it cannot reach `kmemRes` [R42.1]. The bridge's exclusivity argument also misses the 64 all-leaf kernel level-0
pages [R42.1]. On top of that, the bridge is unnecessary: the window exists ONLY for user tables, whose `.pte` arm no proof consumes
(the only `.pte` receipt in the tree is `KptInv.lean:540`, kernel leaves). So restricting liveness to the per-process root region closes
every window. It needs no kalloc or KptInv proof work and is about a third of the size [R42.1, recommended option]. The other three
required changes are plan text: [R42.2] the residual sentence is false under `loadsChained`'s as-of-ENTRY exemption; [R42.3] Q-PTEDISC
lacks the Sail file:line (owner rule); [R42.4] Q-W9A marks (A) "FAITHFUL" although `runAligned` is a run premise that Sail does not
guarantee.

## W8 (pte-ghost) — what was verified, and holds

- **Timestamps are global**, so comparing positions across addresses (head word vs naming word) is meaningful. Every store gets "its
  position in the store order" (`MachCSL/TsoMem.lean:8-14`), and `HEnt` holds t/tid/v (`:76-80`). ✓
- **The exemption is monotone in the top**, as the step law needs. `ptFreedSince … (t0, t]` reads only entries at or below `t`, so the
  `_grow` lemma follows `ptByteAt_grow` (`ChainDefs.lean:740`, used `:752`) and `loadsChained_step`'s `hex` (`:594`) is met. ✓
- **The export stays a pure σ-predicate.** It reads only the static registry (a new footprint-free kind, like `.roots`/`.devPtr`,
  `Reserved.lean:137-151`) and `σ.mem` histories (`wordAsOf :646`). ✓
- **The window closes for EVERY user page-table page.** Every page-table-page free goes through `freewalk` (`vm.c:265-280`), which frees
  bottom-up and pushes each page (`kalloc.c:61`) before its parent slot is cleared (`vm.c:273-274`):
  - the root: freed before `p->pagetable = 0` (`proc.c:162-163`). Its naming word was written at `allocproc`, before the push, so the root
    is not live from the push on ✓;
  - level-1 and level-0 pages: freed before their slots are cleared ✓;
  - `proc_pagetable`'s failure path: frees a table never stored in a root word, so no window ✓;
  - `exec`: moves the root word first ✓;
  - `uvmdealloc`/`uvmunmap`: free leaf DATA pages only, which `ptPtrTo` never follows (RWX ≠ 0) ✓;
  - a reallocated page is named by a fresh slot write, `walk`'s `*pte = PA2PTE(..)|PTE_V`, after its pop. Its old head entries are below
    the new `t0`, so it is live again only through the new word ✓.

  Entries the new owner writes after the push are not exempt as of their position ✓.
- **The junk walk inside the residual is harmless, now for PARTIAL fills too.** `freewalk` zeroes every pointer slot, and panics on a
  leaf, before `kfree`, so a page-table page is all-zero when `kfree`'s `memset(pa, 1, PGSIZE)` (`kalloc.c:55`) starts. I enumerated all
  256 byte-subsets of a word with `0x01` bytes over zero: NONE is a V-only pointer whose `ptPtrTo` target lies in RAM
  `[0x80000000, 0x88000000)` (`TsoMem.lean` `ramBase/ramEnd`). So while the dying page is still walked, its children lead nowhere. ✓
  (Record this; [R42.s3].)
- **All cites check out**: `HEnt :76-80`, `wordAsOf :646`, `ptPageAt :660`, `ptRootAt :664`, `ptByteAt :670`, `chainExAt :699-702`
  (third disjunct `:701`), `kmemFreelistAddr` `KallocDefs.lean:67`, `chainAt :143-146`, `kmemRes :330`, `Kev` `KallocEv.lean:45-52`
  (`KFree` names the actor ✓), `KptInv.leaf_ptByteAt :328`, `kalloc.c:55/60/61/62`. ✓
- **"The ONLY consumer of the strengthening is `KptInv.leaf_ptByteAt`" is TRUE.** `grep exCertAt` finds exactly five receipt producers:
  `Lock.lean:1278,1315` (dynamic locks), `KptInv.lean:529-545` (kernel leaves, the only `.pte` one), `IcachePinwObl.lean:142` (racy) and
  `DiskAcc.lean:2052` (devPtr). No proof produces a user-table `.pte` exemption. §D Q-F2-PTE-WINDOW says the same (`:5229-5230`: "the
  user-table half of the exemption is never NEEDED by the proof"). ✓

## REQUIRED changes

**[R42.1] The second bridge (B2) cannot reach its consumer, its exclusivity argument misses the all-leaf kernel pages, and it is
unnecessary. Rescope (recommended) or re-specify and re-size.**

*What is wrong.*
1. *Placement.* The plan keeps `kmemHeadOk` "in `kmemRes` (`:330`) as a pure history fact plus a ghost freed-page LOG" (`:2281-2284`) and
   has the kernel-leaf receipt "lend the head word's history beside the root word and the two frozen pointers" (`:2286-2287`). The
   receipt is produced in `kpt_readAU` (`MachCSL/KptInv.lean:416-545`), the read of a kernel PTE by ANY hart's page walk. It lends
   companions as `histBytes` fragments (`RdComps`, `WpAtomic.lean:465-470`); for the root and the two frozen pointers these are
   `DFrac.discard` (`KptInv.lean:510-512`). The exemption is the pure implication of `exCertAt` (`WpAtomic.lean:502-506`), which can
   only use lent histories and entry receipts. The head word, however, is owned `wordAtN ξ kmemFreelistAddr 8 (DFrac.own 1) head`
   inside `kmemRes` (`KallocDefs.lean:330-332`). That is `ctxBytes` → `ctxByte` = `a ↦ₕ{own 1} (e :: H) ∗ keyAt …` (`Ctx.lean:989-990`),
   available only to the `kmem.lock` holder. A walker on hart A, while hart B holds `kmem.lock` (or while nobody does, since the payload
   sits in the lock's invariant), has no fragment of the head word's history to lend, so the pure implication cannot exclude head entries
   naming the kernel table's pages. A "pure history fact" inside `kmemRes` is equally out of reach, because a ⌜⌝ inside a lock payload is
   not readable without the lock.
2. *Exclusivity.* `kptNeverFreed` is derived from "`KptInv`'s FROZEN pointer/empty cells (persistent — exclusive with the own-1 first
   word a free-side holder has)" (`:2284-2285`). The kernel's direct map `kvmmap(KERNBASE…etext)` + `kvmmap(etext…PHYSTOP)`
   (`vm.c:39,42`) fills all 512 entries of each of the 64 level-0 pages covering `[0x80000000, 0x88000000)` with LEAVES. Those pages
   have NO frozen `ptrCell`, and their first word is a leaf `pteCell` inside the `kptN` invariant (`kptBody`, `KptInv.lean:115-117`;
   `wordCellT` = `histBytes … own 1`, `WordHist.lean:285-287`). For them the argument has to OPEN `kptN` at every head store (each push,
   each pop's new head, `freerange`'s boot pushes before the seal excepted). The plan does not say so.
3. *Necessity.* The window exists only for tables that are ever freed: user tables (§D `:5212-5222`, `:5231`). The kernel table is never
   freed. It is frozen after the seal (`kptPtrs`/`kptRootW`, `KptInv.lean:120-151`), and xv6 has no `kfree` of a kernel page-table page.
   No proof consumes the user `.pte` arm (verified above). Restricting the walk ONLY for user roots therefore closes every window and
   leaves the one consumer, `leaf_ptByteAt`, untouched.

*Exact change to the plan* (the W8 (pte-ghost) paragraph `:2268-2298`, the Stage 2 roadmap, §D Q-F2-PTE-WINDOW's RULED header).
Replace the B2/`kptNeverFreed` text with **option (i), RECOMMENDED**:
- **Registry.** Split the root registry kinds into PERMANENT roots (`kernel_pagetable`, `xv6KptRootR`, `KernelRsv.lean:72`) and FREEABLE
  roots (`proc[i].pagetable`, `xv6ProcRootsR`, `:74`). Do this with a new footprint-free kind `RsvKind.uroots cnt stride`, or a `Bool`
  on `.roots` (worker's choice; about 9 match sites: `Reserved.lean:159,180,210,316,366,473`, `KernelRsv.lean:245`,
  `BootRsv.lean:55,64`).
- **Definition.** `ptByteLiveAt` := the unrestricted `ptByteAt` walk from a PERMANENT root ∨ the hop-restricted live walk (every hop not
  `ptFreedSince` its naming word's position) from a FREEABLE root, with `RsvKind.freeHead` / `xv6FreeHeadR` as written.
- **Kernel side.** `KptInv.leaf_ptByteAt` → `leaf_ptByteLiveAt` is a one-line left injection, with no new companion. No `kmemHeadOk`,
  no ghost log, no `Kev` change, no `kmemRes` change, and no `ProofKfree`/`ProofKalloc`/`ProofKinit`/`ProofFreerange`/`KmemTier` edits.
- **Docstring.** The export docstring says why the kernel walk needs no freed-check: the kernel table is never freed (`KptInv` frozen
  pointers and root word). On every xv6 run the export is EQUAL to the intended "bytes of pages in use as page-table pages". Spec line
  unchanged (SILENT; FAITHFUL).
- **Acceptance.** Defs + `_grow`; `ptByteLiveAt_freed`; `chainExAt`/`custAt` over `ptByteLiveAt`; `leaf_ptByteLiveAt`; gates as
  written.
- **Size.** S–M ≈ 0.3–0.7k, files `Reserved`, `ChainDefs`, `KptInv` (lemma only), `KernelRsv`, `BootRsv`, `AccessDiscipline`, plus
  tcb. Record this as [OWN.57]'s option (c) scoped to the freeable tables: freed-ness is still read off `kmem.freelist`'s history, and
  the owner is informed, with no menu (EQUAL export on every xv6 run).

If the coordinator prefers the uniform predicate (**option (ii)**), the paragraph must instead specify all of the following:
- (1) a NEW always-open invariant (own namespace) holding a fraction of the head word's histories (`↦ₕ{½}`). It carries the pure fact
  "no head entry after the seal spells a page of the kernel `PTree`". `kmemRes` keeps the other half (`ctxBytes … ½`), and every head
  store (`kfree` `kalloc.c:61`, `kalloc` `:73`, `kinit`/`freerange`) opens it to recombine the fractions and re-establish the fact.
- (2) the fact's proof at each store: open `kptN` for leaf-only pages; use the persistent `ptrCell` otherwise.
- (3) `kpt_readAU` opens that invariant and lends the head histories as a FOURTH companion.
- (4) the files: add `Xv6/KmemTier.lean` (it unfolds `kmemRes`) and the kernel-context threading of the new invariant's name.
- (5) RE-SIZE to ≈ 1.6–2.6k. The 1.0–1.6k does not cover the `kmemRes` split across the five unfolding files (`KallocDefs`,
  `ProofKfree` 620 l., `ProofKalloc` 598, `ProofKinit` 292, `KmemTier`) plus `ProofFreerange` (577) and the leaf-case `kptN` opening.

**[R42.2] The residual sentence and the "loses the exemption" list are false under the as-of-ENTRY exemption.**

*Evidence.* `loadsChained` exempts `ex a e.t`, at the position of the ENTRY READ, not the time of the read (`ChainDefs.lean:573-576`;
`chainOkAt` likewise, `AccessDiscipline.lean:183-189`, `custAt σ a e.t`). The plan says (`:2279-2281`): "Residual (docstring): a dying
page-table page stays exempt from `kfree`'s entry to its push … while the freeing hart holds it EXCLUSIVELY … — no foreign read exists
there". The entries the freeing hart writes in that interval stay exempt FOREVER, as of their own positions: the `0x01` fill (`kalloc.c:55`)
and `r->next` (`:60`, before the push `:61`). They ARE read later by another hart: `kalloc`'s `kmem.freelist = r->next` (`kalloc.c:73`)
reads the `:60` entry under `kmem.lock`. So "no foreign read exists" is false. Likewise, `:2287-2288` lists "`kalloc`'s `r->next` under
`kmem.lock`" among loads that LOSE the exemption. It does not lose it: the entry predates the push. This is harmless, because that read
is lock-chained anyway, but it is wrong text that would go into the docstring.

*Change.*
- **Residual sentence.** Replace it with: "Residual (docstring): the exemption is keyed on the ENTRY's position. The entries the freeing
  hart writes inside `kfree` before its push (the `0x01` fill, `r->next`; `kalloc.c:55,60`) were written while the page was still a live
  page-table page, so they stay exempt. The one later foreign read of them is `kalloc`'s `r->next` (`kalloc.c:73`), under `kmem.lock`
  (also lock-chained). The fill's partial words lead nowhere in RAM ([R42.s3])."
- **"Loses" list.** Drop `kalloc`'s `r->next` from it. Every load of an entry written AFTER the push loses the exemption.
- **Acceptance.** "no window" becomes "no window; the residual is as stated".

**[R42.3] Q-PTEDISC's Spec (FIRST) does not cite the Sail model (owner rule 2026-10-09).** `:5172` says "Sail performs it as
`read_pte_exclusive`/`write_pte_conditional`" with no file:line. *Change:* add `model/Lean_RV64D/LeanRV64D/Vmem.lean:237`
(`read_pte_exclusive`) and `:228` (`write_pte_conditional`). The other five questions meet the rule: Q-KCAT, Q-F-RACY, Q-DYNLKDISC and
Q-F-DISKTAIL state Sail SILENT; Q-W9A cites `Step.lean:331-335`, which I verified (`:332` `dispatchInterrupt` before `:335` `fetch`).

**[R42.4] Q-W9A option (A) is marked "FAITHFUL" (`:5117-5119`), but `runAligned` is a premise on the RUN that Sail does not guarantee.**
Sail dispatches a pending enabled interrupt at ANY instruction boundary (`Step.lean:332-334`), and the question's own example has an
interrupt landing inside a certified stretch with SIE = 1. Under (A) the theorem covers only runs in which no certified stretch is
interrupted. That is an assumption STRONGER than Sail, and its scope shrinks with run length: with interrupts on, a long run almost
surely interrupts some stretch. The owner format requires the faithful/stronger/weaker mark and "what that means in practice".
*Change (§D text only; the running W9a brief is untouched):* "(A) — interim only: the memory model is kept FAITHFUL, but the theorem is
CONDITIONAL on the run premise `runAligned`, which is STRONGER than Sail (Sail may take an interrupt at any boundary). In practice it
excludes every run in which an interrupt, a taken branch off the walk, or a clobbered `ret` lands inside a certified stretch; for long
runs with interrupts on, that is most runs. It must not remain in the published theorem; (B), or (C) for interrupt-free sites, removes
it."

## Checked and accepted

- **F-X** (`:2261-2267`). The verification is reproducible: `grep -E 'ACQUIRE_LLB|ACQUIRESLEEP_LLB' MachCSL/` returns 0 hits, and
  `Xv6/` returns 31 hits in 18 files. `acquire_llb_proof` is at `Xv6/ProofAcquire.lean:242`, `AcquireLlb` at `LinkAcquire.lean:18`, and
  the `ACQUIRE_LLB` structure at `SpecAcquire.lean:123`. No file that produces `srcCertAt`/`chainLb`/`readCertsAt` mentions those
  surfaces. The `llb` hits in `MachCSL/{Ctx,Lock,Wp}` are the generic view-lower-bound notion, not the surfaces. The replacement check
  (tcb names no LLB surface; the MachCSL grep stays empty) is the right automatic guard. Dropping the greps as an acceptance item is
  sound.
- **E1′ / (H3′)** (`:1543`, `:5194-5201`; `Weak/GraphFetchSpike.lean:290-312`). It is correctly identified as the carried-over R1 (a)
  reading, it is listed in §B(11), and its Spec is stated first: `Step.lean:335` checks out, and the `Fetch.lean:253-288` /
  `PlatformConfig.lean:2157` cites in the docstring are consistent. It is STRONGER than the spec text and true of in-order-fetch hardware
  (a later instruction's access performs after its own fetch, which follows the earlier fetch; a cross-hart source visible to a fetch is
  globally performed). I accept it as informed; [R42.s6] is about presentation only.
- **The six questions' format.** Each has a plain-language statement, a tiny example, definitions, why it matters, Spec FIRST, and per
  option the change, the mark, the cost and what it unblocks or risks. The exceptions are [R42.3] and [R42.4], plus the polish in
  [R42.s4]/[R42.s5].

## SUGGESTIONS

- **[R42.s1]** Update the status lines. S4 is MERGED at the tip (`Xv6/AccessDiscipline.lean:219`), so W8 (pte-ghost) is LAUNCHABLE NOW,
  not "after the S4 merge". Places: §C top `:2209-2210`, the roadmap `:2299-2300`, launch status `:4906-4908`, the header `:4`.
- **[R42.s2]** Define the naming word's position as the max over its 8 bytes of `entAsOf … t`'s `.t` (ENTRY-based: the latest write,
  even if it rewrites the same value), e.g. `wordPosAsOf`, beside `wordAsOf :646`. A value-based "since it has held this value" reading
  would wrongly keep a re-linked page freed.
- **[R42.s3]** Put the partial-fill fact in the docstring and §A: a page-table page is all-zero at `kfree` (`freewalk` zeroes each
  pointer slot and panics on a leaf, `vm.c:270-277`), and no byte-subset of `0x01` over zero is a V-only pointer into RAM (256 cases
  enumerated). A `ptPtrTo_fill01_notRam` lemma by `decide` over the 256 masks would make it a theorem (≈ 30 lines).
- **[R42.s4]** In Q-PTEDISC's tiny example, change "hart 1's `walk` reads a kernel PTE" (`:5166-5167`). After the seal no SOFTWARE reads
  kernel PTEs; `walk` is the user-table walker. Write "hart 1's hardware walker reads a kernel PTE on a TLB miss".
- **[R42.s5]** Disambiguate "STRONGER export" (Q-F-RACY (b), `:5139`) from "STRONGER than the spec" (an extra assumption). For example,
  write "export more informative than (a); spec mark FAITHFUL". The owner's scale uses STRONGER for assumptions.
- **[R42.s6]** The E1′ note adds a stronger-than-spec item to the published trusted base. Give it the owner format's tiny example (hart 0
  fetches instruction k from hart 1's store W; (H3′) says W is gmo-before hart 0's later LOAD at k+3, not only its later stores) and
  define (Z2), (H3), gmo and `gzFetch`, so the owner can decide whether to re-open it.
- **[R42.s7]** Cite drift: `chainExAt`'s third disjunct is `:701`, not `:702` (`:2276`).

## Owner questions the plan is missing

None blocking. Under [R42.1] (i), inform the owner, with no menu, that [OWN.57]'s option (c) is implemented scoped to the freeable
(per-process) tables: freed-ness is still read off `kmem.freelist`'s write history; the kernel table is never freed, so its walk needs no
check. RVWMO/riscv.cat/Sail/Zifencei/PMAs are SILENT on custody (no hart's `satp` names a dying user table at `freeproc`), the option is
FAITHFUL, and the export is EQUAL to the intended one on every xv6 run. The owner may ask for the uniform form ((ii), ≈ 1.6–2.6k) instead.
