# RVWMO / Zifencei spec audit: what is confusing or underspecified, how this proof read it, and what the decisions commit us to

One-off advisor, 2026-10-21, for owner ruling [OWN.140] ("I do want to audit what parts of the spec you find confusing
or are underspecified in RVWMO and Zifencei, and the implications of the decisions taken so far").  Design/analysis
only: no proofs, no builds, no jj/git.  Every `file:line` was re-read at `/home/bsdinis/dev/xv6iris-weak` with
`sed`/`grep`.  The RISC-V specification texts are NOT in the tree; where the audit quotes or paraphrases them it
relies on memory and says so ("from memory, verify").  Spec documents referred to: the unprivileged ISA's memory-model
chapter ("RVWMO", with its formal `riscv.cat` appendix), Zifencei, Ziccif, the A extension, Zicsr, and the privileged
ISA (page tables, `sfence.vma`, PMAs).

**Status 2026-10-21 (doc-fix pass).**  Q-AUDIT-1 RULED (a) [OWN.142] (keep (R1) until the capstone; Sail gap recorded
as SAIL-GAP-1 in `notes/sail-gaps.md`); Q-AUDIT-2 RULED (ii) [OWN.143] (align `fence.i` to Zifencei NOW — non-draining,
`itv := max itv (max tv (max rv pub))`; this overrides the recommendation (iii) below).  §4 items carry a status tag;
the plan items (§4 items 4, 5, 8, 10's `plan:344`) are left to the plan reviser.

**Names used throughout (defined once here).**
* *RVWMO* — the RISC-V weak memory model: a set of axioms on *execution graphs* (memory events, program order `po`,
  reads-from `rf`, per-location write order `co`, one *global memory order* `gmo`); *ppo* = "preserved program order",
  the 13 rules saying which same-hart pairs must be ordered in `gmo`.  *riscv.cat* = its formal, machine-readable
  version (herd).  In the tree the model is transcribed in `Weak/AxGraphCat.lean` (`rvwmoCatConsistent`, ≈ :190) and,
  with tagged dependencies, `Weak/AxDeps.lean:299` (`rvwmoCatConsistentT`) — THE published quantifier ([OWN.2], [OWN.13]).
* *Sail* — the official executable RISC-V ISA model, compiled to Lean (`model/Lean_RV64D/LeanRV64D/`); it defines what
  each instruction does to registers and which memory requests it issues, but has no memory model, no fetch model
  beyond "read these bytes", no devices and no DMA.
* *MachCSL* — the proof machine the kernel proof (Iris-style program logic) runs on: Sail for instructions plus a
  memory model (`MachCSL/TsoMem.lean`, `MachCSL/Lang.lean` `evStep :1361-1402`).  Under *route P* ([OWN.110]) each hart
  has a *store buffer* (`MState.sb`): a plain store *issues* into it and *lands* later into one global *landing log*
  (`llog`, the write order); loads read at a per-hart *view* `tv ≤ tvn ≤ ltop` and forward from the hart's own pending
  stores; fences move views / drain the buffer.
* *The bridge* — the proof that every riscv.cat-consistent execution of this kernel image is reproduced by a MachCSL
  run (*completeness*; the direction the theorem needs).  *The walk / replay* (`Weak/Sb*.lean`) replays a graph on a
  twin machine `SbCand`; *the realization* turns that into a real MachCSL run.
* *Trusted texts* — premises of the published theorem with no reference model behind them: the I/O residue
  `ioResidueGmo` with arms (R1), (R2), (R2′), (R3), (R2″) (`Weak/GraphFabResidue.lean:116-143`), the fetch text `gzFetch`
  with clauses (Z1)–(Z3) and (Z2)'s strong form E1′ (`Weak/GraphFetchSpike.lean:292-318`), and the device-model texts
  (`diskFabPo`, `usedElemGateOk`).
* *Marks.* FAITHFUL = same behaviours as the spec; STRONGER = our model admits FEWER behaviours than the spec (the
  theorem then covers fewer executions than "all RVWMO executions"; never unsound, but an over-claim if undocumented);
  WEAKER = our model admits MORE behaviours (harmless for the bridge direction, since the kernel proof then covers extra
  runs; a problem only for a "sound by construction" claim); OUTSIDE-SPEC = the spec says nothing (device models);
  TRUSTED TEXT = a named premise.

---

## 1. One-page summary: the spec points that matter most for the credibility of the final theorem

1. **MMIO versus RAM ordering is where the spec is thinnest and where we assume the most.**  RVWMO's only
   tool for ordering a RAM access against a device (MMIO) access is a `fence` whose predecessor/successor sets carry
   the `i`/`o` bits (`fence w,o`, `fence iorw,iorw`); PMAs ("strongly ordered I/O") order I/O against I/O only.  The
   Sail model DISCARDS the i/o bits in its decoder: `execute_FENCE` keeps only bits 1:0 of each set
   (`InstsEnd.lean:18299-18314`: `fence iorw,iorw` becomes `rw,rw`; `fence w,o` becomes a no-op; `effective_fence_set`
   `BaseInsts.lean:568` folds i/o into r/w only when `menvcfg.FIOM = 1`, which xv6 never sets).  The graph model
   therefore gives an I/O event NO fence ordering at all (`gfenceCovers` `Weak/WeakRvwmoGraph.lean:235-239` requires
   `lbIsR`/`lbIsW` on both ends; I/O labels are neither).  So on fences with i/o bits the tree's RVWMO is WEAKER than
   the spec — and the tree compensates with the trusted (R1)/(R2)/(R2″), which are STRONGER than the spec (every
   MMIO access is a one-way fence; true of QEMU-TCG, not of RVWMO + PMAs).  Two consequences for the owner:
   (i) the published theorem describes a QEMU-like platform, not every RVWMO machine, for every UART/PLIC/virtio path;
   (ii) the model cannot, today, tell a correctly fenced MMIO sequence from an unfenced one — the fix recorded for xv6
   weak-memory bug #1 (`fence iorw,iorw` after the `memset`s, `notes/xv6-weak-memory-bugs.md:20`) would be INVISIBLE to
   the graph model (recorded as SAIL-GAP-1, `notes/sail-gaps.md`, [OWN.142]); only (R1) makes the device see the zeroed pages.  Plan item A4 (drop the hart-side (R1) after the
   capstone) must therefore be paired with a faithful fence-with-i/o-bits rule, or the virtio NOTIFY shape risks a
   stuck replay (§2 row 7, §5 Q1).
2. **Instruction fetch and `fence.i` have no model in the spec; ours is a hand-written text, stronger in places,
   and the machine does not match it exactly.**  RVWMO has no fetch events; Zifencei says only that a `fence.i` makes
   the hart's earlier stores (and, from memory, verify: "any store already visible to the hart") visible to its own
   later fetches.  The tree's `gzFetch` E1′ ("a fetch's source write is gmo-before EVERY later memory access of the
   hart") is a NAMED stronger reading (in-order fetch), listed in plan §B(11); the machine's `fence.i` DRAINS the
   store buffer (`TsoMem.lean:863`, `Lang.lean:1395` — STRONGER; EX-FENCEI-1, `notes/rvwmo-machine-examples.md`) but
   does not enforce E1′ (F-A5-1, `proposal-A5.md` §2.4) and does not pass the hart's read watermark into the
   instruction view (`MState.fence` `Lang.lean:193-200`: `itv := max itv (max tv pub)`, no `rv`) — WEAKER than
   Zifencei's "already visible" clause for foreign code stores the hart has loaded.  Three documents disagree on this
   row (§4).  None of it is unsound (the bridge direction tolerates a weaker machine; E1′ is a stated premise), but
   `notes/weak-allocproc-routeP-design.md:161` marked the drain FAITHFUL, which was wrong (corrected 2026-10-21 to
   "STRONGER today; being aligned to Zifencei per [OWN.143]"; [OWN.143] makes `fence.i` non-draining and passes `rv`).
3. **Dependencies: the spec's syntactic-dependency rules (ppo 9–13) are the most intricate part of RVWMO and the
   machine ignores them.**  MachCSL tracks no address/data/control dependency (`Lang.lean:1373-1377`; design
   `routeP-design.md:159`) — WEAKER (more runs), harmless for the theorem ([OWN.109], [OWN.141]) and fatal only for a
   future "sound by construction" claim (review B5 §2(c), MP+addr example).  The graph side had the opposite problem:
   an untagged rule 12 (`[M];(addr|data);[W];rfi;[R]`) also ordered through control dependencies — STRONGER and marked
   unsound for safety, fixed by the tagged model ([OWN.13]).  Dependencies through CSRs (`satp`, `sstatus` → later
   accesses) are not defined by RVWMO (from memory, verify: the spec's dependency definition is over integer/FP
   registers) — the tree adds tagged `DTctx`/`DTtrans` edges (`AxDeps.lean` §1), a modelling choice.
4. **Implicit accesses (page-table walker reads, A/D-bit updates) and `sfence.vma` are governed by the privileged
   spec's prose, not by riscv.cat.**  We model walker reads as the hart's own PLAIN loads (they forward from its
   store buffer, obey per-byte coherence), A/D write-backs as an AMO (exclusive pair landing at once), `sfence.vma` as
   a memory no-op (`Lang.lean:1397` `.tlbi`; Sail flushes its TLB `InstsEnd.lean:18009-18030`).  The privileged spec
   (from memory, verify) says implicit reads may be performed early and cached, and are ordered after explicit PTE
   stores only by `sfence.vma`; A-bit updates may be speculative ([OWN.39]).  Treating walker reads as explicit
   loads is STRONGER than that prose (the walker always sees the hart's own PTE stores), while Sail's TLB re-adds
   staleness; and premise P2 (no dangling exclusive read, `Weak/GraphFetchBlocks.lean:87`) excludes a real race on a
   user table's first touch (plan SCOPE :518-522) — STRONGER than the platform.  xv6 is fenced (`sfence.vma` after
   every table switch), so these are credibility items, not bugs.
5. **Everything about devices is outside the spec.**  DMA, when a virtio device reads a ring, how a UART or the PLIC
   orders its registers against the fabric, interrupt delivery — RVWMO, Sail, Zifencei and the PMAs say nothing.  The
   tree's device programs (`MachCSL/Dev/*.lean`, `Weak/VirtioProg.lean`) are the model of record; the disk program is
   SEQUENTIAL (STRONGER than virtio's concurrent queue, [OWN.33]); one graph row couples UART/PLIC/disk ([OWN.18]);
   `usedElemGateOk`/`diskFabPo` are permanent device-model premises; and PLIC pin deliveries are I/O events under
   (R1), which makes every interrupt entry a one-way store fence — STRONGER than the ISA, which makes traps no
   ordering point at all.  An xv6 expert should read the final theorem as "for devices that behave like these
   programs on a fabric that serializes like QEMU's".
6. **Mixed-size and misaligned accesses are only partly specified by the ISA and only partly modelled here.**
   riscv.cat is per access with no mixed-size story; the ISA guarantees single-copy atomicity for naturally aligned
   accesses ≤ XLEN only.  The tree's load-value axiom is per BYTE with one gmo position per load (`gloadValue`
   `WeakRvwmoGraph.lean:300-306`), MachCSL reads every byte of an access at ONE view (atomic misaligned accesses —
   STRONGER for user code; Sail has `Zicclsm` ON, `PlatformConfig.lean:2158`), the kernel's accesses are aligned
   (`candSca`, D20).  Caveat for user programs only (N10).
7. **Smaller but real: what the transcription omits or alters.**  Rules 6 and 8 omitted (sound direction, xv6 has no
   `.rl`/LR-SC); rule 7 repaired to riscv.cat's RCsc ([OWN.54]); rule 5 extended to I/O successors (a strengthening
   the spec's I/O-ordering condition excludes, subsumed by (R1), D52); `fence.tso` labelled as `fence r,r`
   (`Weak/WeakEvLang.lean:751` — WEAKER, drops its W→W half; the machine has it right, `fenceEpoch`; vacuous, xv6
   emits none); LR/SC reservation predicates are opaque platform constants (`Xv6Extras.lean`, "arbitrary but fixed");
   Sail asserts the walker's conditional PTE write never fails (`Vmem.lean` `update_and_write_pte`, `internal_error
   "PTE conditional write failed"`) and MachCSL makes that true by blocking other harts' overlapping stores while a
   reservation is held.  Liveness, the spec's progress axiom, timing and power cycles are out of scope (safety-only).

Bottom line: the final theorem is sound as stated; its credibility hinges on three named, stronger-than-spec readings
— the I/O residue, the fetch text E1′, and the device programs — and on a hand-transcribed riscv.cat checked only by
litmus tests.  The I/O point is the one where the documents' marks are misleading and where a planned after-capstone
step (A4) needs a design change.

---

## 2. The table: spec points that are confusing, informal, ambiguous, silent or underspecified

Columns: spec text (section, from memory unless a tree file is cited); why it is confusing/underspecified; how we
interpreted it (file:line); mark; which rulings/decisions depend on it; implication for what an xv6 expert can conclude.

| # | Spec point (cite) | Why confusing / underspecified | Our interpretation (file:line) | Mark | Rulings depending on it | Implication for the final theorem |
|---|---|---|---|---|---|---|
| 1 | **Instruction fetch vs data accesses.**  RVWMO ch. "Memory Model": no fetch events; Zifencei: `fence.i` "synchronizes the instruction and data streams", a later fetch sees stores "already visible to the hart" (from memory, verify).  Explanatory appendix: self-modifying code needs `fence.i`; cross-hart needs a data fence + remote `fence.i`. | The spec never says WHEN a fetch happens relative to the hart's loads/stores, whether a fetch may read a store the hart has not yet made visible, nor what "visible to the hart" covers (own buffered stores? foreign stores it has loaded?). | Graph: `gzFetch` (Z1) value, (Z2) E1′ "source gmo-before every own memory event at/after the slot", (Z3) "fresh past `fence.i`, one fill instant" (`GraphFetchSpike.lean:306-318`); contributors = own writes before a `fence.i` site AND rf-sources of the hart's earlier reads (`gzContrib :285-290`).  Machine: fetch reads landed memory at `itv ≤ tvn ≤ ltop`, never forwards (`Lang.lean:1368-1371`); `fence.i` drains the buffer (`TsoMem.lean:863`, `Lang.lean:1395`) and raises `itv` past `tv` and the own last landed store, NOT past the read watermark `rv` (`Lang.lean:193-200`). | Graph text: STRONGER (E1′; no reference model) — TRUSTED TEXT.  Machine drain: STRONGER (EX-FENCEI-1).  Machine `itv` without `rv`: WEAKER than Zifencei's "already visible" (harmless).  Machine does not enforce E1′: WEAKER than our own text (F-A5-1). | [OWN.3] [OWN.6] [OWN.15] [OWN.26] [OWN.35] [OWN.42] [OWN.86] [OWN.101] [OWN.137] [OWN.138] [OWN.139] [OWN.143] (align the machine's `fence.i` now: no drain, `itv` past `rv`) | The theorem covers user code and `fork→exec` paths only under E1′ (in-order-fetch hardware); an out-of-order-fetch design that lets a later load be satisfied before the fetch's source is visible is outside the quantifier.  Nothing in xv6 relies on `fence.i` as a data fence (EX-FENCEI-1 is not a bug). |
| 2 | **Zifencei scope: "the same hart" only.**  `fence.i` orders a hart's OWN stores before its OWN later fetches; cross-hart code publication needs the writer's data fence and the fetching hart's `fence.i` (from memory, verify). | Informal; the interaction "writer's store → reader's acquire → reader's `fence.i` → fetch" is a chain the spec describes in prose only. | `gzContrib` includes rf-sources of the fetching hart's earlier reads, so a foreign code store the hart has observed must be visible to a fetch after `fence.i` (`GraphFetchSpike.lean:285-290`); the fetching hart's acquire raises `tv`, `fence.i` lifts `itv ≥ tv`. | Graph: FAITHFUL.  Machine: see row 1 (`rv` not passed). | [OWN.3] (user text after `exec`), (f3-utext) rows, [OWN.87] | `exec` + user fetch on another hart is covered because xv6's hand-off is a lock release/acquire chain, not because of `fence.i` alone. |
| 3 | **Ziccif / fetch atomicity.**  Ziccif: a naturally aligned fetch of up to XLEN bits is atomic (from memory, verify); the base ISA leaves a misaligned 4-byte instruction fetch as two halves. | Which bytes a torn fetch may mix is implementation-defined. | Sail `fetch` does one 4-byte read at a 4-aligned pc under `Ext_Ziccif` (`Fetch.lean:253-288`, `PlatformConfig.lean:2157`) else two halfword reads; (Z3) "one fill instant per label"; `textAt4S` covers 2-aligned 4-byte words (Q22, commit f5ba22147). | FAITHFUL (follows Sail + Ziccif). | [OWN.35] (Sail cycle order), Q22, [OWN.144] (Q1 fetch half (E2): MachCSL guard "a Supervisor-mode, armed, RAM-PC ifetch read is at pa ∈ {PC, PC+2}" + a FAITHFUL Sail-text lemma that the k-th ifetch read of `fetch()` is at pc + 2k) | None beyond Sail's own platform assumptions. |
| 4 | **Implicit page-table reads.**  Priv. spec, Sv39 "Memory Ordering" prose: implicit reads of PTEs are not ordered w.r.t. explicit stores except by `sfence.vma`; they may be performed early and results cached (TLB); `Svvptc`: invalid→valid becomes visible without `sfence.vma` eventually (from memory, verify). | Pure prose; riscv.cat has no translation events; how an implicit read sits in `gmo` is unspecified. | Walker reads are the hart's PLAIN loads: `Lang.lean:1372-1376` (forward from the buffer, per-byte coherence floors); design `routeP-design.md:162` "FAITHFUL w.r.t. cat"; Sail's TLB (`VmemTlb.lean`, `Ext_Svvptc = true` `PlatformConfig.lean:2225`) sits above. | STRONGER than the priv. prose (walker always sees own PTE stores, never stale beyond Sail's TLB); FAITHFUL w.r.t. riscv.cat IF one treats implicit reads as explicit — a modelling choice. | [OWN.39] [OWN.57] [OWN.66] [OWN.77] [OWN.87] [OWN.89] [OWN.115] [OWN.135] | The page-table export ("after the seal every entry is the sealed value up to A/D") holds for hardware whose walker is at least as coherent as an explicit load.  xv6 fences every table switch (`sfence.vma`), so no xv6 path relies on the strengthening. |
| 5 | **A/D-bit updates (Svadu).**  Priv. spec: when `ADUE = 1` the hart updates A/D "atomically", as if by an AMO; A-bit updates may be speculative (from memory, verify; [OWN.39] records this). | "Atomic with respect to other accesses to the PTE" is stated, but the update's place in `gmo` relative to the hart's other accesses is not. | Exclusive pair landing at once (`Lang.lean:1377-1381`, `:1389-1392`; design `:163`); Sail `update_and_write_pte` re-reads exclusively and asserts the conditional write succeeds (`Vmem.lean` ≈ :340-370, `internal_error "PTE conditional write failed"`); MachCSL blocks other harts' overlapping stores while the reservation is held (`othersReserve`, W-RSV); premise P2 `emNoDangle` (`Weak/GraphFetchBlocks.lean:87`) excludes dangling exclusive reads. | Pair/atomic: FAITHFUL.  P2: STRONGER than the platform (excludes a real two-hart first-touch race, plan SCOPE :518-522). | [OWN.19] (D19), [OWN.22] [OWN.23] (W-RSV), [OWN.39] | Runs in which two harts race to set A/D on one user PTE are outside the quantifier until P2 is discharged (plan: 0.5–1.5k, unverified). |
| 6 | **`sfence.vma` / `satp` / ASID.**  Priv. spec: `sfence.vma` orders prior PTE stores before later implicit reads of the same hart; `satp` writes need no fence for the next instruction's translation? (from memory, verify: an `sfence.vma` is required after changing `satp` unless the new table is unused). | Prose; ASID semantics (xv6 uses ASID 0) and the "implicit `sfence.vma`" cases are easy to misread. | Memory no-op (`Lang.lean:1397` `.tlbi`); Sail flushes its TLB (`InstsEnd.lean:18009-18030`); the sfence marker label `LFence false×4` is an inert graph item shared with `fence.i` (`WeakEvInst.lean:159`). | FAITHFUL w.r.t. riscv.cat (no data ordering); the ordering content lives in Sail's TLB flush. | Q7 route (a), [OWN.15], [OWN.87] (custody window `csrw satp` → `csrw satp`) | None for data; user-table facts are pinned to the `satp` switch windows, which is how xv6 actually orders things. |
| 7 | **I/O ordering vs main memory.**  Unpriv. FENCE: predecessor/successor sets `pr pw pi po`/`sr sw si so`; "device input/output operations are ordered only by the i/o bits" (from memory, verify); PMA chapter: "strongly ordered" I/O channels order I/O against I/O in the same channel only; `menvcfg.FIOM` makes i/o bits imply r/w.  Memory-model appendix condition "(c1)" (as quoted in plan §B(11b)) on dependency edges into I/O. | The spec's prose and `riscv.cat` diverge: `riscv.cat` has no I/O events at all; the prose's "observed by an external device" clause for FENCE has no formal counterpart; whether an MMIO access is a "memory write" (`W`) or an "I/O output" (`O`) for ppo rules 1–5 is not said. | Sail drops the i/o bits (`InstsEnd.lean:18299-18314`; `effective_fence_set` `BaseInsts.lean:568`, FIOM = 0 in xv6, `Xv6/SpecStart.lean:29,40`); I/O labels `LIo` are gmo events but not `R`/`W`, so rules 1–4 give them nothing (`gfenceCovers` `WeakRvwmoGraph.lean:235-239`), rule 5 does (`gacqPo :244`, D52), tagged (c1) dependency edges do ([OWN.17] D50); the rest is the TRUSTED residue (R1)/(R2)/(R2′)/(R3)/(R2″) (`GraphFabResidue.lean:116-143`); MachCSL: MMIO unbuffered at the event, no drain (`Lang.lean:1364-1367`, `:1382-1385`). | Graph model on fences with i/o bits: WEAKER than the spec (admits executions a `fence iorw,iorw` forbids).  Residue: STRONGER than RVWMO + PMAs — TRUSTED TEXT (QEMU-TCG-true).  Rule 5 to I/O: STRONGER (subsumed by (R1)). | [OWN.8] [OWN.12] [OWN.14] [OWN.16] [OWN.17] [OWN.18] [OWN.53] [OWN.116]; A4 (drop (R1)); bug #1 [OWN.127] [OWN.131]; [OWN.142] (keep (R1) until the capstone; SAIL-GAP-1) | (i) The theorem holds for platforms where every MMIO access is a one-way fence for the issuing hart (QEMU-TCG; many in-order SoCs), not for every RVWMO + PMA machine.  (ii) The model cannot distinguish fenced from unfenced MMIO sequences: the fix for bug #1 is not certifiable without (R1).  (iii) A4 as planned would leave the `fence iorw,iorw; NOTIFY; device reads ring` shape with no graph edge from the ring stores to the device read — the replay's fence head (row H2) waits for the landing, the landing gate waits for the device's stale read, the device read (H4) waits for NOTIFY: a stuck replay unless a fence-with-i/o-bits arm is added.  Verify (`Weak/SbOrd.lean:796,1059`). |
| 8 | **Interrupt delivery as an event.**  The ISA: interrupts/traps are not memory-ordering points; precise exceptions order the trap entry after prior instructions retire (Sail executes in order). | Where a PLIC pin delivery sits in `gmo`, and whether stores before the trap are visible to the handler's device accesses, is unspecified. | PLIC pin deliveries are I/O-class items in the hart row under (R1)/(R2) (plan §B(11) :2216 ff.: "EVERY RAM store po-before a PLIC pin delivery"); `takeException`/`returnException` are memory no-ops (`Lang.lean:1400-1401`). | Trap/xRET as no-op: FAITHFUL.  Delivery under (R1): STRONGER (an interrupt entry becomes a one-way store fence). | [OWN.8] [OWN.12] [OWN.96] (excRetR), [OWN.142]; [OWN.145] (s-a) (a proof-only "interrupts off" ghost record — a control fact, no ordering; EX-TRAP-1) | Handler code may assume all pre-trap stores of the same hart are visible to its MMIO accesses — true on QEMU, not promised by the ISA; xv6's handlers go through locks anyway. |
| 9 | **DMA / device writes to RAM.**  Outside RVWMO and Sail entirely; the virtio spec requires buffer data visible before the used-ring update; the PMA chapter speaks of coherence of I/O masters only informally (from memory, verify). | Silent. | Disk writes land at once at the top (`MState.storeDma` `Lang.lean:203-215`, zero-byte = no-op [OWN.30]); the disk row's program order is fabric order (`diskFabPo`, N11); used element only after the NOTIFY gate (`usedElemGateOk`, N12); sequential pf disk program [OWN.33]; one device row [OWN.18]. | OUTSIDE-SPEC (device model); sequential program STRONGER than virtio; `diskFabPo` STRONGER for pairs other than data→used-idx. | [OWN.29]–[OWN.34] [OWN.40] [OWN.43] [OWN.53] [OWN.93] | The theorem holds for a device that completes requests one at a time and writes RAM in program order; a device that reorders its DMA writes, or processes two requests concurrently, is outside the quantifier (follow-up after M2 per [OWN.33]). |
| 10 | **Mixed-size / misaligned accesses.**  Unpriv. "Memory Model" §: single-copy atomicity for naturally aligned accesses ≤ XLEN; misaligned may be split arbitrarily (`Zicclsm` only promises support); riscv.cat is per-access and has no mixed-size semantics; the appendix admits mixed-size is an open area (from memory, verify). | Underspecified by design. | Per-byte `rf` with ONE gmo position per load event (`gloadValue` `WeakRvwmoGraph.lean:300-306`); MachCSL reads all bytes at one view (`Lang.lean:1372-1376`); `candSca` ISA-faithful for aligned accesses (D20); Sail `Zicclsm = true` (`PlatformConfig.lean:2158`). | FAITHFUL for naturally aligned accesses (the kernel); STRONGER for misaligned user accesses (made single-copy atomic). | D20 [OWN.19], N10 | Kernel conclusions unaffected; a user program relying on torn misaligned accesses is modelled more strongly than the ISA promises. |
| 11 | **AMO `.aq`/`.rl`, rules 5–7.**  riscv.cat: rule 5 `[AQ];po;[M]`, rule 6 `[M];po;[RL]`, rule 7 `[RCsc];po;[RCsc]` with `RCsc = (Acq|Rel|AcqRel) & (EX|X)`; RCpc semantics informal. | RCsc vs RCpc and the "both bits" vs "either bit" reading of rule 7 misled the tree once (D35). | Rule 5 `gacqPo` (successor any `gmem`, incl. I/O — row 7); rule 6 OMITTED; rule 7 `grcsc` with `lbRcsc := aq || rl` ([OWN.54]); machine: `.aq` exclusive read sets the floor to the landed top, its write overtakes only same-epoch, non-overlapping pending entries (design `:155`, F-P-W1-1); `.rl` drains (xv6 has none, `LockFacts.amoCensus :74`). | Rule 7: FAITHFUL (after D35-fix).  Rule 6 omitted: WEAKER (sound direction; vacuous).  Exclusive-read same-address drain: machine STRONGER, harmless (design `:152`). | [OWN.13] [OWN.54] [OWN.110] [OWN.113] [OWN.114] | `acquire` = `amoswap.w.aq` with no trailing fence (`acquire+0x1c`): the whole lock discipline rests on rule 5 being read as "acquire read before everything po-later" — the standard reading. |
| 12 | **LR/SC, reservation sets, forward progress.**  A ext.: reservation granularity implementation-defined; SC may fail spuriously; constrained-LR/SC loops guarantee eventual success; atomicity axiom pairs LR with SC. | Platform-defined predicates; "dangling" LR (no SC) is allowed by the ISA. | Sail's `match_reservation`/`valid_reservation` are OPAQUE constants (`Xv6Extras.lean`, in the TCB `tools/tcb/expected.json` opaques); no LR/SC in the image; the walker's exclusive pair is the only user (row 5); P2 excludes dangling exclusive reads; rule 8 (`rmw`) OMITTED. | Opaque predicates: FAITHFUL ("every platform").  P2: STRONGER (row 5).  Rule 8 omitted: WEAKER (sound; vacuous). | [OWN.19] D19, [OWN.22]–[OWN.23] W-RSV, P2 | A future kernel using LR/SC would need rule 8 and a dangling-LR story; today only the walker is affected. |
| 13 | **Dependencies (rules 9–13) — syntactic, through registers; rule 12 `[M];(addr|data);[W];rfi;[R]`; rule 13 `[M];addr;[M];po;[W]`.** | The definitions of address/data/control dependency are syntactic and long; "control dependency orders only later STORES" (rule 11) is a frequent misreading; dependencies through CSRs are not defined (from memory, verify). | Graph: tagged edges `DTaddr/DTdata/DTctrl/DTtrans/DTr13/DTctx` from the emission (`AxDeps.lean` §1, §4); rule 12 over addr/data only (`gppo12T`); the untagged `gppo12` over `gdDeps` is marked UNSOUND and kept as the comparison model (`AxGraphCat.lean` header "RULE 12 GAP").  Machine: none tracked (`Lang.lean:1373-1377`). | Graph tagged: FAITHFUL (plus `DTctx`/`DTtrans` — STRONGER modelling choices for CSR/translation edges).  Machine: WEAKER (more runs). | [OWN.13] D33, [OWN.17] D50, [OWN.52], [OWN.73] (rule 11 certifies benign reads), [OWN.109] [OWN.141] | The theorem's quantifier is riscv.cat with tagged deps; the kernel proof never needs a dependency; a "sound by construction" machine would need tracking (B5 [B5.1]). |
| 14 | **Load value / store forwarding; rules 1–3.**  riscv.cat: a load reads the co-latest write that is gmo-before OR po-before it; rule 1 `[M];po-loc;[W]`; rule 2 `[R];po-loc-no-w;[R] \ rsw`; rule 3 `[AMO|SC];rfi;[R]`. | The po-before disjunct (forwarding) is easy to over-order (RVWMO⁻ did: `AxGraphCat.lean` header "THE POINT"). | `gvisible := gmoLt ∨ gpo`, co-max (`WeakRvwmoGraph.lean:295-306`); machine `readFwd` + per-byte coherence floors raised by FOREIGN sources only, reset at own stores (`TsoMem.lean` header, [OWN.20]–[OWN.23]). | FAITHFUL. | [OWN.17] [OWN.20] [OWN.21] [OWN.23] (W-COH) | Solid; litmus-checked. |
| 15 | **Rule 4 (FENCE) — which pairs, and `fence.tso`.** | `fence.tso` = `r,rw` + `w,w` is not expressible as one pr/pw/sr/sw tuple. | Graph label `(true,false,true,false)` = `fence r,r` (`WeakEvLang.lean:751`); machine: `fenceAcq` true, `fenceEpoch` true (W→W), no drain (`TsoMem.lean:502-516`, `:868`). | Graph: WEAKER (drops W→W; sound direction; vacuous — xv6 emits no `fence.tso`).  Machine: FAITHFUL. | — | None for xv6; fix before any other kernel. |
| 16 | **Load→load reordering, load buffering (LB), multi-copy atomicity.**  RVWMO: R→R to different addresses unordered without fence/dep; R→W unordered (LB allowed); the model is multi-copy atomic. | LB requires value speculation or promises to produce operationally. | Machine: stale views give R→R reordering (`TsoMem.lean` header); NO LB (loads in order) — a strengthening; one global order = multi-copy atomic. The cycle kill proves xv6 has no LB-shaped cycle (`Weak/SbLbFree.lean:70-78`). | No LB: machine STRONGER, FAITHFUL for the quantifier via the kill.  MCA: FAITHFUL. | [OWN.2] [OWN.5] [OWN.121] [OWN.123] | The theorem covers every RVWMO execution of THIS binary; the machine would not cover an LB-dependent program. |
| 17 | **The progress axiom / liveness.**  RVWMO: "no memory operation may be preceded in gmo by an infinite sequence of other operations" (from memory, verify). | Not in riscv.cat; not a safety property. | Out of scope (safety-only tree; plan SCOPE :556). | N/A (not modelled). | — | The theorem says nothing about termination, fairness or timing. |
| 18 | **CSR accesses to MMIO-like state (timer, `stimecmp`, CLINT).**  Zicsr: CSR accesses are not memory operations; Sstc puts the timer compare in a CSR. | Whether `mtime`/CLINT accesses are memory events is platform-defined. | CLINT/SIG/HTIF windows "are dispatched inside the Sail model and never reach the language" (`MachCSL/Dev/Fabric.lean` header); xv6 uses `stimecmp` (`Xv6/SpecStart.lean:29`). | FAITHFUL to Sail's platform; OUTSIDE-SPEC. | [OWN.45] (`wbootFacts`) | Timer interrupts arrive as Sail-internal events; no memory ordering is claimed for them. |
| 19 | **Power loss / reset.**  Not a memory-model item. | — | Single era, pending stores lost (design `:167`), [R2.2]. | FAITHFUL; scope limit. | D8 [OWN.19] | Power cycles are not covered (plan SCOPE :559). |
| 20 | **The riscv.cat transcription itself.** | Hand-transcribed into Lean from the Rocq port; no mechanised equivalence with herd's `riscv.cat`. | `rvwmoCatConsistentT` (`AxDeps.lean:299`) over `gppoCat6` + `gppo12T`; litmus-checked (`Weak/Litmus*.lean`). | TRUSTED TEXT (plan SCOPE :538-540). | [OWN.2] [OWN.13] | "RVWMO" in the theorem means this transcription; a herd equivalence proof is the discharge (XL, out of scope). |
| 21 | **Sail's cycle order (fetch → announce → execute).**  Implicit in the ISA; explicit only in Sail. | Whether a hart may fetch the next instruction while the current one's memory accesses are pending is exactly the spec's silence of row 1. | `sailCycleOrder` PROVED for every instruction under boot facts (`Weak/SailCycleOrderCycle.lean` header; [OWN.42]); `wbootFacts σ0` (device regions non-executable, `bootPMA` `MachCSL/Platform.lean:199`). | FAITHFUL to Sail; STRONGER than hardware prose (in-order). | [OWN.35] [OWN.42] [OWN.45] | Pipelined fetch is covered only through E1′ (row 1). |

---

## 3. Implications of the decisions taken so far (grouped; what each commits to, what if the spec reading is wrong, how bad)

Severity scale: **soundness** (the stated theorem could be false), **credibility** (the theorem is true but covers fewer
platforms/executions than "RVWMO" suggests, or rests on a text with no reference model), **proof work** (a stuck
replay or a re-proof, no change to the claim).

**A. The target is full riscv.cat RVWMO with tagged dependencies — [OWN.2], [OWN.13] (D33–D36), [OWN.54], [OWN.52].**
Commits the theorem to the transcription in `AxDeps.lean:299` as the meaning of "RVWMO".  If a KEPT rule is too strong
(adds a ppo edge the spec lacks — the known cases are rule 5 reaching I/O successors, D52, and `DTctx`/`DTtrans`
edges) the quantifier is smaller than RVWMO's: credibility, never soundness.  If a kept rule is too weak (rules 6, 8
omitted; `fence.tso` as `r,r`) the quantifier is larger: sound, and the kernel proof still had to cover those graphs.
If the transcription has an outright error in rules 1–4 (the lock discipline rests on them) the theorem could be
vacuous or false against real RVWMO — this is why the litmus suite and a future herd equivalence matter.  **Severity:
credibility (documented) today; soundness only through an undetected transcription error.**

**B. I/O ordering by a trusted residue — [OWN.8], [OWN.12], [OWN.14], [OWN.16]–[OWN.18], [OWN.53], [OWN.116]; A4
planned.**  Commits the theorem to a platform where every MMIO access (and every PLIC pin delivery) is a one-way fence
for the issuing hart's RAM accesses and the fabric serializes I/O — QEMU-TCG, not RVWMO + PMAs.  The spec reading
behind it (Sail drops i/o bits; `riscv.cat` has no I/O; PMA strong ordering is I/O-vs-I/O only) is CORRECT; the
residue is an honest, named strengthening.  If a reader insists on "every RVWMO machine", the theorem does not deliver
for any UART/PLIC/virtio path — **credibility, permanent for this binary** unless xv6 adds the spec's fences
(`fence w,o` etc.), which the model then still could not see (Sail).  **New point for A4:** dropping (R1) without
adding a faithful fence-with-i/o-bits ppo arm reintroduces executions the spec FORBIDS (the device reading ring
bytes the hart fenced with `fence iorw,iorw` before NOTIFY) into the quantifier; the replay would be stuck on them
(**proof work**, discovered late) — and if some premise were quietly widened to pass, **soundness** of the "device
never sees junk descriptors" conclusion.  Recommend a design check before A4 (§5).

**C. Fetch model and `fence.i` — [OWN.3], [OWN.6], [OWN.15], [OWN.26], [OWN.35], [OWN.42], [OWN.86], [OWN.101],
[OWN.137]–[OWN.139].**  Commits the theorem to E1′ (in-order fetch; a fetch's source precedes every later access of the
hart) and to (H1) (no forwarding into the fetch).  If the hardware reading is wrong for some core (a load satisfied
before an older fetch's source is visible), those executions are outside the quantifier: **credibility**.  The
machine's drain at `fence.i` is a strengthening bridged by proof ([OWN.139] (t3), 2–4k): **proof work** — [OWN.143]
removes the drain and passes `rv` into `itv` (re-proving the drain's consumers).  The
machine not enforcing E1′ and not passing `rv` into `itv` are weaker-machine facts: harmless for the bridge, but
they falsify any "texts hold by construction" claim (A5 F-A5-1, B5 §3) and they contradict (H2) as written in §B(11):
**documentation**.  [OWN.138] (r1) and [OWN.139] (t3) chose the FAITHFUL path over scope premises — good for
credibility, paid in proof work.

**D. Route P: per-address + fence-epoch store buffer, no load buffer, no dependency tracking — [OWN.110]–[OWN.114],
[OWN.123], [OWN.109], [OWN.141].**  Commits the machine's STORE side to exactly RVWMO's (rules 1 and 4) — FAITHFUL —
and its LOAD side to views without LB and without dependencies.  No LB: STRONGER, bridged by the cycle kill's
LB-freedom (`SbLbFree`): **proof work** if a new LB-shaped site appears.  No dependencies: WEAKER (machine admits
MP+addr), harmless for the theorem; only a future graph machine pays ([OWN.141]).  The exclusive-read same-address
drain: STRONGER, harmless (same rf/co, different mo witness).  If the spec reading of rule 4 for `pw ∧ sw` fences
("W→W only, no drain") were wrong, the buffer would admit too much — sound direction.  **Severity: proof work only.**

**E. Page tables, implicit accesses, P2 — [OWN.19] (D19), [OWN.22]–[OWN.23], [OWN.39], [OWN.57], [OWN.66],
[OWN.77], [OWN.87], [OWN.89], [OWN.104], [OWN.115], [OWN.132]–[OWN.135].**  Commits the theorem to "walker reads are the
hart's explicit loads" and "A/D updates are AMOs", plus P2 (no dangling exclusive read).  If the privileged prose is
read differently (a walker may read a PTE older than the hart's own un-fenced store — which the prose ALLOWS), our
model is STRONGER than the ISA: **credibility**, mitigated because xv6 fences every table change.  P2 excludes a real
race: **credibility** until discharged (0.5–1.5k).  [OWN.135]'s withdrawal of the kvminit premise was the right
soundness hygiene: a premise that papers over a proof gap is worse than a stronger model, because it hides the gap.

**F. Bug-list rule and the one program-step assumption — [OWN.127], [OWN.129], [OWN.131], [OWN.134], [OWN.135].**
Commits the theorem to a `drvOkGuard` step guard at `virtio_disk_init+0x170` (`Lang.lean:1383-1385`): WEAKER claim,
honestly named; correct spec reading (a RAM store and a later MMIO store are unordered without `w,o`).  Note that the
"fix" the list proposes cannot be verified by the present model (group B).  **Severity: credibility (named); the
rule itself is sound methodology.**

**G. Benign races certified by value/control arguments — [OWN.63], [OWN.64], [OWN.73], [OWN.112], [OWN.124].**
Commits to the reading "rule 11 orders a load before later STORES only" and to value facts (`ip->ref ≥ 1`, "a
non-holder never reads its own `lk->cpu`").  Reading is correct; the exempt pcs are replay artefacts (REVISIT item 1).
**Severity: proof work (A5 §6 S-R may retire the exemptions).**

**H. Devices — [OWN.18], [OWN.29]–[OWN.34], [OWN.40], [OWN.43], [OWN.93].**  Commits to the Lean device programs as
the devices, sequential disk, one coupled row.  Outside any spec; conformance tests (`notes/device-conformance.md`:
150 captures across QEMU/VisionFive 2/CVA6) are the only evidence.  **Severity: credibility ("for devices like
these"); a concurrent-queue device is a follow-up.**

**I. Scope rulings — [OWN.19] (D8 eight harts, D9 panics not excluded), single era, [OWN.93] witness to first UART
store.**  Not spec readings; they bound what the theorem says (no no-panic, no liveness, inhabited only to the
first console write).  **Severity: stated scope.**

---

## 4. Inconsistencies between our documents

1. `notes/weak-allocproc-routeP-design.md:161` (Zifencei row) marks the `fence.i` drain **FAITHFUL**; it is STRONGER
   (Zifencei orders fetches only; `riscv.cat` has no `fence.i` event).  Already called out by
   `notes/rvwmo-machine-examples.md:45-46` and `proposal-A5.md` §8.0 example 3; the design file is unchanged.
   **FIXED 2026-10-21:** "STRONGER today; being aligned to Zifencei per [OWN.143]".
2. `routeP-design.md:164` (I/O row) marks MMIO "FAITHFUL to RVWMO + PMAs (appendix (c1); Sail drops the i/o fence
   bits)".  Dropping the bits makes the model WEAKER than the spec on `fence iorw,iorw`/`fence w,o`; the row should say
   so and point to (R1) as the compensating STRONGER text.  Same for `Weak/SbCand.lean:33` ("`LIo` inert …
   FAITHFUL to RVWMO + PMAs").  **FIXED 2026-10-21** (design row + SbCand header; both cite SAIL-GAP-1).
3. `routeP-design.md:162` (`sfence.vma` row) says "FAITHFUL w.r.t. cat"; `riscv.cat` has no implicit accesses, so the
   mark is about a modelling choice (walker reads as explicit loads) that is STRONGER than the privileged prose.
   **FIXED 2026-10-21.**
4. Plan §B(11) (`notes/weak-allocproc-plan.md:1920-1922`) states reading (H2) as "`fence.i` completes the hart's
   earlier stores AND READS before later fetches"; the machine passes only `tv` and the own last landed store into
   `itv` (`MachCSL/Lang.lean:193-200`), never the read watermark `rv`; the graph text does include rf-sources
   (`GraphFetchSpike.lean:285-290`).  Three readings in three places.  **OPEN (plan reviser);** [OWN.143] makes the
   machine pass `rv` too.
5. Plan §B(11) / `GraphFetchSpike.lean:302-304` present E1′ as the fetch reading; the registered machine does not
   enforce it (fetch cut and data view independent, `Lang.lean:1368-1376`) — B5 [B5.s4] asked for one §B(11) line; not
   yet there.  **OPEN (plan reviser).**
6. `notes/xv6-weak-memory-bugs.md:13,20` records `fence iorw,iorw` as the ordering xv6 lacks and the fix; nothing in
   that note says the tree's model (Sail + graph) cannot see that fence's i/o bits and relies on (R1) instead — a
   reader would expect the fix to be checkable.  Add a sentence.  **FIXED 2026-10-21** (cites SAIL-GAP-1).
7. `notes/rvwmo-machine-examples.md:59-60` points to "pending decision Q-A2-2" (keep/remove the drain); [OWN.140]
   ("first do P", G-pv deferred) left it undecided — the note should say the decision is deferred to after the
   capstone (A5 §6 M-S2), not pending.  **SUPERSEDED and FIXED 2026-10-21:** [OWN.143] ruled "align now"; the note
   says "RULED [OWN.143]: align now".
8. Plan SCOPE `:553` calls misaligned user accesses "not excluded, not modelled faithfully"; more precisely the
   machine models them as single-copy ATOMIC (one view per access, `Lang.lean:1372-1376`) — STRONGER than the ISA,
   with Sail's `Zicclsm = true` admitting them.  **OPEN (plan reviser).**
9. `proposal-A5.md` §8.0 cites `kernel/trampoline.S:107` (not in tree; B5 noted); `notes/rvwmo-machine-examples.md:20`
   gives the right in-tree cite (`Xv6/KernelImage.lean:17614-17615`).  **OPEN** (`proposal-A5.md` lives in
   `~/dev/weak-orch/weakmach/`, outside the tree).
10. `routeP-design.md:154` and the SbCand header say `fence iorw,iorw` "= rw,rw in Sail"; the bug list and the
    design's DMA row (`:165`) then argue "xv6's `fence iorw,iorw` before every notify drains, so descriptors are landed
    when the device looks" — true in the MACHINE, but in the GRAPH only via (R1); A4's claim "P replays every xv6 shape
    using (R3) only" (`plan:344`) needs this shape checked explicitly.  **FIXED 2026-10-21 for the design rows
    `:154`/`:165`** (they now say "in the GRAPH only via (R1)" and cite EX-IO-1); `plan:344` OPEN (plan reviser).

---

## 5. Recommended actions

**Documentation fixes (no owner input needed).**
* Correct the three marks in `routeP-design.md:161,162,164` and `SbCand.lean:33` per §4 items 1–3.  **DONE 2026-10-21**
  (the SbCand I/O row is at `:34`).
* Add to plan §B(11): "the registered machine does not enforce E1′; `fence.i` raises `itv` past `tv` and the own last
  landed store only (not `rv`); the drain at `fence.i` is a machine strengthening (EX-FENCEI-1)".  **OPEN (plan
  reviser);** after [OWN.143] lands, the sentence becomes "`fence.i` is non-draining and raises `itv` past `tv`, `rv`
  and `pub`".
* Add to `notes/xv6-weak-memory-bugs.md` #1: "the model cannot see fence i/o bits (Sail drops them); the device-side
  ordering is supplied by the trusted (R1); the proposed fix is therefore not checkable by the present model".  **DONE
  2026-10-21** (with a SAIL-GAP-1 cross-reference).
* Update `rvwmo-machine-examples.md:59-60` (now "RULED [OWN.143]: align now", superseding "Q-A2-2 deferred to G2-S
  M-S2") and add this audit's rows 7/8 as EX-IO-1 (fenced NOTIFY shape) and EX-TRAP-1 (pin delivery as a one-way
  fence).  **DONE 2026-10-21.**
* In the final theorem's header, state the platform in plain words: "MMIO accesses act as one-way fences for the
  issuing hart (QEMU-TCG-like); fetch is in-order (E1′); devices behave as the Lean device programs".  **OPEN** — the
  final allocproc theorem's header is written by the capstone (W11-F); [OWN.142] confirms the QEMU-like MMIO sentence.

**Design checks before after-capstone items.**
* Before A4: a read-only spike (S, 1–2 worker-days) on the `fence iorw,iorw; NOTIFY; device descriptor read` shape
  under `ioResidue` minus (R1): is `noStuckP` provable from (R3) + `diskFabPo` + `usedElemGateOk` alone?  If not, A4
  needs the faithful arm of Q1 below.
* Before any "sound by construction" (G2-S) statement: decide F-A5-1 and the `rv` gap together (B5 §3).

**Owner questions (two).**

### Q-AUDIT-1 — How should the model treat `fence` i/o bits, and does A4 (dropping (R1)) stay as planned?

**RULED [OWN.142] (2026-10-21): (a) until the capstone** — keep (R1) (header: QEMU-like platform for MMIO); record
the Sail decode gap (SAIL-GAP-1, `notes/sail-gaps.md`); after the capstone, raise again with the NOTIFY-shape spike
and option (b).  Example: EX-IO-1 in `notes/rvwmo-machine-examples.md`.

*Where it sits.*  The I/O-ordering trusted text `ioResidueGmo` is the largest stronger-than-spec item in the theorem's
header; A4 plans to drop its hart-side arm (R1) after the capstone.

*Plain-language briefing.*  RISC-V's `fence` instruction has four kinds of operation it can order: memory reads (`r`),
memory writes (`w`), device inputs (`i`) and device outputs (`o`).  The spec says a store to RAM and a later store to a
device register are ordered ONLY by a fence that names `w` before and `o` after (`fence w,o`, or the all-in
`fence iorw,iorw` that GCC emits for `__sync_synchronize()`).  The official Sail model throws the `i`/`o` bits away
when it decodes a fence (`InstsEnd.lean:18299-18314`): `fence iorw,iorw` becomes `fence rw,rw`, `fence w,o` becomes
nothing.  Our graph model, built on Sail's labels, therefore gives device accesses NO fence ordering at all
(`gfenceCovers` `WeakRvwmoGraph.lean:235-239`).  To make the device model work we added the trusted text (R1): "every
RAM access before a device access is ordered before it" — true on QEMU, stronger than the spec, and it also quietly
provides the ordering the real fences would have provided.

*Concrete example.*  `virtio_disk_rw` stores the descriptors, executes `fence iorw,iorw`, then stores `QUEUE_NOTIFY`.
The device then reads the descriptors.  Spec: the device must see the descriptors (the fence orders `w` before `o`,
and the FENCE prose says no device may observe the successor before the predecessor).  Our graph model without (R1):
no edge from the descriptor stores to NOTIFY, so a graph where the device reads stale descriptors is "consistent";
the replay cannot reproduce it (the hart's fence waits for the stores to land; the landing waits for the device's
stale read to be replayed; the device read waits for NOTIFY by (R3)) — it gets stuck.  Today (R1) excludes that
graph.  Separately, xv6 bug #1's fix (`fence iorw,iorw` before `DRIVER_OK`) would change nothing in our model.

*Definitions.*  (R1): "a RAM access program-ordered before a device access of the same hart is ordered before it in
the global order".  (R3): device accesses are ordered as the fabric serializes them.  A4: plan item to drop (R1).
Stuck replay: the bridge cannot reproduce a graph, so the theorem's progress proof fails on it.

*What RVWMO / Sail / PMAs say.*  RVWMO + FENCE prose: i/o bits are the only RAM↔MMIO ordering; PMAs: I/O ordered
against I/O only; `riscv.cat`: no I/O events; Sail: bits dropped, `FIOM = 0`.

*Options.*
* **(a) Keep (R1) permanently; cancel A4.**  STRONGER than spec (QEMU-TCG platform), documented.  0 lines.  Credibility
  cost stays; the bug-#1 fix remains uncheckable.
* **(b) Add a FAITHFUL fence-with-i/o-bits rule and then do A4.**  Recover the fence's `pi/po/si/so` bits from the
  instruction word at the fence's pc (the image, not Sail's barrier kind), carry them in the fence label, extend rule 4
  to I/O endpoints when the bits say so, and give MachCSL a `fence w,o`-class drain.  FAITHFUL to the spec text
  (the device-observation clause stays a device-model text).  Estimate: 1.5–4k Weak + 0.5–1.5k MachCSL + the A4
  1–2.5k; confidence M.  Makes the bug-#1 fix checkable.
* **(c) A4 as planned (drop (R1), rely on (R3) + device texts).**  Risk: stuck replay on the NOTIFY shape (verify by the
  spike above); if a premise had to be widened to pass, that is a soundness risk for the device conclusions.

*Recommendation.*  (a) until the capstone; run the spike; then (b) if the owner wants the "every RVWMO machine"
sentence for I/O paths, otherwise (a) with the header sentence.

### Q-AUDIT-2 — `fence.i`: keep the machine's drain and the three-way disagreement, or align machine and text now?

**RULED [OWN.143] (2026-10-21): (ii) ALIGN NOW** — MachCSL `fence.i` becomes non-draining, `itv := max itv (max tv
(max rv pub))`, FAITHFUL to Zifencei; the drain's consumers (`FetchProg` row 6m, F-6m-1, the P-W6 fetch marker,
[OWN.139] (t3) scope) are re-proved on the MachCSL serial lane.  Supersedes the Q-A2-2 default and the
recommendation (iii) below.

*Where it sits.*  Row 1 of §2; EX-FENCEI-1; F-A5-1; the (H2) sentence in plan §B(11).

*Plain-language briefing.*  `fence.i` tells a hart "your later instruction fetches must see the code stores that are
already visible to you".  It is NOT a data fence: it does not make the hart's stores visible to other harts, and it
does not order the hart's later data loads.  Our proof machine makes `fence.i` wait until the hart's store buffer is
empty (a data effect the spec does not have — EX-FENCEI-1, stronger), while on the fetch side it moves the
instruction view past the hart's own stores but NOT past foreign code stores the hart has already loaded (weaker than
the "already visible" clause).  The graph text `gzFetch` is faithful on the second point and stronger on in-order
fetch (E1′).  None of this makes the theorem false; it makes the machine's `fence.i` different from both the spec and
our own text, which is confusing and will matter if we ever claim the machine is RVWMO-faithful by construction.

*Concrete example.*  Hart B stores new code at `y` and releases a lock; hart A acquires the lock (its data view now
includes `y`'s new value), executes `fence.i`, jumps to `y`.  Spec: A fetches the new code.  Machine: A's `itv` passes
its data floor `tv`, which the acquire raised past `y` — fine here.  But if A had merely LOADED `y` (no acquire) before
`fence.i`, the spec still says the fetch must see the new code; the machine lets the fetch read the old bytes (`itv`
ignores `rv`).  Harmless for xv6 (it always acquires), but a reader comparing machine and spec sees a gap.

*Definitions.*  Store buffer / drain / view as in the preamble.  `rv`: the highest position any of the hart's loads has
read ("read watermark").  `itv`: the view fetches read at.  E1′: see row 1.

*What Zifencei / RVWMO / Sail say.*  Zifencei: own later fetches see stores already visible to the hart; no data
ordering.  RVWMO: no fetch events.  Sail: `fence.i` is `Barrier_RISCV_i` with no memory effect (`InstsEnd.lean:18295`).

*Options.*
* **(i) Keep as landed; document (0 lines).**  Machine STRONGER (drain) and WEAKER (`rv`) in two different directions;
  theorem unaffected; the (t3) proof [OWN.139] carries the bridging.  Fix the §B(11) sentence and the design mark.
* **(ii) Align the machine to Zifencei now:** `fence.i` non-draining, `itv := max itv (max tv (max rv pub))`.  FAITHFUL
  to the spec text; 0.5–1.2k MachCSL (A5 M-S2) + re-proof of the drain's consumers (`FetchProg` row 6m, F-6m-1) in the
  middle of the capstone — risk of slip.
* **(iii) Defer (ii) to after the capstone (G2-S M-S2), with (i)'s documentation now.**

*Recommendation.*  (iii).
