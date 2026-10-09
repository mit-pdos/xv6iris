VERDICT: NOT SATISFIED

# Review R8 of `notes/weak-allocproc-plan.md` rev 10 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R7's four required changes and [OWN.10]–[OWN.15] applied; (2) is the [OWN.14] redesign —
MMIO as I/O-class graph events `Lbl.LIo`, the trusted inclusion `ioResidueGmo` (R1)–(R3) — faithful to
what RVWMO / the Sail model / Zifencei / the PMAs say, sound, and correctly sized; (3) does every owner
question meet the OWNER RULE (spec reading FIRST, each option marked faithful / stronger / weaker).
`file:line` cites `../xv6iris-weak`; ISA cites are `riscv-isa-manual` `main` (`src/unpriv/rvwmo.adoc`,
`src/unpriv/mm-explanatory.adoc` "I/O Ordering", `src/unpriv/rv32.adoc` FENCE, `src/unpriv/zifencei.adoc`),
fetched this round.  Advisory only; no proofs or builds; no git/jj; no subagents.

## R7 application check and what was verified (not to re-litigate)

[R7.1] (a′) RULED [OWN.12] and re-encoded as (R2) (plan:193-194); the dropped `dv → read` arm is dropped
(`ptraceRel :124` re-confirmed: a read has no cross-hart out-edge).  [R7.2] "strongly-ordered I/O" is gone
as a justification; D37 (c) dropped (plan:815-816).  [R7.3] the disk row is first-class ((a) plan:179-183,
(b) kinds `dev`, (c) gate 2 plan:720-723, (d) plan:203-204).  [R7.4] D44 RULED (i) → W14 (plan:732-744).
[OWN.10] GraphFetchSpike stays in `-w3` (plan:39-41).  [OWN.13]/[OWN.15] D33–D36, D39, D40 RULED (plan:802-827).
[OWN.14]: redesign in §A(†), §B(11), §C W13 (eight pieces) with D47–D50.

Code re-verified for the redesign (all cites correct unless noted below): `gwf`'s membership clause
`∀ e, e ∈ gxGmo ↔ gmem e` and its exhaustive `Lbl` shape arm (`WeakRvwmoGraph.lean:168-179`);
`gfenceCovers` requires `lbIsR`/`lbIsW` on both ends (`:190-194`), so I/O events get no fence edge by
construction under D47 (a); `gacqPo`'s `gmem e2` (`:200-201`) orders an acquire read before a later I/O
event once `gmem` covers I/O; `gppo1/2/3` and `grcsc` (`AxGraphCat.lean:146-163`) are footprint/RMW/aq-rl
based and skip I/O; `grule14 :255-256` is (R2)'s shape; `gpow` requires `gmem e` (`Acyc.lean:192-194`), so
(R2)-shaped pairs are ALREADY `racyD` obligations once `gmem` includes I/O (plan:193 says so);
`gloadValue`/`gfr` are `greadsByte`-based, `gmsg` is `lbWr`-based (`Lin.lean:461-468`) — vacuous for `LIo`.
Event LTS: MMIO arms emit `LDev` with `oib = none` (`WeakEvInst.lean:300-303,335-338`), `pstepPlic
:459-466` (hart row, `m' = m`), `pdiskProg :481-507` (START `:484`, COMMIT `:500-503`, DMA `LLoad`/`LStore`
`:487-496`, `LFence true true true true :497`), `pdiskUart :512-520` as an arm of `pstepDisk :522-526` — the
disk ROW; `elabOk LDev = True` (`:558`); TsoMem MMIO arms touch only `devs` (`Lang.lean:356-358,372-375`).
Bundle: `hemitf` HFone's realizing step carries the fabric move `da → dvo k` (`Fab.lean:238-247`), so an
`LDev` left-arm step needs no new mechanism; `gfDev`/`isDevBlock` clause (`:516-518,530`); `supplyOfFconf`'s
`hblkQ` (`:686-700`); `projLbl .LDev = none` (`WeakPromiseBridge.lean:537`), `PFDev :392-396`, `lbAdmin`
admits `.LDev` (`WeakAxRealize.lean:130-134`), `execProgOk' :373-386`; `dstepT` is inert on `LDev`
(`AxDeps.lean:461-463`); `rvwmoCatConsistentT :208-211`; `candShape` (`WeakAxiomatic2.lean:910-915`);
`promiseFreeCompleteClean` (`WeakAxiomatic3.lean:1433`), `srvwmoConsistent :2073`, `mstep`
(`WeakAxiomatic.lean:137`).  **Sail `execute_FENCE` claim: TRUE** — `InstsEnd.lean:18299-18313` matches on
`(extractLsb pred 1 0, extractLsb succ 1 0)` only; `(_, 0b00)` and the catch-all are no-ops; `fence.i` is
`Barrier_RISCV_i` (`:18295-18297`).  One precision the plan lacks: the sets first pass through
`effective_fence_set pred fiom` (`BaseInsts.lean:568-573`), which with `menvcfg/senvcfg.FIOM = 1` ORs the
I/O bits INTO the memory bits — never the reverse — so the claim "the i/o bits never produce I/O ordering" is
unconditional, while "they never reach `LFence`" holds because xv6 leaves FIOM = 0 (boot `menvcfg = 0`,
`BootBoard.lean:30`; xv6's `start()` sets only STCE).  Image: the four `0x0ff0000f` words at
`KernelImage.lean:17301,17311,17441,17451` (`0x80005c7a,c8a,d54,d66`); NOTIFY `sw zero,80(a5)` `:17315`,
`virtio_disk_intr` STATUS `lw a5,96(a5)` → ACK `sw a5,100(a4)` `:17439` → fence `:17441` — the §B(11b) path
audit is right; `ProofVirtioDiskIntr.lean:92-99` reads the fence as `Barrier_RISCV_rw_rw`.  **PMAs in this
tree**: the Sail `PMA` structure (`model/Lean_RV64D/LeanRV64D/Defs.lean:549-566`) has `mem_type`,
`coherent`, `read/write_idempotent`, … and NO ordering/channel attribute; the platform table `bootPMA`
(`MachCSL/Platform.lean:199-239`) types `[0x2000000, 0x12000000)` `IOMemory`, non-idempotent, and the
proofs consult PMAs only through `matching_pma_ram` (`PlatformFacts.lean:24`).  So "PMA ordering is prose"
is right, but the plan nowhere cites what the model DOES carry (see [R8.1]).

**ISA text, fetched.**  RVWMO chapter: "The interaction of the memory model with I/O memory, instruction
fetches (Ziccif), … sfence.vma is not (yet) formalized"; gmo is "defined over the primitive load and store
operations generated by memory instructions".  Explanatory appendix "I/O Ordering": "For I/O, the load
value axiom and atomicity axiom in general do not apply"; the ppo rules "still generally apply for accesses
to I/O memory" when one of five conditions holds — **(1) ppo as defined in the RVWMO chapter, "with the
exception that acquire and release ordering annotations apply only from one memory operation to another
memory operation and from one I/O operation to another I/O operation, but not from a memory operation to an
I/O nor vice versa"**; (2) overlapping addresses in an I/O region; (3) the same strongly ordered I/O
region; (4) either region on channel 1; (5) the same channel (except channel 0); then "To enforce ordering
between I/O operations and main memory operations, code must use a FENCE with PI, PO, SI, and/or SO, plus
PR, PW, SR, and/or SW", and "implementations must assume that the device may attempt to access memory
immediately after receiving the MMIO signal, and subsequent memory accesses from that device to memory must
observe the effects of all accesses ordered prior to that MMIO operation".  FENCE (rv32): "The EEI will
define which memory addresses … will be treated and ordered as device input and device output operations
respectively rather than memory reads and writes."  Zifencei: "ensures that a subsequent instruction fetch
on a RISC-V hart will see any previous data stores already visible to the same RISC-V hart"; "orders all
explicit memory accesses and instruction fetches that precede the fence.i … before all instruction fetches
that follow"; "An instruction fetch is always ordered before any explicit memory accesses that instruction
gives rise to"; does NOT order other harts' fetches.  (The privileged "Memory Ordering PMAs" section could
not be fetched verbatim this round; the appendix sentence above is the normative pointer it defers to.)

**Verdict on the redesign's faithfulness and soundness.**  (i) [OWN.14]'s premise — MMIO accesses are
ordinary load/store events in gmo, ppo applies, values device-supplied, outside load-value/atomicity — is
EXACTLY the appendix's "I/O Ordering" model.  (ii) D47 (a)'s by-construction choices are each on the
WEAKER (sound) side of that text except one: rule 5 over I/O (`gacqPo`'s `gmem e2`) is a strengthening the
appendix explicitly rules out (condition 1) — harmless only because (R1) subsumes it, as the plan says
(plan:188-189).  (iii) (R1)/(R2) are realization-necessary in THIS model: a cycle `io_A →po w →co w' →po
io_B →fab io_A` is a genuine posted-MMIO + store-buffer behaviour that no sequential-row trace reproduces
(B's `w'` is logged before `io_B`), so without (R1)/(R2) (L)'s existence fails — the plan's reading
(plan:496-499) is right, and the inclusion form covers the same executions as the old acyclicity form
(gmo is existentially chosen; a consistent position exists iff the extended order is acyclic).  (iv) (R3)
cross-channel issue order is residue (conditions 3–5 do not give it without channel PMAs the platform does
not declare) — plan:195-196 right.  (v) Risk R5 (I/O-entry / read-exit segments have no pin) is real and
honestly a STOP.  (vi) Sizing: `Lbl` arm files 69 (plan: 41 + 30 ✓); `lbIsMem` 39 files ✓; `Wlabel.LDev`
arm files 34–36 by grep, NOT 28 (plan:692) — the ~70-file total still holds.

## REQUIRED changes

**[R8.1] The OPEN semantics questions D41, D45, D46, D47, D48, D49, D50 do not meet the OWNER RULE, and
D48 mislabels its options.**  Evidence: plan:838-870 — none opens with what the RVWMO chapter, the Sail
model (file:line), Zifencei and the PMA rules say; D45, D46, D47, D49 carry no faithful/stronger/weaker mark
on any option; D48 (a) is labelled "PROSE-faithful" (plan:852).  It is not: under (a) the four `fence
iorw,iorw` (`KernelImage.lean:17301,…`) give I/O events NO ordering, while the FENCE text and the appendix
("code must use a FENCE with PI, PO, SI, and/or SO, plus PR, PW, SR, and/or SW") say they order I/O against
RAM both ways — (a) is WEAKER than the prose (sound direction) and faithful only to the Sail translation
(`InstsEnd.lean:18299-18313`, `BaseInsts.lean:568-573`); (b) is STRONGER than the prose for every fence
WITHOUT I/O bits (the locks' `fence r,rw`/`fence rw,w` would order MMIO) and faithful only for the four
`iorw` words; the prose-faithful option is D46 (b) (`emIoFence`), which recovers the bits from the
instruction word.  Change: (a) prefix EACH of D41, D45–D50 with one "Spec:" line stating, as applicable:
RVWMO chapter — I/O "not (yet) formalized", gmo over memory instructions' operations; appendix "I/O
Ordering" — the five conditions (quote condition 1's acquire/release exception verbatim), the FENCE
sentence, the device-DMA sentence; Sail — `execute_FENCE` (`InstsEnd.lean:18299-18313`) + FIOM folding
(`BaseInsts.lean:568-573`, FIOM = 0 at `BootBoard.lean:30`), MMIO as ordinary `mem_read`/`mem_write` routed
by `devAddr` (`Dev/Fabric.lean:122-123`), the `PMA` structure with NO ordering attribute
(`Defs.lean:549-566`) and the platform table's `IOMemory`, non-idempotent window (`Platform.lean:220-239`),
no device/DMA model in Sail (devices are MachCSL's, `Dev/*.lean`); Zifencei — the three sentences above (D41);
PMAs — strong ordering is among I/O accesses of one channel, never against main memory (the appendix's
FENCE sentence).  (b) mark every option faithful / stronger / weaker relative to that line, in particular:
D48 (a) "weaker than the prose, Sail-faithful", (b) "stronger than the prose except at the four `iorw`
words", and note that the prose-faithful form is D46 (b); D47 (a) "weaker on rules 1–3 for I/O (condition 2
is covered by the STRONGER (R3) instead)", (b) "faithful on rules 1–3 (condition 2), same executions once
(R3) holds"; D50 (a) weaker, (b) faithful (condition 1 says ppo 9–13 apply to I/O; the ctrl→I/O-LOAD edge is
NOT ppo under either reading); D41 — the plan's "(a) stronger" is relative to TsoMem's `itvPost`; relative
to the Zifencei TEXT ("any previous data stores already visible to the same hart" — including rf-sources of
plain loads and everything in the hart's view) both (a) and (b) are weaker-or-equal, i.e. sound — say so;
D45/D46/D49: the ISA is SILENT on device-internal events and on START/COMMIT (only the device-DMA sentence
speaks), so every option is "beyond the spec", stronger than silence, and the mark must say what each
adds.  (c) Costs AFTER the marks, as the rule requires.

**[R8.2] The device row's single sequential thread makes (R1)/(R2) couple DMA accesses with UNRELATED
UART/PLIC moves, and the plan names neither this artifact nor the pin-delivery stores in its per-arm
list.**  Evidence: `pdiskUart` (`WeakEvInst.lean:512-520`, UART tx/rx and the PLIC gateway) is an arm of
`pstepDisk` (`:522-526`), the SAME row as `pdiskProg`'s DMA `LLoad`/`LStore` (`:487-496`); under D49 (a)
(plan:858-860) each such move is an `LIo .dev` event of row `NCPU`, so (R1) says "every DMA read/write
po-before a UART byte move is gmo-before it" and (R2) "every DMA write po-after it is gmo-after it" — an
ordering between the virtio DMA engine and the UART that NO text gives (the appendix's device sentence
orders a device's DMA only after the MMIO it received), excluding genuine executions (a DMA write delayed
past an unrelated UART byte).  It is realization-necessary only because the MODEL serializes all device
threads into one row (Rocq deviation 5).  Likewise `pstepPlic` in the HART row (`:459-466`): (R1) orders
every pre-trap RAM STORE gmo-before the pin delivery — §B(11b) (F5) says a store "need not be performed"
(plan:492-493) and marks "pre-trap stores ✗" (plan:518), but the §B(11) per-arm list (plan:462-467) names
the pin deliveries nowhere.  Change: (a) §B(11) "Machine-model choices" (plan:474-477) gains "ONE sequential
device row for the disk program, the UART threads and the PLIC gateway — (R1)/(R2) therefore order DMA
accesses against unrelated device moves; a model artifact, stronger than any spec text"; (b) the (R1) list
gains "every RAM store po-before a PLIC pin delivery (`devintr` entry on all harts)" and the (R1)/(R2) lists
gain "the device row's DMA accesses around UART/PLIC moves"; (c) D49 gains option (a′): `dev`-kind events
from `pdiskUart`/`pstepPlic` carry (R3) only, with the honest note that (a′) is NOT realizable in the
current one-row device model (the trace must respect the row's po), so it costs a `WeakEv` row split
(M–L, owner-gated) — and mark (a) as the stronger-than-spec choice it is.

**[R8.3] §B(11b) cites the wrong ISA source for "what the ISA gives" and misses the one sentence that
grounds the virtio path.**  Evidence: plan:484-496 cites "Unpriv. §2.7" (FENCE) and "PMA strongly-ordered
channel" for (F1)–(F6) and says riscv.cat has no I/O; the RVWMO chapter itself says I/O is "not (yet)
formalized"; the ONLY ISA text that says which ppo rules apply to I/O is the explanatory appendix's "I/O
Ordering" subsection (five conditions + two sentences, quoted above), which the plan never cites.  Its
condition 1 settles (F4) (acquire/release do not cross memory↔I/O — so `gacqPo` over I/O is a named
strengthening, not "a reading"), condition 2 gives po-loc on I/O, conditions 3–5 give the channel order,
and the device-DMA sentence is the ISA-prose basis of the pre-NOTIFY `fence iorw,iorw` → device-reads-the-
descriptors path that §B(11b) currently attributes to the device MODEL alone ((F6), plan:494-496,505).
Change: (a) §B(11b)'s "What the ISA gives" opens with the appendix citation and lists (F1)–(F6) against its
conditions; (b) (F6) adds "the appendix's device sentence: after the MMIO the device's memory accesses
observe everything ordered before it — the NOTIFY fences' ISA reading; the device MODEL (`dmaView`,
`Dev/DevLang.lean:20-21`) is the stronger 'reads at the top' form"; (c) §A(†) plan:188-189 says "a
strengthening the appendix's condition 1 excludes; subsumed by (R1)"; (d) §A(†)/§B(11) add the FIOM clause
of the Sail claim ([R8.1]) in one sentence.

**[R8.4] Sizing line for W13 (E).**  Evidence: `grep -lE '(\| *\.?LDev\b|\.LDev\b)' Weak/*.lean` = 34
files (36 with `= LDev`/`LDev =>` forms), against "`Wlabel.LDev` arms in 28 files" (plan:692); the
`WeakRobust*` files (`WeakRobustMain/Trace/Sim/…`) and `AxFetch1/3`, `AxLock3*`, `AxRunGV2` use the
constructor and are missed.  Change: "~35 files"; the ~70-file total and XL verdict stand.

## SUGGESTIONS

- [R8.s1] §A(3) "I/O accesses are events of the rows [OWN.14]" could cite the appendix sentence "the load
  value axiom and atomicity axiom in general do not apply" as the ISA warrant for `lbRd = lbWr = none`.
- [R8.s2] The header's "the residue is what QEMU TCG gives and RVWMO + PMAs do not" is right; add "(and the
  one-row device model requires, [R8.2])" so a reader sees both sources of the residue.
- [R8.s3] W14: "TsoMem step → pf step at the SC-like view (`tvn := top`)" presupposes an SC-like run; say
  "choose the SC run (all loads at `top`) — SC ⊆ RVWMO makes the trace-order graph cat-consistent trivially",
  which also removes the `linCand`-style construction from the risk list.
- [R8.s4] D48 (b) is inconsistent with D47 (a) as written (`gfenceCovers` keys on `lbIsR`/`lbIsW`, which D47
  (a) keeps RAM-only); if (b) is kept as an option, note it needs a separate `lbIsIo` disjunct in rule 4.
- [R8.s5] The privileged "Memory Ordering PMAs" subsection should be quoted in §B(11b) once someone can
  fetch it verbatim (this reviewer could not); until then cite the appendix's FENCE sentence as the pointer.

## Owner questions the plan is missing

- **D51 (NEW, [R8.2]) — the one-row device model.**  Spec: RVWMO/riscv.cat/Sail are silent on device
  threads; the appendix orders a device's memory accesses only after the MMIO it receives; the UART and the
  virtio DMA are unrelated agents.  (a) keep ONE device row and NAME the (R1)/(R2) coupling as a model
  artifact (stronger than the spec; zero cost; recommended for this plan); (b) split `pdiskUart` into its
  own row(s) so (R1)/(R2) bind only START/DMA/COMMIT (faithful to the spec's silence; `WeakEv` row count
  `xN` changes, `Capstone.lean:94`; M–L, owner-gated, after W13 (E)).
- **D52 (NEW, [R8.1]) — rule 5 over I/O.**  Spec: appendix condition 1 — acquire/release do NOT order
  memory↔I/O.  (a) keep `gacqPo`'s `gmem e2` as is (stronger than the text; subsumed by (R1), so no
  coverage change; zero cost; recommended); (b) add `¬ gisIo e2` to `gacqPo` (faithful; touches the cat
  arms and `cyBackwardNotAq` `Cert4.lean:588`; S–M).
