# PROGRESS — AxSpinT2Spike (Theorem 2, certificate (a′) de-risking spike)

Notes draft, 2026-10-08.  File: `Weak/AxSpinT2Spike.lean` (Lean-only, fully proved, no sorry/axiom/
native_decide; `lake build Weak.AxSpinT2Spike` on the VM: **261 s**, of which ≈ 124 s `obs1Lit`
(the tracer) and ≈ 127 s `chk1` (the drive + checks); everything else ≈ 10 s).  All times below are
kernel evaluations on the c4d VM, measured with `#kernel_eval` in scratch files (NOT in the tree;
copies, the Nat-dump decoder `dec.py`/literal generator `gen.py` and the decoded 3-hart rows
`row3.json` in the session scratchpad `w3/`), unless they say "build".

Design questions: `notes/weak-lb-thm2-design.md` §E Q-T2-6, Q-T2-7, Q-T2-8, "jrun and warm start".

## The instance

Hart 0 enters at allocproc+0x38 (`auipc a0,0x11`, first instruction of the inlined allocpid) with
`s1 = &proc[0]`, `sp` in stack0's 2nd page, `tp = 0`, SIE = 0, `satp` → the new table `tX`, and a
PRESET warm TLB `tlbW`; memory = real kernel text + table words + `nextpid = 1`, all other RAM 0.
The run is 466 instruction steps (acquire with push_off/mycpu/holding, the amoswap.w.aq claim,
the 64-slot pid scan, the nextpid/p->pid stores, release with holding/fence/pop_off, `li a5,1;
sw a5,24(s1)`) and stops at allocproc+0x9c with `a3 = 1`, `nextpid = 2`.  Row: **135 items**
(98 loads, 35 stores, 1 RMW, 1 fence) = 134 graph memory events.  (Design §A.6 guessed ≈ 230
instructions / ≈ 133 events: the event count is right, the instruction count is 2×, because the
64-iteration scan alone is 4 × 64 = 256 instructions.)

## Q1 (Q-T2-6 + warm start) — tracer: WORKS; cost measured

* `AxScRun3.jrun` runs the whole segment unchanged from a warm state; the warm state is just a
  register file whose `tlb` register is preset (`regsE`), so no tracer plumbing was needed (the
  "jrun and warm start" risk is CLOSED).  `lit1NoWalk`: no row item touches a table page.
  Justification of the preset: `tlbWOk : tlbOk tX tlbW` (MachCSL TLB invariant) and, measured, a
  COLD run of the same segment fills 11 TLB slots that are entry-for-entry identical to `tlbW`'s
  (cold row: 168 items = 135 + 11 walks × 3 reads; 123 s).
* Cost, 1 hart: **124 s** per evaluation (`#kernel_eval`; the `decide +kernel` in the build is the
  same).  Not linear: 20 steps 2.0 s, 60 steps 7.2 s, 120 steps 18 s, 250 steps 49 s, 466 steps
  124 s (0.10 → 0.27 s/instruction).  A flat register-overlay tracer (deduplicated written
  registers instead of the `RegFile.set` closure chain) had IDENTICAL cost at 20/60/120 steps, so
  the register chain is not the cause; the 32-bit instructions of the scan and the growing
  `TMem.set` write chain (every fetch looks up through it) are.
* Cost, 3 harts serial (A, B, C, each 466 steps, slots proc[0..2], stacks in pages 0x8000b-d):
  **664 s (11 min)**, i.e. ≈ 1.8× the 3 × 124 s; rows 135/135/135, il 402, pids 1/2/3, nextpid
  stores 2/3/4, every hart ends at allocproc+0x9c.  With fetches answered from the IMAGE instead of
  the write-chained memory (`jtrI`: `AxScRun3.jtr` with one line changed; untrusted, so no proof
  obligation; outputs checked IDENTICAL to `jrun`'s for 1 and 3 harts): **94 s** (1 hart) and
  **362 s = 6 min** (3 harts, now ≈ linear).
* The literal trick WORKS on the whole run: `obs1Lit` ties `AxScRun3.jrun` to the pasted literal
  `lit1Row`/`lit1Il` (+ final pc, a3, nextpid) in ONE `decide +kernel` (≈ 124 s build); every
  later check runs on the literal (`lit1Facts`, `lit1NoWalk`, `shil1`, `gT1Vals`: ≈ 5 s together).
* PITFALL (cost me 25 min): `#kernel_eval` of a large STRUCTURED result is quadratic — its
  printer calls `Kernel.whnf` per constructor argument with a fresh cache, re-running the tracer
  for every list cell.  Recipe used instead: encode the whole output as ONE `Nat`
  (`foldr (acc * 2^32 + d)`), `#kernel_eval` it (one evaluation), decode offline (Python, 30
  lines) into Lean literal syntax.

## Q2 (Q-T2-7) — consistency / ctrl closure: generic lemmas APPLY; checks are cheap

* `graphOfScCatT` (AxScRun, built on AxScCat's `scGraphCatT`: SC interleavings are consistent)
  and `graphOfScCtrlClosed` apply directly: `cat1 : rvwmoCatConsistentT gT1`, `ctrl1 :
  ctrlClosed gT1` — NOTHING is decided on the graph.  What is decided are the B-checks:
  `shapesOkB && ilOkB` on the literal (< 5 s incl. `valsOkB`), and `emsOkB` + `ctrlOkB` on the
  drive's emission.
* `drive2` on the graph's own row (from `regsE 0`): reaches the row end; **100 s**; emission
  **30 920 items** (136 positioned).  `emsOkB` + `ctrlOkB` on top: **+27 s** (127 s total =
  `chk1`); `gdepsOf` (260 deps) +9 s.  `run1` (the `tierAAstep` RUN premise) then follows from
  `runGraphOfSc` at no cost.
* Quadratic?  `coverB` is O(#row writes × |emission|) PER HART (37 × 31k here); emissions are
  per hart, so over 3 harts the checks grow linearly (≈ 3 × 27 s).  No blow-up; the drive (a
  second evaluation of the real `riscvStep` per hart) dominates.  The design's fear (Rocq
  `ctrl_okb` 16–36 s) is about this size: fine.
* PITFALL: a proof that `match`es / `cases` on `drv1` made the KERNEL re-evaluate the drive
  (97 s extra) — the kernel's whnf of `casesOn drv1` reduces the major premise.  Fix used:
  `chkOf rows o` / `emsOf o` are functions of a variable drive result, `chkOfFacts` is proved for
  a VARIABLE `o`, and `chk1Facts := chkOfFacts _ drv1 chk1` (no evaluation).  Likewise
  `gtGEms`/`gdGEms` (graph part independent of the emission) are proved for a variable emission:
  a direct `rfl` against `ems1` evaluates the drive.

## Q3 (Q-T2-8) — page table: did NOT exist; built (S, ≈ 120 lines, in the file)

* None of the existing tables covers Theorem 2's data: `AxSpinE8f.tT` / `AxSpinSpikeRun`'s table
  map only pages 0x80000/0x80001, and their table pages sit at 0x80010-0x80012 — page 0x80012 is
  pid_lock / cpus / proc[0] in this kernel, so they cannot simply be extended.  `AxSymCtl3.pT`
  (AxDataX8/AxWalk4) is the same probe table (pages 0x80000/1), A/D variants for walker
  experiments, not kvmmake.  `Xv6/KvmCounts.lean` describes kvmmake's tree only abstractly.
* Built: `tX` — identity map of KERNBASE..`end` (36 pages, one L0 table), text pages (< etext)
  `KPerm.rx`, the rest `KPerm.rw`, leaves `kLeaf ppn perm 1 1` (A/D PRESET), pointers `kPtr`,
  table pages 0x87fff/0x87ffe/0x87ffd (top of RAM, where kalloc starts).  Proved: `tXWalk` (MachCSL
  walk of every page), `tXMaps` (`AxPtProt.ptreeMaps` for EVERY mapped page: pid_lock 0x80012,
  nextpid 0x8000a, cpus 0x80012, proc[] 0x80012-0x80018, stack0 0x8000a-0x80012, text 0x80000-6),
  `tlbWOk`, `satpXFacts` (mode/ASID/ppn premises as in AxSpinE8f).  Elaboration ≈ 3 s.
* Honest deviations from kvmmake: no device/trampoline/kstack mappings; data map stops at `end`
  (kvmmake: PHYSTOP); A = D = 1 preset (kvmmake leaves 0; Svadu write-back is excluded by the HAD
  scope of the theorem).

## Recommendation for AxSpinT2c

1. Import (or move to a shared `AxSpinT2x` base) this file's `tX`/`tlbW`/`mem0`/`img`/`regsE`;
   `regsE h` already parameterises the hart, slot `proc[h]` and stack page.
2. Schedule A×466, B×466, C×466 (serial; verified: pids 1/2/3, no collision branch).
3. SPLIT T2c into modules so lake builds them in parallel (the literal makes them independent):
   `T2cRows` = the 3 literal rows + interleaving (generated by the Nat-dump recipe) and ONE tie
   theorem against the tracer (11 min with `jrun`, 6 min with the image-fetch variant `jtrI` —
   recommended; add it next to `AxScRun3.jtr` as a Lean-only tracer);
   `T2cDrvA/B/C` = one `chkOf` decide per hart's drive on the 3-hart graph's row (≈ 2.1 min each,
   importing only the literal, not the tie); `T2c` = the capstone application (cheap).  Wall
   time ≈ max(tie, drive) ≈ 6 min instead of the sum (≈ 12.5 min sequential with `jtrI`, 17.5
   with `jrun`).
4. Keep every proof that mentions an expensive constant (`drvX`, `jres3`, `emsX`) generic over a
   variable (the `chkOfFacts` / `gtGEms` pattern) — otherwise each such proof silently pays a full
   re-evaluation.
5. Use the generic `graphOfScCatT`/`graphOfScCtrlClosed`; do not decide `rvwmoCatConsistentT` or
   `scGraphB` on the 400-event graph.
6. Graph-value pins (Option V / Q18b) are cheap on the literal (`gT1Vals` style, `sim` over the
   rows: seconds).

## Open questions

* Q-a: is the tie theorem needed at all?  The rows are only an input to `graphOfSc`; soundness
  comes from `drive2` (which re-runs `riscvStep`) — the tracer only GENERATES the literal.  If
  T2c's statement never mentions `jrun`, the 11-min tie can be dropped (keep it in a separate,
  optional module as provenance).  Recommended: drop from the critical build, keep as an optional
  module.
* Q-b: the image has only text/table/nextpid non-zero; T2c's `Himg` premises (lock word 0,
  `proc[j].pid` ≠ candidates) hold on it, but if the capstone wants the REAL `.data` image a
  bigger `imgByte` is needed (cheap: one more range).
