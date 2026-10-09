VERDICT: NOT SATISFIED

# Review R7 of `notes/weak-allocproc-plan.md` rev 7 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R6's five required changes applied; (2) are the three folded-in spike designs SOUND as
premises/mechanisms of the published theorem (`ioObAcyclic`, `gzFetch`/`emZifencei`, `rvwmoCatAD`); (3) is
the plan launchable as written.  `file:line` cites `../xv6iris-weak` unless prefixed.  Advisory only; no
proofs or builds run; no git/jj.  Binding rulings [OWN.1–9] (`../weak-orch/allocproc_revise3_extra.txt`)
respected; [OWN.8] is under the plan's provisional [OWN.8-conflict] (D32).

## R6 application check (what NOT to re-litigate)

All five R6 items are in rev 7 and substantively right.  [R6.1] §A(3) quantifies over the TAGGED model
(`rvwmoCatConsistentT`, `AxDeps.lean:208-211` = `gwf ∧ gppoCatTGmo ∧ gloadValue ∧ gatomicity ∧ gtdepsWf ∧
gtdepsGmo`, re-confirmed), with `twCatT :876`/`twNotCatForget :883`, `rowDepsSubT :690`, header note `:12-18`;
the one-liner [R6.s1] is in.  [R6.2] W12b exists (plan:549-552); "the kill AND the walk floor" (plan:279);
the plan CORRECTED the spike's/R6's Cert3 line numbers to `311,391,428,468` (verified: `cinvReplay :311`,
`floorOfCgraph :391`, `certFloorOk :428`, `cpolRead :468`); `gvisUb` `Floor.lean:100-101`, `greadSrcUb :442-453`
(`gpolocGmo` at `:453`), `finvStep :605-619` (`hoacc` at `:619`) re-confirmed.  [R6.3] `devAcyclic` is gone
(grep: only the historical mention at plan:12,133); `gfexecConsistent'` is `Lin2.lean:761-762` as stated;
`ptraceRel :124`, `gtraceLinearizationMin :623`, `ptraceExistsF :836`, `trDevOrderedOfPtrace :944`,
`fconfSupply' :995`, `fconfTraceRealize :1012` all re-confirmed; W13 is XL in six pieces; D39 applied.
[R6.4] spikes marked DONE; W5b defines `execProgOk'S` + `pairAdjacent` on day one (plan:476-478); W2's `R`
carries `itv ≤ q`.  [R6.5] (a) `MachCSL/BootImage.lean:31` is `bootByte_zero` ✓; (b) `0x80000896` is the
`c.addi sp,sp,-16` entry (`KernelImage.lean:1515`), the `jal` at `:1590`, the first UART store `sb zero,1(a5)`
at `0x800008a0` (`:1525`; offset 1 = IER) ✓; (c) W3's `tcb/expected.json` decision stated (plan:448-449) ✓;
(d) W1's theorem shape stated, and [R6.5d-alt] is RIGHT: `PidEv.lean:136` is `pidPick`'s DEFINITION (`cycAt
pidmax (nextOf pidmax h) i`, `cycAt :132` = `(n-1+i) % pidmax + 1`), the file's lemmas are `cycAt_zero :158`,
`cycAt_period :179`, `pidPick_spec :200` — W1 proves the range ✓.

Spike scratch files re-read in full: `Weak/W13Spike.lean` (145; `lbExcluded :35`, `scDevExcluded :55`,
`scDevUnrealizable :66`, `ioOrd :88-92`, `ioObAcyclic :95`, `ioObAcyclicNodev :109`, `w13fIoOk :116`),
`Weak/CatOfMinusSpike.lean` (399; `rvwmoCatAD :31`, `catADOfCatT :37`, `grfiLex :60`, `racyDSplitC :97`,
`segPinCForward :178`, `cycleKillArmsC :218`, `csChainedC :318`), `../xv6iris-weak-w3/Weak/GraphFetchSpike.lean`
(226; `fetchCutOk :36`, `fetchCutPrefix :63`, `fetchCutEdge :83`, `fetchRelCut :140`, `gzFetch :189`,
`emZifencei :206`, `fetchPinCutOk :213`).  Plan cites into them are all correct.  The W12 design is sound as
stated: `grfiLex` uses rule 1 + load value only (`:60-87`); `catADOfCatT` feeds rule 12 over `gtAd` (`:37-42`);
`gcrossEGmo` needs `gwf` + lv (`:133-138`); nothing in the C-kit uses a dropped ppo rule.  The W5d-G design is
coherent: tags above `itv` are admissible (`ifetchByteOk … := logByte … ∧ ¬ writesIn log a t (max t itv)`,
`WeakPromise.lean:222-223`), so the cut form is STRONGER than the pf `elabOk` check (`WeakEvInst.lean:564`) and
is correctly an extra conformance clause, not a replacement; the single `fence.i` of the image is at
`0x8000609c` (`KernelImage.lean:17614`), immediately after `uservec`'s `jalr t0` (`:17612`) = the head of
`userret`, so "exec/fork → `p->lock` → `userret` `fence.i`" is real; TsoMem raises `itv` only on `fence.i`
(`MachCSL/Lang.lean:157-163`, `fenceIfetch`), matching (H2).  Disk DMA IS representable at the graph tier:
the disk agent is a ROW (`epsInit … ++ [.PDisk none]`, `WeakEvCapstone.lean:1026-1027`; `xboot`, `Capstone.lean:
90-91`; `nDiskDiskAgent`, `WeakLang.lean:384`) whose `pdiskProg` arms are START `LDev`, DRead `LLoad`, DWrite
`LStore`, DFence `LFence true true true true`, COMMIT `LDev` (`WeakEvInst.lean:480-507`).

## REQUIRED changes

**[R7.1] `ioObAcyclic`'s "I/O node → po-later READ" arm is OVER-STRONG: the strong model itself realizes
executions it excludes, and neither the kill nor the realization needs it.**  Evidence.  (i) The arm:
`ioOrd … | .dv i k, .ev y => (i,k) ∈ gfDev ∧ y.1 = i ∧ k ≤ y.2 ∧ gmem … y` (`W13Spike.lean:91`) orders every
memory event po-after an MMIO access gmo-after it, reads included.  (ii) The pf machine does NOT: `elabOk σ c
LDev = True` (`WeakEvInst.lean`, `def elabOk`, the `LDev` arm) — an MMIO step moves no view; TsoMem does NOT:
its MMIO arms are `devBytes … ∧ … σ' = { σ with devs := ds' }` (`MachCSL/Lang.lean:356-358,372-375`), `tv`/`hr`
untouched, so a plain load po-after an MMIO access still reads at any `tvn ∈ [tv, top]` (`:363-367`) — a STALE
value is a TsoMem behaviour, and the Xv6 Iris proofs are sound under it (they get no MMIO→load ordering from
TsoMem).  Concretely (xv6, panic path): hart B `pr.locking = 0` then MMIO prints; hart A, whose previous
`printf` character's MMIO is fabric-AFTER B's, later reads `pr.locking = 1` (stale).  In the graph: `st_B →
dv_B` (iopo-in), `dv_B → dv_A` (fabric), `dv_A → ld_A` (THE ARM), `ld_A → st_B` (`gfr`, by load value) — a
cycle, so NO `GT` satisfies the premise for this rf/co/fabric and the published theorem is silent about an
execution TsoMem, the pf machine and RVWMO hardware all produce.  (iii) Not needed: in `ptraceRel = po ∪ rf ∪
gmo|W` (`Lin2.lean:124`) a READ has no cross-hart OUT-edge (`fr` is not in the trace relation), so in the
(L) existence argument every po-run of a trace cycle still ends at a write (`gpow ⊆ racyD`, `Acyc.lean:
192-199`) or at a dev node (`iopo`-in), and the only `dv →` arm (L) and (K) consume is `dv → po-later WRITE`
(stores never early + dev steps in program order).  The arm `.ev x → .dv` for READS po-before the MMIO IS
realization-necessary (the read's trace step precedes the dev step) and stays.  Change: (a) in D32 add
option **(a′) `ioObAcyclic` with `.dv i k, .ev y` restricted to `gisW … y`** as the RECOMMENDED form, with (ii)
and (iii) as its justification; keep (a) as "the full-fence reading, excludes strong-model executions"; (b)
§A(†) (plan:139-144) and §B(11) (plan:405-408) describe the item in these terms: "a hart's memory accesses
po-before an MMIO access are performed before it; its STORES po-after are performed after it; MMIO accesses are
fabric-ordered"; (c) W13 (T)/(K)/(L) text (plan:570,574-579) notes that the kill composes in `tc ioOrd` with the
weak arm and that `w13fIoOk`/`ioObAcyclicNodev` re-prove by the same rank functions; (d) §B(11) names, under
either option, that the virtio path's own `fence iorw,iorw` ×4 (`KernelImage.lean:17300-17450`) is what
justifies MMIO→load ordering THERE and that the graph tier cannot express it (`LFence` has no i/o bits,
`WeakAxiomatic.lean:90`) — so with (a′) the virtio reads of `used->idx`/`b->disk` after the ACK MMIO are simply
unordered at the graph tier, exactly as in TsoMem.

**[R7.2] "Strongly-ordered I/O" / "PMA strong ordering" is the WRONG name for (T), and D37(c) does not
deliver it.**  Evidence: the plan (header plan:7 "strongly-ordered MMIO as on QEMU virt"; plan:142,406-408,
412; D37 plan:657-660; spike `W13Spike.lean:80-81`, `W13-spike.md:105-107`) labels the item "strongly-ordered
I/O, in program order".  RISC-V's "strongly ordered" PMA (Priv. spec, Memory Ordering PMAs) orders a hart's I/O
accesses within one channel AMONG THEMSELVES; it does NOT order them against main-memory accesses — that is
what the FENCE I/O bits exist for.  What `ioOrd`'s hart arms assert is "every MMIO access is a (one- or
two-way, per [R7.1]) FENCE between the issuing hart's main-memory accesses and the fabric" — a strictly
stronger, different property.  So D37's option (c) "restrict the claim to platforms with PMA strong ordering"
is NOT a way to obtain (T).  Change: (a) header one-liner: "plus an I/O-ordering PLATFORM assumption
(`ioObAcyclic`: MMIO accesses act as fences for the issuing hart's memory accesses and are fabric-ordered — not
an RVWMO or PMA guarantee)"; (b) §B(11) (plan:405-412) and D37: delete "strongly-ordered I/O"/"PMA strong
ordering" as the justification, rewrite (c) as "platforms whose MMIO path orders the hart's prior RAM accesses
before the device sees the access (QEMU TCG: program-order execution per vCPU + the BQL around MMIO), named as
a trusted assumption, host-dependent"; (c) [R6.s4]'s list of trusted USES (plan:412-414) gains the panic/`printf`
racy flags (`pr.locking`, `panicked`) as the sites whose coverage depends on the arm [R7.1] discusses.

**[R7.3] The disk agent's row is a FIRST-CLASS W13 object and the plan never says so.**  Evidence: the
capstone's rows are `xN σ0 = (epsInit σ0).length = NCPU + 1` (`Capstone.lean:94`), row `NCPU` = `.PDisk none`
(`WeakEvCapstone.lean:1027`), booted by `xboot` (`Capstone.lean:90-91`); its `LDev`s are the disk START and
COMMIT (`WeakEvInst.lean:483-486,500-503`) and its DMA writes are plain `LStore`s between them, drained by
the device-side `LFence true true true true` (`:497-498`) before COMMIT (`setDvirtio`).  Under `ioOrd` these
become dev nodes `(NCPU, k)` whose `iopo`-in arm ("DMA writes are performed before COMMIT moves the fabric") is
THE fact that makes DMA'd buffer data visible to a hart that observes the completion through the fabric — the
one place where (T) carries disk correctness.  The plan's W13 text (plan:569-590) speaks only of "hart `i`" and
MMIO; §A(†) says "xv6's MMIO accesses as I/O events" (plan:406); the W13-wit is UART-only and the plan's only
disk sentence is "without the disk row `exec("/init")` never completes" (plan:567-568).  Change: (a) (T)'s
prose: "I/O nodes are a hart's MMIO accesses AND the disk agent's START/COMMIT fabric moves; `i` ranges over
`xN σ0 = NCPU + 1` rows"; (b) W13 (I): the disk row's admin-only steps (START/COMMIT, and the malformed-chain
`LSilent` arm `:504-507`) are in `execProgOkA`'s scope; (c) W13 (W): a SECOND non-vacuity gate "first disk
START → DRead/DWrite → COMMIT" (device-active disk, the precondition of every user-fetch witness), distinct from
W13-wit; (d) §B(11): the DMA-visibility reading of (T) named as a trusted use.

**[R7.4] D18's residual "user-fetch witness = whole-boot replay (XL)" is not XL — it is INFEASIBLE by kernel
evaluation, and the published theorem therefore has NO planned non-vacuity evidence at allocproc.**  Evidence:
every candidate reaching `userinit → allocproc` (let alone `fork → allocproc` after user code, [OWN.3]) runs
`kinit`'s `freerange(PGROUNDUP(end), PHYSTOP)` first: `end = 0x80023b10` (`KernelImage.lean:17935`), `physTop =
0x88000000` (`Xv6/KallocDefs.lean:71`) — 32,732 pages, each `kfree` a 4 KiB `memset` (`Xv6/SpecMemset.lean:5-7`,
byte-granular), i.e. 10^7–10^8 dynamic instructions, far beyond `esil`/`pevrunAdmRun` kernel evaluation
(the W5c/W13-wit mechanism, plan:489-491, ≈ 100 instructions).  The plan's D22 is honest that W5c "certifies
NOTHING about reaching allocproc" and D18/W5d-G (plan:567-568,696-697) defer the witness as "(b) after M2 (XL)";
nothing in rev 7 can ever discharge it.  Consequence for (d): conclusion (b) ("every filed fork round …") and
the [OWN.3] coverage are, as planned, unsupported against vacuity — an xv6 expert will ask.  Change: (a)
re-state D18's residual as "not buildable by evaluation; options: (i) a symbolic/existence route — ONE
device-active TsoMem-side execution lifted to a conformant cat candidate (the (↑) direction for a SINGLE run,
not receptiveness; sized by W2's per-label table, D15 revisited); (ii) accept and state in the header that
non-vacuity is certified only up to the first UART store / first disk COMMIT; (iii) a reduced-RAM image variant
(leaves the `verified` branch, [OWN.4])" — owner question D44 below; (b) §A(5)/(b) carry the caveat until (i)
or (iii) lands.

## SUGGESTIONS

- [R7.s1] Length: 718 lines against the brief's ≤ ~400 ([R5.s2],[R6.s3] again).  D1–D31 and §B(9)'s (9a)–(9c)
  are RULED; move them to `notes/weak-allocproc-plan-appendix.md` and keep rev 8 to the statement, the gaps and
  the roadmap.
- [R7.s2] One list of NEW names in §A (`GfexecT`, `GT.gfGd`, `forgetF`, `xv6ConfS`, `gfexecConfA`,
  `execProgOkA`, `execProgOk'S`, `pairAdjacent`, `candSca`, `candKfetch`, `textPristine`, `gdFetch`, `emZifencei`,
  `gzFetch`, `rvwmoCoreD`, `rvwmoCatAD`, `ioObAcyclic`) — today only some carry "NEW"; W12/W13/W5b workers must
  not grep for them.
- [R7.s3] `GraphFetchSpike.lean` exists only in `../xv6iris-weak-w3` (its REPORT is merged as
  `notes/W5dG-spike.md`); make "merge the scratch (builds; `propext, Quot.sound`)" W5d-G's day-one step and
  cite the merged path.
- [R7.s4] W13 (T): spell out why `ioOrd`'s hart arms carry a `gmem` guard (fences are not in gmo, `gwf`,
  `WeakRvwmoGraph.lean:171`; spike R4) so (L)/(K) workers do not re-discover it.
- [R7.s5] W12's acceptance witness (SB+rfi-pos) is right; add to W12b's acceptance ONE forwarding read whose
  floor the old `gvisUb` would mis-state (the exact `finvStep` case), so gate 3's redesign has a check too.
- [R7.s6] §A line 36 "In the cone of the audited roots" — add the baseline's three opaques by name here as
  well (`tools/audit/baseline.json:11-14`: `xv6_resv_is_valid`, `xv6_resv_matches`, `bootImageSealed`); the
  header's "the three opaques" is otherwise unresolved for a reader of §A alone.

## Owner questions the plan is missing

- **D32 (revised, [R7.1]) — the form of `ioObAcyclic`.**  (a′) `.dv → .ev y` restricted to WRITES
  (recommended: implied by nothing the strong model lacks; sufficient for (L)/(K)/realization; keeps the
  stale-read-after-MMIO executions TsoMem and hardware produce IN the quantifier); (a) the spike's two-way form
  (MMIO = full fence; excludes them); (b)–(d) as in rev 7 (refuted).
- **D37 (revised, [R7.2]) — naming the platform assumption.**  (a) "MMIO acts as a fence for the issuing
  hart" named as such, QEMU TCG cited as the platform; (b) fence-guarded MMIO (i/o bits in `LFence` + a kernel
  change — leaves `verified`); (c) DROP "PMA strong ordering" as an option: it does not give (T).
- **D44 ([R7.4]) — non-vacuity past boot.**  (i) a single-execution existence theorem (TsoMem → cat
  candidate) as a Stage-2 item, sized after W2; (ii) publish with "non-vacuity certified to the first UART
  store and first disk COMMIT only" in the header; (iii) a reduced-RAM image for the witness only (not the
  published kernel).
- **D45 ([R7.3]) — the disk agent in (T).**  (a) one `Ioev.dv` kind for hart MMIO and disk fabric moves
  (recommended, matches `gfDev`); (b) a separate `dma` node kind with its own arms (clearer header, +S–M).
