VERDICT: NOT SATISFIED

# Review R21 of `notes/weak-allocproc-plan.md` (rev 24)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj).  Every cite below was read
at the working-copy tip.

## What was checked and holds

- **[R20.1] applied correctly.**  `pre₁` is the status `pre` cut off before capture's `modify` (`Virtio.lean:517-518`).
  It runs the in-flight pre-check, then `setPhase .fetched` (`:526`), then the `taken` guard (`:529`, which sets
  `taken := some h` when it passes).  That text is at plan `:1316-1330` and again at `:1510-1527`.  The commutation claim
  checks out against the code.  `pre₁` reads and writes only `inflight` and `taken`.  A non-reset `write`
  (`Virtio.lean:291-325`) touches only `cfg` or `isr` (`offQueueNotify` is `some v`), and `read`
  (`:268-289`) reads only `cfg`, `isr` and `cap`.  So hart MMIO reads return the same value on both sides.  A reset
  (`:260-262`) keeps `disk` and `cap`, and the pre-check's identity arm absorbs it.  One formula covers the free, held
  and reset cases.
- **[R20.2] mostly applied.**  `DmWf` keeps `n ≠ 0` (`:1490-1491`), the `n = 0` disjunct is gone from (M5′)
  (`:1470-1472`), and the elision matches today's `dreadData`/`dwriteData` (`VirtioProg.lean:358-366`).  One step count
  is wrong: see [R21.3](a).
- **[R20.3] applied.**  `Weak/RvwmoXv6ScaT.lean` is 792 lines.  `linCandScaT :757`, `linCandScaTCatT :780` and
  `linCandScaTMinus :787` are present, and the file is imported at `Weak.lean:632`.  The Names lists are fixed
  (`:321-347`).  But the consumption sentence R20.3 introduced is wrong: see [R21.2].
- **[OWN.35] recorded.**  The ruling is reflected in §A `:272-273`, §B(11) `:915-922`, §C W-SCO `:1704-1711` and §D
  Q-FIARM `:2241-2302`.  `MachOfPf.Hyps.fi` (`:635-643`) has exactly the stated content.  The fact itself looks true of
  the Sail model:
  - `run_hart_active` (`Step.lean:331-404`) is fetch, then `instr_announce`, then `execute`;
  - no `execute_*` uses `InstructionFetch` (grep of `LeanRV64D/*.lean`: only Fetch/PMA/PTW/PMP sites);
  - `ebarNow` is `none` only for `Barrier_RISCV_i` (`WeakEvLang.lean:733-745`), so no other barrier emits
    `LFence false×4`;
  - `fence 0,0` emits nothing (`InstsEnd.lean:18313-18314`).

  The vacuity risk from a false premise is therefore low.  The wording of the premise is a suggestion, [R21.s1].
- **W-DMA0 landed as recorded.**  `MState.storeDma` has the `n = 0` split inside its two moving fields
  (`MachCSL/Lang.lean:181-183`), with `storeDma_zero :186` and `storeDma_of_ne :191`.  The `hzero` obligations are at
  `WpDevDisk.lean:156`, `WpDevDmaStep.lean:139,157` and `WpDevDmaStepV.lean:126,143`.  `WpDma.lean:70,124,150` take
  `hn : n ≠ 0`.  The plan honestly names the deviation from the ruled wording of (A).
- **W4 F1–F8 landed as recorded.**  `Weak/MachOfPf.lean` is 1659 lines.  It contains `SimRel :305-322`, `Hyps
  :620-660`, `simRun :1497` and `machRunOfPfRun :1535`, plus `winPristine`/`cutOfPristine :1559,1588`.
  - The W5 discharges exist.  `cutOfPristine` uses only `SimRel.pow`/`.mem`/`.auth`.  `xv6TextAdequacy_closed`
    (`Xv6/LinkTextAdequacy.lean:26-31`) gives `Reducible ∧ (pow → textPristine)` at every reachable state.  That
    yields HSafe and `winPristine` directly (through `textWin_get`).
- **(b) The TsoMem–sRVWMO claim matches the code as worded.**  sRVWMO is RVWMO plus rule 14 (stores never early), with
  rules 6, 9 (load half) and 12 omitted (`WeakAxiomatic3.lean:2052-2084`).  §0 F1 names TsoMem's extra strengthenings:
  reservation serialisation until W-RSV, and DMA reads at the top as a device-model item.  It says honestly that
  nothing in Lean relates TsoMem to `srvwmoConsistent`.
- **(a)** spot-checked: `Xv6.Allocproc` at `Xv6/LinkAllocproc.lean:14-16` (parametric in the six callee interfaces).
  The `xv6FsAdequacy_closed` baseline at `tools/audit/baseline.json:11-14` lists the three opaques, with roots at
  `roots.txt:6-8`.

## REQUIRED changes

- **[R21.1] W8 is in the launch set but is not launchable as written.  Its file lane contradicts the plan's own
  serial-MachCSL discipline, and its export statement is not pinned.**
  *What is wrong (evidence).*
  - §C W8 (`:2131-2141`) says W8 exports "per reachable MachCSL state (the `mmOk` idiom)" through "a ledger threaded
    through the MachCSL memory rules — mechanical but wide".  `mmOk` lives in the state interpretation
    (`MachCSL/Resources.lean:779-785`, inside `memModelAt :938-951`), and every memory rule (`Wp`, `WpAtomic`, `WpDma*`)
    maintains it.  A sibling ledger means editing those rules and rebuilding the whole `Xv6` cone (≈ 0.73M lines).
  - §B(12) (`:1010`) instead classes W8 as a "pure-`Xv6/` item".
  - §C "THE THREE SERIAL MachCSL items" (`:1712-1721`) does not list W8.  Yet W-RSV, the serial item after M1, rewrites
    exactly `Wp.lean`, `WpAtomic.lean` and `Resources.lean`, and re-threads 25 MachCSL files plus 12 `Xv6/` files
    (`:1798-1878`).
  - Nevertheless the launch set (`:1047-1048`), Status (`:2190`) and D26 (`:2819`) launch W8 now, in parallel, "at the
    coordinator's discretion".
  - The export's form is D24, which is only a provisional recommendation (`:2809-2811`), and no statement skeleton
    exists.  W8 (L–XL) would design its own interface for consumers years away: W11 (i) `badSeg` and (ii) `protReg`,
    both read through `R`'s log identification (`:2155-2163`).
  - W8's Deps line is stale ("the composition `pfStepTso` pending", `:2145-2146`; it landed).

  *Exact change (§C W8, §B(12), §C top launch set, Status, D26).*  Replace "∥ W8 (… launch at the coordinator's
  discretion — L–XL)" with "∥ **W8-design** (S, read-only)".  W8-design pins two things:
  1. **The export statement.**  A Lean skeleton over `MState`'s per-byte histories (`HEnt.tid`/`HEnt.t`) and the author
     log, for (i) ownership, (ii) lock-protected access and (iii) no foreign owned-unpublished message.  It must be
     checked against how W11 (i)/(ii) will consume it through `rmem`'s `R-log`/`R-hist` (`PfStepTsoMem.lean:57,62`).
  2. **The lane.** Either:
     - (α) a state-interpretation ledger, in which case W8 becomes the FOURTH serial MachCSL item.  It must land before
       M1 closes (so W-RSV rebases on it), or else run after W-RSV.  The order must be stated.
     - (β) a form that needs no MachCSL rule edits, D24's (c), "trace-free from W9a's check + ownership facts"
       (`:2811`).  Only then is W8 an `Xv6/`-only parallel item, as §B(12) says.

  W8 proper launches after W8-design is reviewed.  Also fix the stale Deps line.  See the owner question Q-W8-lane
  below.

- **[R21.2] The Stage-2 consumption of `linCandScaT` is mis-stated.  `grule14` does not hold on the published graph.**
  *What is wrong (evidence).*
  - §B(10) `:753-756` and §C W11 (iv)b `:2167-2168` say "W11 (v)/W13 (L) consume `linCandScaTCatT :780` on `GT.gtG`".
    That theorem needs `grule14 GT.gtG` (`RvwmoXv6ScaT.lean:780-781`).
  - `grule14` is "every memory event po-before a write is gmo-before it" (`WeakRvwmoGraph.lean:266-267`).  That is
    exactly the sRVWMO residue the published quantifier ALLOWS to fail: "W→W reordering and load buffering ALLOWED",
    §A(3) `:232`.  On a cat-consistent LB or W→W-reordered `GT` the hypothesis is false, so the stated consumption is
    unusable.
  - The same paragraph says "on the linearized graph" (`:754`).  That is the right graph: rule 14 holds there by
    construction (`normalizeOfAcyclic`'s conclusion `grule14 GD'.gdG`, `WeakRvwmoTopo.lean:596-605`).
  - The file header itself names `linCandScaTMinus` as the corollary for "the current chain's `normalizeOfAcyclic`
    output" (`RvwmoXv6ScaT.lean:36-37`).
  - Under the cat chain, the normalized `GD'` must also give `gppoCat6Gmo` (or RVWMO⁻).  W12 (1) restates
    `normalizeOfAcyclic` "over the core" `gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf` (`:1912-1914`), and lists no ppo
    conclusion for `GD'`.  So the premise `linCandScaT` needs at Stage 2 has no producer in the roadmap.

  *Exact change.*
  - In §B(10) `:755-756`, §C W11 (iv)b `:2168` and §D G1-Q `:2554`, replace "consume `linCandScaTCatT :780` on
    `GT.gtG`" with: "consume `linCandScaT :757` (or `linCandScaTMinus :787`) on the NORMALIZED hull graph `GD'` from
    `normalizeOfAcyclic` (rule 14 by construction); `linCandScaTCatT` is a statement about the input graph and is not
    on the Stage-2 path".
  - Add to W12 (1)'s deliverables: "the restated `normalizeOfAcyclic` ALSO concludes `gppoCat6Gmo GD'.gdG` (the topo
    order extends the cat chain's `racyD`, which must contain `gppoCat6`; or keep RVWMO⁻ on `GD'` if `racyD` keeps
    `gppo`) — **unverified**, S–M; the producer of `linCandScaT`'s premise".
  - §A "Names" `:322-323` may keep its factual description of `linCandScaTCatT`.

- **[R21.3] Three errors in the binding F9 / W-DISK bookkeeping.**
  - **(a) The step count for a zero-length IN is 1 → 5, not 1 → 4.**
    *Evidence.*  Folding rule (`:1502-1505`): the `modify`s since the previous fabric step go into the next fabric
    step's `pre`.  For an IN request the previous fabric step is the POP, so `setPhase .fetched` (`Virtio.lean:526`) is
    in the fill's `pre`.  When the fill is elided, it moves to the status write.  MachCSL's steps from the POP's
    continuation to the status byte are then `:526`, `get :489`, `dmaWriteIf r.buf 0 :491`, `:534`, `:536` (five).
    `R-dev`'s full equality off the capture segment forbids performing `:526` any earlier.  The plan lists four, omitting
    `:526` (`:1344-1345` "IN 1 → 4"; `:1465-1468`).
    *Change:* "IN 1 → 5 (`:526`, `:489`, `:491`, `:534`, `:536`)" at both sites.
  - **(b) The single-burst invariant is false without a driver fact.**
    *Evidence.*  `:1336-1337` states "`dvirtio.inflight` has at most one entry during a burst, none outside one".  The
    plan's own arms leave entries outside a burst:
    - An idx-write own-guard SKIP after a mid-burst config write leaves `(h, .pushed)` in flight forever.  MachCSL's
      task then FINISHES (`:1441-1445`; `Virtio.lean:552-554`; `Lang.lean:569-573` no-op arm).
    - An (α) ABORT on a failed `DevM.guard` "ends with the request IN FLIGHT" (`:1506-1507`).

    F9's standard is "no driver fact" (`:1420`).  `:1557-1561` is closer, but its "every OTHER in-flight entry is a
    zombie" is also false: after the SKIP the entry's task is done, not a zombie.  Nothing needs the invariant, because
    `R-dev` is full `dvirtio` equality and `pushOk`/the pop guard read the same map on both sides.
    *Change:* drop the invariant at `:1336-1337`.  Restate `:1557-1561` as: "at most one entry belongs to a LIVE MachCSL
    task (the current burst's); every other entry's task is a never-scheduled zombie or has finished; `R-dev`'s
    equality makes such stale entries harmless (both sides refuse/abort alike); under the verified driver none exists".
  - **(c) F9's scope must list every consumer of `SimRel.dev`, not only "the hart MMIO row".**
    *Evidence.*  `SimRel.dev : c.pcDev.efDev = g.m.devs` (`MachOfPf.lean:315`) is used by:
    - every hart row's post-condition `c'.pcDev.efDev = σ'.devs` (`:869`, `:906`, `:918`, `:935`, `:943-958`, `:989`,
      `:1003`, `:1061`);
    - the MMIO arms (`:1007-1038`);
    - the disk agent's UART/PLIC-gateway rows `simDev`, via `devStepOfFdev … hdev.symm` (`:1253`, `:1266`);
    - the PLIC wire `simWire` (`:1301-1339`).

    During the OUT capture segment the disk agent may still take `pdiskUart` steps, since `dp' = dp`
    (`WeakEvInst.lean:519-525`).  The PLIC gateway samples virtio's line `irq` = `isr`, which `pre₁` leaves untouched,
    so those rows close, but they must be re-proved.  The plan says only "re-check the hart MMIO row" (`:1050-1052`,
    `:1262-1264`), and [R20.1]'s commutation sentence covers "every hart action" (`:1326`, `:1522`) but not the device
    threads' moves.
    *Change (§C top, §C W4 OPEN (b), F9 `:1313-1330`, MECHANISM `:1522`):* "F9 replaces `SimRel.dev` by `R-dev` (+ the
    `isr`/`cfg`/`cap` agreement every reader needs) and re-proves every consumer: all `simNode` posts, the MMIO arms,
    `simDev` (UART/PLIC gateway, incl. moves taken ON the capture segment) and `simWire`; the commutation of `pre₁` is
    checked against hart MMIO writes AND the disk agent's `pdiskUart` moves".  F9's size stays L (unverified); add
    "S–M of re-proof in `MachOfPf.lean`".

- **[R21.4] W5 CORE: say plainly that its theorem is vacuous until W-DISK and F9, and give it an acceptance that does
  not count it as M1.**
  *What is wrong (evidence).*  W5 CORE takes `Hyps.disk` as an explicit hypothesis (`:1044-1047`, `:1693-1702`).
  `Hyps.disk` (`MachOfPf.lean:644-660`) quantifies over every shaped pf run and demands MachCSL steps re-establishing
  `SimRel`, including `rmem`'s `R-log`/`R-hist`.  Against TODAY's pf disk program this is UNSATISFIABLE for every `DR`:
  - The used element is two 4-byte writes (`VirtioProg.lean:587-588`) against MachCSL's single 8-byte `dmaWriteIf`
    (`Virtio.lean:546-548`).  The MachCSL device has no step appending a matching 4-byte disk-agent entry, so any run
    that completes a request breaks `R-hist`.
  - Under `SimRel.dev`'s full equality it is unsatisfiable even for the ALIGNED program, on the OUT capture segment
    (the reason for [R20.1]).

  So the W5 CORE conclusion holds only under a hypothesis currently known false.  The plan correctly says M1 closes
  only at F9 and offers no disk-free variant (`:1052-1055`).  But it does not say W5 CORE is vacuous, gives W5 CORE no
  acceptance, and "Registered per §B(12)" (`:1693`) would register a vacuous root in `baseline-weak.json`.  The owner's
  status reports (% done) would then over-count.
  *Exact change (§C W5, §C top, Status):*
  - "W5 CORE's theorem is CONDITIONAL on `Hyps.disk`, which is UNSATISFIABLE until W-DISK (aligned program) and F9
    (`R-dev`) land.  It is plumbing, NOT a milestone, and is not registered in `roots-weak.txt`/`baseline-weak.json`;
    its acceptance is the four discharges (`tso` by `pfStepTsoProposed`, HSafe and `winPristine` from
    `xv6TextAdequacy_closed`, `cut` by `cutOfPristine`) plus the statement checked to use `SimRel` only through
    `MRun`/`pfObsOf`/`cutOfPristine`'s three fields.  M1 is registered and reported only when F9 discharges `Hyps.disk`."
  - Correct `MachOfPf.lean`'s header deviation 3 ("its owner is OPEN", `:58-60`) to [OWN.35] at the same time.

## SUGGESTIONS

- **[R21.s1] Wording of `sailCycleOrder`.**
  - The plan calls it "a CLOSED proposition about the Sail hart program" (`:916`, `:272`).  As defined (= `Hyps.fi`,
    `MachOfPf.lean:635-643`), it quantifies over `pfRunST` runs and mentions `tsoShadow … .fiArm`, an internal M1 bit.
    Every reader of the PUBLISHED premise would have to understand the shadow.
  - Define it instead in the form the owner ruled (`:2280-2281`): "at every own `.barrier Barrier_RISCV_i` node the
    latest own `LInstr`/`LIFetch` step is `LInstr`; at every own sfence-marker announce it is `LIFetch`".  That is a
    statement about the hart row's label list, i.e. Sail's residual program as `pnodeStep` labels it.  Derive `Hyps.fi`
    by a one-fold lemma over `shStepF` (`TsoShadow.lean:310-318`).
  - Describe it as "about the pf hart rows (Sail's cycle as the event instance labels it)", not "about the Sail hart
    program".
  - Recording the grep (no `execute_*` uses `InstructionFetch`) as evidence of truth would also help.
- **[R21.s2] Coverage of W-SCO.**  M1's runs may fetch anywhere in `[bcRoLo, bcRoHi)`, which includes `.rodata` and
  `.eh_frame` (`Xv6/LinkTextAdequacy.lean:8-9`).  HSafe does not confine the pc to `.text`.  So the per-word lemma
  must cover every 2-aligned 4-byte word of the window (data decoded as instructions), or obtain a pc-in-text export.
  Say which; the Q22 `textAt4S` 2-aligned pattern is the precedent.
- **[R21.s3] One missing case in the capture-`DRead` count.**  If a reset falls between the POP and the capture `DRead`,
  the pre-check fails and the matched run performs NOTHING at the `DRead` (1 → 0; `:526` would resurrect).  The formula
  already covers this, since `pre₁` is then the identity.  Add "1 → 0 when the request is no longer in flight" beside
  "1 → 3 / 1 → 1" (`:1321-1322`, `:1516`).
- **[R21.s4] Cite drift and stale text.**
  - The elision lives in the definitions `dreadData`/`dwriteData` at `VirtioProg.lean:358-366`; `:913-923` are their
    `DmWf` lemmas (`:1462-1463`).
  - "the composition pending" is stale at W14 (`:2127-2128`) and D26 (`:2820-2821`).
  - The MECHANISM write arm still lists `bs s ≠ []` (`:1492`) while the skip arm has no `bs s = []` disjunct.  This is
    harmless under `DmWf`; say so or drop the conjunct.

## Owner questions the plan is missing

- **Q-W8-lane — which proof lane does W8 (the per-access discipline export) run on?**  Raised by [R21.1].
  - *Spec, per the OWNER RULE:* this is not a memory-model question.  RVWMO, riscv.cat, the Sail model in this tree,
    Zifencei and the PMAs say nothing about how a proof's ghost state is organised, so every option below is FAITHFUL.
    None changes the published statement.
  - *Plain language.*  The robustness argument (route (9d)) needs facts about how xv6 accesses memory.  For example,
    "this byte belongs to hart 2's stack, so no other hart writes it", or "this read of `p->state` happens while
    `p->lock` is held".  Only the existing SC proofs know these facts, so a new export (W8) must surface them as a
    property of every reachable machine state.
  - *Tiny example.*  Hart 0 reads `proc[3].state` at `allocproc+0x40` while holding `proc[3].lock`; hart 5 writes it
    only under the same lock.  The final theorem's cycle-kill needs the state-level fact "every write to that byte in
    the history was made by a lock holder" (W8's (ii)).  The cycle-kill is the step that rules out weak-memory
    executions the kernel could not survive.
  - *Definitions.*
    - The serial MachCSL lane is the one-at-a-time queue of changes to the machine model's proof rules.  Each change
      forces a rebuild of the ≈ 0.73M-line kernel proof cone.  Done: W-COH, W-DMA0.  Next: W-RSV, the
      reservation-clearing change, after M1.
    - A state-interpretation ledger is a ghost record kept beside the machine state and updated by every memory rule,
      as `mmOk` is today.
    - `badSeg`/`protReg` are the robustness proof's two consumers of W8's facts.
  - *Why it matters.*  Nothing in the theorem changes.  It is schedule and risk: W8 (L–XL) and W-RSV (L–XL) both edit
    the memory rules, and whichever lands second redoes its edits.
  - *Options.*
    - **(α) Ledger in the state interpretation (D24's recommendation), as the 4th serial MachCSL item, before W-RSV.**
      Concretely, `Resources.lean`'s `memModelAt` gains the ledger and every `Wp*` memory rule maintains it; the cone
      is rebuilt once.  FAITHFUL.  Cost: L–XL on the serial lane, now (the lane is idle until M1).  It unblocks W11
      (i)/(ii) early.  Risk: if it is not done when M1 closes, W-RSV waits for it, and the critical path moves.
    - **(α′) The same, after W-RSV.**  No collision.  It delays W8 by W-RSV's length, which matters only if W8 becomes
      the bottleneck; W13 (XL) is expected to be.
    - **(β) An export derived without touching the rules (D24 (c)).**  It is built from W9a's static pin check plus
      ownership facts proved inside `Xv6/` at adequacy.  FAITHFUL.  Parallel now, with no cone rebuild.  Cost and
      feasibility are **unverified**; (ii)'s lock-protection facts may not be derivable without a ledger.  Risk: a
      partial export, with the rest of the ledger later.
  - *Recommendation:* (α) with a read-only W8-design spike first ([R21.1]).  If the spike shows (β) suffices for (i)
    and (iii), split W8 accordingly.

No other owner question is needed.  [R21.2]–[R21.4] are plan text and bookkeeping in the sound direction, and
[R21.s1] stays within [OWN.35]'s ruling.  The plan's existing questions are all RULED and carry their "Spec:" lines;
Q-FIARM meets the 2026-10-10 format (plain language, tiny example, definitions, marked options).
