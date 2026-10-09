# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 2 = rev 1 + review R1 (11 required changes, tags [R1.n]).**
History: rev 1 (2026-10-09) initial survey; rev 2 (2026-10-09) applied `weak-allocproc-plan-review-R1.md`
(all 11 required, suggestions s1–s5 adopted, owner questions Q-A..Q-F merged as D8–D13).

Advisory only; read-only survey of `../xv6iris-weak` (Lean weak tier `Weak/`, the SC/machine tier
`Xv6/` + `MachCSL/`), `notes/weak-memory-scope.md`, `notes/weak-lb-thm2-final.md`,
`notes/weak-port-architecture.md`, `claude-notes/completed/{relaxed-rr,relaxed-ww,weak-memory-lift}.md`,
`~/dev/weak-orch/open_questions.txt`.  `file:line` cites this tree.  Sizes: S ≤ 300 lines,
M ≤ 800, L ≤ 2k, XL = multi-week / many files.  Anything I could not confirm is marked **unverified**.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14`, proof `Xv6/ProofAllocproc.lean:3623`,
3.6k lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers
the whole function on the real image (`allocproc` = 0x80001b72..0x80001c72): the `proc[]` scan with
`acquire`/`release` per slot (interrupts may be ON; the scan runs at a migrating hart via `wpNext`),
the inlined allocpid under `pid_lock` with the 64-word collision scan (Löb-closed outer loop,
`PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `p->state = USED`, `kalloc` (kmem lock +
freelist, `Xv6/SpecKalloc.lean`, `KallocDefs`), `proc_pagetable` → `uvmcreate`/`mappages`/`walk`/
`kalloc` with PTE writes into fresh OWNED pages (`Xv6/SpecProcPagetable.lean` `pptPost`), `memset`
of the context, `ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`, and
`p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).  Its callees are verified too
(`Proof{Kalloc,ProcPagetable,Mappages,Walk,Uvmcreate,Memset,Freeproc,Acquire,Release,Pushoff,
Popoff,Mycpu}.lean`, ≈ 10.7k lines; file names as on disk).  It is in the cone of the audited roots
(`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; design
`claude-notes/completed/relaxed-rr.md`, `notes/design/tso-memory-model.md`): one total store order
with per-byte write histories, per-hart view FLOORS (a plain load reads at any view ≥ floor:
load–load reordering), store forwarding by author, store buffering, `fence` semantics
`fencePost` (`:345`: W→R edge drains past the hart's own last store, R→R edge acquires past the
read watermark; `fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC reservations,
a non-coherent i-cache view `itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]:
(i) store–store reordering (stores append in po) and load buffering (stores are never early) —
exactly the sRVWMO strengthening of the weak tier (`Weak/WeakAxiomatic3.lean:2050-2071`, rule 14
"stores never early"; the two deliberate divergences LB and reader-fence-only MP,
`Weak/WeakSrvwmoLitmus.lean:1663-1695`); and (ii) **reservation serialisation**: a foreign hart's
store or exclusive read overlapping a held reservation is BLOCKED (self-loop `blockedStep`,
`MachCSL/Lang.lean:366-378,395-403`), DMA likewise (`anyReserve`, `:539,562`), and the reservation
persists until the holder's next store of ANY address (`MState.store … resv := none`, `:145-153`)
or a blocked exclusive read, and survives fences (`MState.fence`, `:157-160`).  RVWMO's atomicity
axiom constrains only SUCCESSFUL LR/SC pairs (intervening foreign stores make the SC fail), and
sRVWMO keeps exclusives fused (`WeakAxiomatic3.lean:2070`), so TsoMem is stronger than both here.
Harmless for kernel code (xv6 locks use only `amoswap.w.aq`, `Xv6/ProofAcquire.lean:5`), but
arbitrary USER code is in the theorem and may `lr`/`sc`; the SC success predicates are two of the
three audited opaques.  Dependency order (ppo 9–13) is absent in TsoMem — the sound
(weaker-than-RVWMO) direction.  So the honest description of the landed system theorem is "xv6 on
sRVWMO + reservation serialisation", not "on SC".

**F2. The AxSL tier cannot reach allocproc.**  Theorem 2 (`allocpidOpen2`, `Weak/AxSpinT2b2.lean:325`)
covers ≈ 230 dynamic instructions on literal row families and cost ≥ 57k lines in the `AxSpin*`
cone (`wc Weak/AxSpin*.lean` = 88k including shared infrastructure) [R1.s1].  allocproc's dynamic
footprint is ≈ 8k instructions for a 64-slot scan (64 × acquire/push_off/holding/mycpu/release ≈ 130)
plus ≈ 16k per page `memset` × 7 (4 `kalloc` fills of `5` + root/L1/L0 zeroing in
`uvmcreate`/`walk`; `procPagetableNodes = 3`, `Xv6/SpecProcPagetable.lean:39`) ≈ 120k instructions
[R1.s1], with four more lock protocols (every `p->lock`, `kmem`), the freelist, and private
page-table pages.  Literal rows are out; loop-invariant WPd reasoning on the AxSL tier for
memset/scan would be a new programme (XL), and gap (1) would still stand.  Recommendation: keep
Theorem 2 as what it is (a validation of the handle-based lock protocol on riscv.cat) and do NOT
extend its segment.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary, and WHICH one [R1.9]: xv6-riscv `b72cbac1` on the project's `verified`
   branch (`notes/STATUS.md:8-11`, `README.md:89-90`), i.e. upstream with two deltas an xv6 expert
   must be told about — (a) the per-process root (`p->root`, `sys_chroot`, `igetroot`), and
   (b) upstream's post-`ded23f2` allocpid: a bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`)
   plus a 64-slot liveness scan, inlined by gcc (`claude-notes/kernel-defects.md:224-231`) — NOT the
   textbook monotone `nextpid`.  Every callee real, no mocks, no hand nodes; failure paths included.
   The caller discharges the contract premises of `wp_allocproc_body` (`Xv6/SpecAllocproc.lean:204-224`):
   `k.tier = KTier.kpt`, `allocprocSlots (= 48) ≤ k.avail`, `k.noff + 2 < 2^31`,
   `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s, `kallocAvail γk on`,
   `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend` — all of them kernel-state facts,
   none about memory ordering;
2. harts [R1.1]: **exactly `NCPU = 8` harts, all booted** (`MachCSL/TsoMem.lean:52`; `PowerOn` forks
   `cpus = List.finRange NCPU`, `MachCSL/Lang.lean:315-319`; `riscvPowerAdequacy` takes
   `[∗list] cpu ∈ cpus, hartWP …`, `MachCSL/Adequacy.lean:383`) — fewer harts is NOT covered
   (named assumption, §B(11); owner D8).  The other harts run ARBITRARY xv6 kernel/user code
   verified against the same invariants (the Iris "rest of the kernel": the third party is every
   other hart of the whole-system proof), interrupts on where xv6 allows them, devices as modelled
   (2 UARTs, PLIC, virtio with DMA as a store-order agent);
3. memory: RVWMO as the ISA defines it — in this tree `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`,
   riscv.cat transcription, fidelity by litmus) or the promising machine + `robustMain`; with every
   strengthening NAMED (today: "stores never early" + reservation serialisation, F1);
4. page tables live: the shared kernel table with concurrent hardware A/D write-back (the SC tier
   has this: `MachCSL/KptInv.lean:39` `pteVariant`, `:85` `kptBody`; TLB `MachCSL/UTlb.lean`), the
   fresh user table as private memory until published;
5. the conclusion is functional AND safety [R1.2][R1.9]: returned slot `&proc[j]`, `j < NPROC`,
   `p->lock` held by the caller, `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid,
   fresh trapframe page (`kalloc`'s fill of 4096 bytes of `5`, `Xv6/SpecKalloc.lean:69`, exposed by
   `allocprocPost` through `procPrivNocwd`, `SpecAllocproc.lean:131`, not as a literal byte list),
   fresh user table with trampoline + trapframe mapped, context `[forkret, kstack+PGSIZE, 0×12]`; or
   `0` with the lock released and everything freed; **no hart ever stuck in the machine semantics**
   (no Sail event without an answer: no unmodelled address, no fault the model rejects —
   `Reducible`); all kernel invariants preserved — i.e. exactly `allocprocPost`.  **Panics are NOT
   excluded by the system theorem**: `panic` is verified with NO postcondition, a bare `wpLoop`
   ("a caller that reaches `panic` has thereby discharged its own goal", `Xv6/SpecPanic.lean:11-14`),
   and a panicking hart's `for(;;)` is reducible, as is a hart self-looping on a foreign reservation
   (`blockedStep`).  The lock cone does refute its own panic arms as WP facts
   (`Xv6/ProofRelease.lean:75-77`, "beqz a0, panic: not taken"), but that is not a conclusion of
   `xv6FsAdequacy`.  "allocproc never panics" is expressible as a console-trace statement (`printk`
   is traced through `uartSentSub`, `Xv6/UartTrace.lean:182`, `SpecPanic.lean:36-41`: "no `panic:`
   bytes in the UART trace"), size M–L, new work — owner D9;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:10-14`), no `sorry`; the trusted base named: the Sail model, the kernel
   image dump, the cat/sRVWMO transcriptions.

**Legitimately out of scope:** liveness/fairness (spin termination, `kalloc` eventually non-null),
timing, the published Promising-RISC-V ≡ RVWMO equivalence (restated natively, D-M6-3), mixed-size
fidelity of the hand-written cat model (scope N10), MMIO ordering beyond the modelled devices, and
hardware outside the Sail model.

**The statement to aim for (two layers, both real theorems):**

*T-alloc (contract layer, exists):* `Xv6.Allocproc` on the MachCSL machine.  Nothing to prove; the
work is to make its memory model honest and composed.

*T-alloc-RVWMO (the credible claim)* [R1.5][R1.2][R1.6][R1.3][R1.4]:
```
∀ (σ0 : WGState) (c : Cand) (pst dv),
  c.cdImg = imgZ σ0.wgimg ∧ pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧
  execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst dv (candExec c) ∧   -- xv6 is the program
  consistent c    -- step 1: srvwmoConsistent ("RVWMO, stores never early"); step 2: rvwmo via robustMain
  →
  (a) the realizing MachCSL run (T1 → pf run → W4) satisfies xv6FsAdequacy_closed's conclusions:
      no hart stuck in the machine semantics (Reducible of the MachCSL configuration; panics not
      excluded), xv6TracePure (fs purity + mmOk), the NI/app conclusions; and, after W4b, Reducible
      of the WEAK configuration itself; and
  (b) the pid/allocation shadow of allocprocPost, tied to the observation trace κs (W1):
      every PAlloc pid ∈ [1, PIDMAX] and the counter tie (nextOf); KAlloc/KNull/KFree well-formed
      (poolEmpty on KNull); every fork return at a `uEnter` carries a0 ∈ {-1} ∪ [1, PIDMAX] with a
      matching PAlloc receipt — and, after W1b, live pids pairwise distinct.
```
The premises are exactly the (c)-side premises of `xv6SrvwmoSafe` (`Weak/WeakSrvwmoCapstone.lean:76-102`):
T1 alone yields only `execWf (candExec c)`, a run of the MEMORY-ONLY machine `mstep`
(`Weak/WeakAxiomatic.lean:273-277`; `Mstate = ⟨msImg, msLog, msWs⟩`, `:103-106`, no program), so
program conformance `execProgOk'` (`Weak/WeakAxRealize.lean:373-386`, which also un-fuses RMWs via
`lblRealizesPair`) is a genuine hypothesis, and `execWfPfRunProg` (`:802-808`) is the lift [R1.5].
(b) is the trace-observable shadow of `allocprocPost` (Iris WPs do not export internal state; the
tree exports ghost ledgers to the adequacy level tied to the OBSERVATION trace — `xv6NiPhi g h :=
∃ F, niOk h F ∧ …`, `Xv6/NiAdequacy.lean:7-9`, `Xv6.xv6NiTwoRun`, `Xv6/LinkNiAdequacy.lean:100` — so
this is the idiom to reuse; the tie is what makes (b) falsifiable, §C W1) [R1.4].

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier.

**(1) AxSL tier not composed with the machine tier.**  Need: only on route (A).  Candid verdict:
there is no cheap AxSL soundness theorem.  What exists: `t2Ev` (`Weak/WeakEvInst.lean:2046`, pf run
⇒ `execWf` execution), `hemitAstep` (conformance IS an opax run), T1 `srvwmoRealizable`
(`Weak/WeakAxiomatic3.lean:2077`, sRVWMO candidate ⇒ pf run), `rule14Linearization`.  Missing:
(i) pf run ⇒ `srvwmoConsistent` candidate (T2 proper; grep finds no such theorem — route (M) does
NOT need it: it quantifies over consistent candidates and only uses T1's direction) [R1.5];
(ii) sRVWMO candidate (`Cand`, `WeakAxiomatic3`) ⇒ tagged `GdexecT` with `rvwmoCatConsistentT` +
ctrl closure (`AxGraphCat`/`AxDeps`) — two independently hand-written models to relate; (iii) the
per-hart opax runs `Hrun`/`Hk0`/`Hend` of `tierAAdequacy` (`Weak/AxTierA.lean:91-98`) from the pf
run's program half (plausible: `pstepEv` and `AxOpsem` are both over `MachCSL.riscvStep`,
`Weak/WeakEvInst.lean:286`); (iv) the row-family premises (`allocPre`, Option V pins, warm TLB, SIE=0)
must hold of EVERY real execution — they do not (cold TLB, interrupts), and prefix closure is
informal (`Weak/AxSpinT2b2.lean:126`).  Cost XL and the result would still be conditional on (iv).
*Recommended treatment:* do not pursue for allocproc; record Theorem 2 as a riscv.cat-tier
validation.  The cheapest CREDIBLE composition is on route (M), §B(9).

**(2) Page tables (HAD, read-only PTE pages, identity map, warm TLB).**  Route (M): CLOSED for
allocproc's own accesses — the kernel table is a live shared invariant with A/D variants
(`KptInv.pteVariant`), the TLB invariant `utlbOk` caches every resident leaf "up to the A/D bits"
(`MachCSL/UTlb.lean:17-21`), hit/miss/fill/write-back modelled (`UFetchWalk`, `WpPtWalk*`) [R1.s3];
user-table pages written by `mappages`/`walk` are fresh owned memory (`pptPost`'s `procPtAt`),
published only at `satp` write + `sfence.vma` (`MachCSL/WpSmodeKpt.lean`).  The direct map is xv6's
real layout, not an assumption.  Remaining named assumption (listed in §B(11)): the Svadu A/D
write-back is modelled as a plain LR/SC that moves no view (relaxed-rr stage E) — a hardware-model
choice beyond RVWMO's text (implicit accesses).  Route (A): L–XL (`AxPtwModel`/`AxPtProt` switch,
plan rev 8 (ii)).  Size (M): S (documentation).

**(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext` migration,
`NCPU = 8` — exactly 8, [R1.1] — device fabric with DMA at the store order, `MachCSL/Lang.lean:1-60`).
Route (A): excluded by design (`devAddr = false`, scope N6).  Size (M): none.

**(4) Text never written / fetch pinned.**  Carried on BOTH tiers (`efetchItvOk`/`fetchSrcOk`,
owner Q4 "leave as premise").  On the machine tier the fact is derivable: kernel text is the
persistent image byte `imgByte` (`notes/design/tso-memory-model.md`: `imgByte a v` at t = 0,
persistent), every store leaf consumes an owned/context byte, and no `↦ₕ` fraction for text bytes
is ever minted — so "no reachable log entry writes a text byte" is a trace export of the state
interpretation.  BUT `efetchItvOk` is a predicate on the WEAK event language (`pstepEv`, `σ.wglog`,
`σ.wgitv c`; `Weak/WeakEvCapstone.lean:681-685`), so the MachCSL-side lemma transports to it only
through W4's log projection (or must be re-proved weak-side), and route (M) (W4/W5) never uses
`efetchItvOk`/`fetchSrcOk` — they are premises of `xv6RvwmoSafeModulo`/`robustMain` (route 9c, W7)
[R1.8].  `WeakEvCapstone.efetchItvOkRunOfUnwritten` (`:697`) is the discharge.  Size M; the lemma is
independent, its corollary is not.

**(5) Segment coverage; `p->pid`/`p->state` hart-private.**  Route (M): CLOSED (F1).  Route (A):
XL (F2).  Size (M): none.

**(6) Scope pins `npNowrap`/`npNcoll`.**  Route (M): CLOSED — the pid register/ledger handles wrap
and collision retries (`ap_pidloop`, `PidEv.cycAt`, `pidPick`, `Xv6/ProofAllocproc.lean:16-24`).

**(7) Store-value row conditions, image facts, informal prefix closure.**  Route (M): none exist —
the WP is over the decoded instruction stream, text facts by `rfl`/`decide` against
`Xv6/KernelImage.lean`.  CLOSED by construction.

**(8) Stack/cpu privacy as WOK, not points-to.**  Route (M): real resources (`stackOwn`,
`MachCSL/StackOwnBounds.lean`; `kctx`/`ctxTok`).  CLOSED.

**(9) NEW — the real gap: TsoMem is sRVWMO + reservation serialisation, not RVWMO** [R1.7] (stores
never early: no W→W reordering, no LB; foreign stores/exclusives blocked against a held reservation).
Need: yes — this is the whole weak-memory content of T-alloc-RVWMO.  Three routes:
- (9a) *Name it.*  State T-alloc at `srvwmoConsistent` ("RVWMO with stores never early") after the
  composition §B(10), with the reservation strengthening named beside it (the simulation W2 will
  show whether WeakMem's `Wresv` discipline is weaker — it clears the reservation at any
  non-trivial fence, `Weak/WeakMem.lean:686`, while TsoMem keeps it — so the composed theorem may
  inherit BOTH restrictions; the header lists whatever W2 establishes).  Honest and credible as a
  first landing; an expert will note that xv6's release idiom (`fence rw,w; sw zero,0(s1)`,
  `Xv6/ProofRelease.lean:83-86`) is load-bearing on real RVWMO and a no-op here (`fenceDrains`),
  so the proof does not exercise it.  Size: §B(10).
- (9b) *Relax the machine to PSO* (`claude-notes/completed/relaxed-ww.md`: design checkpoint,
  two-log machine — issue log + drain log, store pending in a per-hart buffer, `fence` with a W
  predecessor waits for own drains; "exactly two ghost steps become fence-bound: `ctx_stamp` (the
  lock's release) and `ctx_dom_to_stamped`, both already at a release fence in every xv6 use",
  `:30-41`).  The design lives on the Rocq-era branch `relaxed-ww-twolog` (`:7`); the Lean port has
  NONE of it, so the size below is a fresh estimate [R1.s4].  Moves the machine to "RVWMO minus LB
  minus dependency order" and makes `fence rw,w` load-bearing.  Size: L for `TsoMem`/`Lang`/`Ctx`/
  `Lock` + re-threading; the design predicts few whole-function proofs move.  **unverified**
  against the Lean tree.
- (9c) *Robustness for LB*: `robustMain` (`Weak/WeakRobustMain.lean:1520`, promising → pf) needs
  violation-free pf runs (φ) + `fetchSrcOk`; the Rocq line found φ REFUTABLE at event granularity
  (`claude-notes/completed/weak-memory-lift.md:19-29`) and closed it only through the block-granular
  cone composition `WeakComposeLang.xv6_weak_robust_lifted`, which the Lean port SKIPPED
  (`notes/weak-port-skip.md:6`).  The graph-side alternative `xv6RvwmoSafeModulo`
  (`Weak/WeakRvwmoCapstone.lean:187`) carries `l2Claim` (`Weak/WeakRvwmoGlue.lean:449`, "L2′
  proper, the project's remaining content") and `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`).
  Either way XL.
*Recommended:* (9a) now, (9b) as the next machine step (owner question D4), (9c) as the long-term
programme.

**(10) NEW — the machine-tier composition is missing too, but it is tractable.**  The SC tree's
adequacy conclusions are trace properties over MachCSL runs (`MachCSL/Adequacy.lean:266`
`riscvPowerAdequacy`, `Xv6/SystemAdequacy.lean:543` `xv6FsAdequacy`: `Reducible` + `xv6TracePure`,
the latter already exporting the memory-model invariant `mmOk g.m` whenever the power is on,
`Xv6/SystemSlot.lean:135-136`, `MachCSL/Resources.lean:779` [R1.s2]).  The weak tier's pf machine
is `WeakMem` (`Weak/WeakMem.lean`), strictly RICHER in restrictions than TsoMem (per-register
dependency views, message classes, parked release fence; the fence shape is MachCSL's,
`Weak/WeakInterp.lean:376`; the access classifiers are MachCSL's, `:34`, `classify :306`).  The
program half is literally shared (`MachCSL.riscvStep`, `Weak/WeakEvInst.lean:286`).  So the needed
theorem is a SIMULATION, not a re-verification: every `wpPfStep` (`Weak/WeakPromiseBridge.lean:339`)
/ `epfRun` step of the event language is a `MachCSL.primStep` (`MachCSL/Lang.lean:599`) with the
same hart expression and observations; then T1 (`srvwmoRealizable`) + `execWfPfRunProg` + the
simulation give: every sRVWMO-consistent, program-conformant candidate is realized by a MachCSL
run, to which `xv6FsAdequacy` applies.
**Two directions are needed** [R1.6]: (↓) WeakMem step ⇒ TsoMem step (the simulation; carries
trace/state conclusions — W1, `xv6TracePure`); and (↑) RECEPTIVENESS: if the related MachCSL hart
can answer event `o`, the WeakEv hart can answer it — needed to transfer `Reducible` to the weak
configuration, since "WeakMem is more restrictive" gives the opposite direction (`xv6SrvwmoSafe`
gets weak-side reducibility from the WEAK WP package `wpPackage`, `Weak/WeakRvwmoGlue.lean:338-346`,
which xv6 does not have).  Without (↑), conclusion (a) is a property of the projected MachCSL run
and the header must say so.
Risks to check first (spike, both directions, per memory label) [R1.7][R1.11]: WeakMem's parked
`fence rw,w` / release-pending `wRelp` publication (`Weak/WeakMem.lean:640`) vs TsoMem's no-op;
`wRes := none` on every non-trivial fence (`:686`) vs TsoMem keeping the reservation across fences
(`Lang.lean:157-160`); split exclusives `PFExLoad`/`PFExStore` (`Weak/WeakPromiseBridge.lean:414-436`,
`exclOkTs`) vs `othersReserve` blocking (`Lang.lean:366-378,395-403`) — TsoMem blocks foreign
stores, WeakMem fails the SC; `.aq` carried bit `hr.acq` (`MachCSL/TsoMem.lean:255-280`) vs
WeakMem's; the i-fetch agent (no forwarding, `Lang.lean:339-341`) vs `LIFetch`'s `ifetchOk`;
devices/DMA (`Efab` vs `MState.devrt`, "Lean-only, as MachCSL.MState.devrt", `Weak/WeakLang.lean:202`;
`anyReserve` on DMA).  Spot checks already fine in the (↓) direction: WeakMem's `fencePost` raises
`wVrNew` to `max wVrOld wVwOld` for `pr,pw` (`WeakMem.lean:674-678`), `wVwOld` = max own-store
timestamp (`storePostD`, `:634`) = TsoMem's `ownPub`, `wVrOld` = TsoMem's `rv`; so `fence rw,rw`/
`r,r`/`rw,w` agree.  Size: L (↓ simulation) + M (↑ receptiveness) + L (language lift) + M
(corollary).  This is the cheapest credible route to a composed statement, and it lifts the WHOLE
system theorem, not just allocproc.

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R1.s3].
Strengthenings beyond RVWMO: "stores never early" (rule 14); reservation serialisation (F1(ii), and
whichever of TsoMem's/WeakMem's reservation disciplines W2 shows the composed theorem inherits).
Machine-model choices: exactly 8 harts all booted; Svadu A/D write-back as a plain view-neutral
LR/SC (`KptInv.pteVariant`, `utlbOk` "up to A/D"); DMA as a store-order agent.  Fidelity:
`rvwmoCatConsistent` omits rules 6, RCpc 7, 8 (sound direction) and is checked by litmus only
(`Weak/AxLitmus.lean:29`); sRVWMO is a hand-written strengthening; the Sail fork `070832a1` with
`-D SYMBOLIC`; two opaque reservation predicates + one more opaque; `Xv6/KernelImage.lean` by
`tools/dump_kernel.py`.  Treatment: keep, list.

**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (grep: 0 files) while
11 `Weak/` files import `Xv6`; the lake libraries are `MachCSL`, `Xv6`, `Weak` in that dependency
order (`lakefile.toml:2,28-40`).  So every composition file that mentions both `Weak` and `Xv6`
lives in `Weak/`, is registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` +
the `XV6_AUDIT_MODULES` list in `tools/ci/audit.sh:44` (today the 8 T2 modules), and is built/audited
by `--weak` CI — whose cone will then include the whole `Xv6` adequacy cone (audit time and memory
grow accordingly; owner D13).  Pure-`Xv6/` items (W1, W3) go to `roots.txt`/`baseline.json`.  Size S.

## C. Roadmap

Each stage ends in a theorem; "∥" = can run in parallel (one Opus worker, one file each).

**Stage 0 — launch now (∥ W1, W2, W3).**
- **W1 `Xv6/AllocprocTrace.lean`** (M) [R1.3][R1.4].  Milestone `allocprocLedgerAdequacy`,
  RE-SCOPED to what today's ledgers export (R1.3 option (i)): `Kev` is `KAlloc p | KNull p | KFree p`
  with NO page address (`Xv6/KallocEv.lean:45-52`) and `kmemLedger` ties only counts
  (`npages + allocs h = frees h`, `Xv6/KallocDefs.lean:220-222`); `Pev` is `PAlloc act pid | PFree act
  pid` with NO slot index (`Xv6/PidEv.lean:50-55`); `liveOf` is a SET (`:69`), so "live pids pairwise
  distinct" is vacuous on `h`, and the authority `pidLedger` (`Xv6/PidLock.lean:113-114`) carries
  only `liveOf h = dom R ∧ pidTie`, its cell side existential (`pidCells`, `:85`) — slot uniqueness
  is not an invariant of the tree (`claude-notes/kernel-defects.md:249-250`: "Uniqueness (no two live
  slots share a pid) is a further step nothing consumes yet").  So W1 states, as a pure predicate on
  the exported histories: every `PAlloc` pid ∈ [1, PIDMAX] and the counter tie (`nextOf`,
  `PidEv.lean:77`); `KAlloc`/`KNull` well-formedness (`poolEmpty` at every `KNull`,
  `KallocEv.lean:72`); the slot-exhaustion receipt.  **Tie to the observation trace** (β,
  recommended; owner D11): `Obs.uEnter cpu satp epc gprs` carries the register file at the user
  boundary (`MachCSL/Lang.lean:243-249`), so a fork's returned pid is in `κs` and the per-call
  receipt `pidAllocRcpt` (`PidLock.lean:118-119`, `pid = pidPick PIDMAX prefix`) is cited against it
  — the NI fork lane already matches `uEnter` registers this way (`Xv6/NiTrace.lean:138`), and the
  dispatcher's fork row (`r = -1 ∨ 1 ≤ sint r ≤ PIDMAX`, `kernel-defects.md:243-247`) is the
  bridge.  Alternative (α): a STATE predicate on `g2.m` in the `mmOk` idiom (`Xv6/SystemSlot.lean:135-136`)
  — "pid words of slots whose `state` word ≠ UNUSED are in [1, PIDMAX]" — but the pid cells sit in
  `pid_lock`'s payload, absent from the invariant while held, so (α) needs a lock-free caveat.
  Derived as an `xv6PowerAdequacyGen` hook (`Xv6/SystemAdequacy.lean:277`) in the `xv6NiAdequacy`
  idiom.  Deps: none; one file; `roots.txt`/`baseline.json`.
- **W1b (owner-gated, R1.3 option (ii), L, serial, shared files)**: strengthen `pidLedger` with a
  history-wide `pidHistWf h` (every `PAlloc` = `pidPick` of its prefix ⇒ live pids distinct by
  induction) and re-thread `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally add addresses to
  `Kev` (ripples through `ProofKalloc`, `ProofKfree`, `NiLedger`, `UnionOutLed`, every ledger
  consumer) for page disjointness.  Only this yields "live pids pairwise distinct", "live slots
  distinct", "allocated pages disjoint from the free list" as exported facts.  Not Stage 0; owner D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report first) [R1.11].
  Milestone `pfStepTso`: for every memory label (load/store/fence/AMO/LR-SC/ifetch), a `WeakMem`
  pf step from a state related by `R` (views: TsoMem floor ≤ WeakMem effective view; histories =
  log projection; reservations; `itv`) is a TsoMem step with the same bytes, to a related state.
  The spike report lists, PER LABEL, (↓) WeakMem ⊆ TsoMem (simulation) and (↑) TsoMem-enabled ⇒
  WeakMem-enabled (receptiveness), recording the fence spot checks of §B(10) as done and settling the
  open items: `wRelp`, `wRes := none` on fences, split exclusives vs `othersReserve`, i-fetch agent,
  DMA vs `Efab`.  Deps: none.  **STOP rule**: if the spike finds a WeakMem behaviour TsoMem lacks
  (↓ fails) OR a TsoMem-enabled event WeakMem cannot answer at a related state (↑ fails), STOP and
  report (the fix would be a MachCSL or WeakMem change — owner-gated, D7).
- **W3 `Xv6/TextUnwritten.lean`** (M) [R1.8].  Milestone `kernelTextUnwritten`: no reachable store
  (hart or DMA) targets `[text, etext)`, as a trace export of the state interpretation (`imgByte`
  persistence + the store leaves' ownership premise).  Corollary discharging `efetchItvOk`/
  `fetchSrcOk` via `efetchItvOkRunOfUnwritten` — this needs W4's log projection.  Deps: lemma none;
  corollary W4; consumer W7 (route 9c).  Stage 1 does not need W3; it closes owner Q4 only at Stage 2.

**Stage 1 — the composed sRVWMO theorem (after W2).**
- **W4 `Weak/MachOfEpf.lean`** (L).  Milestone `machRunOfEpfRun`: an `epfRun` of `WeakEvLang` from
  `epInit` projects to a `MachCSL.primStep` run (`-<κs>->ₜₚ^[n]`) with the same hart expressions,
  the same observations (`hartObs`), and devices aligned.  Deps: W2.
- **W4b `Weak/MachOfEpfRecv.lean`** (M) [R1.6].  Milestone `epfReceptive`: at `R`-related states, if
  the MachCSL hart can answer event `o` the WeakEv hart can (memory arms total modulo views;
  devices/`Efab` aligned).  Transfers `Reducible` to the weak configuration.  Deps: W2 (↑ column).
  If skipped, W5's (a) is stated for the projected MachCSL run.
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R1.10].  Milestone **T-alloc-sRVWMO**: from the
  (c)-premises of `xv6SrvwmoSafe` (`srvwmoConsistent c`, `c.cdImg = imgZ σ0.wgimg`, `execProgOk' …`,
  `pst 0 = epsInit σ0`, `dv 0 = efInit σ0.wgdev`), reuse its FIRST conjunct (proof
  `WeakSrvwmoCapstone.lean:111-116`, needs none of the WP-package premises) to obtain
  `rtc epfRun (epInit gen, σ0) (P', σ')` with `σ'.wglog = cdLog c …`; W4 projects it to a MachCSL
  run; `xv6FsAdequacy_closed` and W1 conclude; W4b (if landed) adds weak-side `Reducible`.  Header
  lists the named strengthenings and trusted base (§B(11)) and `mmOk` at every reachable state
  [R1.s2].  Lives in `Weak/`; register in `roots-weak.txt`/`baseline-weak.json`/`XV6_AUDIT_MODULES`;
  `--weak` CI builds the full `Xv6` cone.  Deps: W1, W4 (W4b optional).

**Stage 2 — towards RVWMO proper (owner decision D4 first).**
- **W6 (option 9b) PSO machine** (L, fresh estimate [R1.s4], serial, MachCSL change): `TsoMem`
  two-log drain semantics per `relaxed-ww.md` §1; `fenceDrains` becomes load-bearing for W
  predecessors; re-thread `Lock`, `Ctx` (`ctx_stamp`/`ctx_dom_to_stamped` fence-bound),
  `WpSmodeFencePub`, the lock Spec/Proofs; full `lake build` + audit.  Then W2/W4/W4b are re-checked
  (the relation `R` gains the drain log).  Milestone: `xv6FsAdequacy` on "RVWMO minus LB minus deps".
- **W7 (option 9c) robustness composition** (XL): either revive `WeakComposeLang` (block-granular
  cone premises `xv6_cone_premises`) or discharge `l2Claim`/`walkSupply` for xv6; consumes W3's
  corollary (owner Q4 closes here) [R1.8].  Milestone: `xv6FsAdequacyRvwmo`.  Not before W5 lands.

**Stage 3 — optional, AxSL tier.**  Park Theorem 2's segment; if the owner wants the AxSL tier tied
in, the item is §B(1)(i)–(iii) (XL) — recommend NOT scheduling.

**First three work items to launch now:** W1 (`Xv6/AllocprocTrace.lean`, re-scoped), W2 spike
(`Weak/TsoOfPf.lean`, two-column risk report first), W3 lemma (`Xv6/TextUnwritten.lean`).  All three
are independent, each one file, none touches shared `MachCSL/` (W2's spike is read-only on MachCSL).
W1b waits for D10.

## D. Owner questions (recommended option first)

- **D1. Tier.**  (Rec) Build the allocproc theorem on the machine tier (SC tree + composition,
  §C), retiring further AxSL segment work; (b) extend Theorem 2's segment (XL, still gap (1)).
- **D2. First landing statement.**  (Rec) T-alloc-sRVWMO with the strengthenings named in the
  theorem's header ("RVWMO, stores never early" + reservation serialisation); (b) hold publication
  until RVWMO proper (W7, XL).
- **D3. Conclusion form.**  (Rec) trace-level ledger predicate (W1) tied to `κs`, beside the Iris
  contract; (b) Iris contract only (not readable as "a theorem on allocproc" by outsiders).
- **D4. Machine relaxation.**  (Rec) schedule the PSO two-log machine (W6) right after W5 — it
  shrinks the named gap to LB only and makes xv6's `fence rw,w` load-bearing; (b) skip to W7;
  (c) stay at sRVWMO.
- **D5. Q4 now.**  (Rec) launch the W3 lemma now (its corollary waits for W4, its consumer is W7);
  (b) keep the premise carried.
- **D6. Theorem 2.**  (Rec) keep `allocpidOpen2` + certificates as the audited riscv.cat-tier
  validation of the lock protocol; its header already says so (`Weak/AxSpinT2b2.lean:318-324`), so
  the amendment is a one-paragraph note, size S [R1.s5]; (b) continue the reduce-pins lanes.
- **D7. W2 failure mode.**  If the spike shows a WeakMem step TsoMem lacks (parked release fence /
  reservation clearing are the suspects) or a TsoMem event WeakMem cannot answer, (Rec) change
  `WeakMem`'s event instance to MachCSL's shape where the kernel proofs allow, else (b) accept a
  MachCSL change (owner-gated, serial).
- **D8. Hart model** [R1.1, Q-A].  (Rec) publish "exactly 8 harts, all booted" as a named
  assumption (no proof change); (b) a "≤ 8, some harts never leave `_entry`" variant (a MachCSL
  `PowerOn`/`cpus` change, serial).
- **D9. Panics** [R1.2, Q-B].  (Rec) state "no hart stuck in the machine semantics", panics
  explicitly NOT excluded; (b) add "no `panic:` bytes in the UART trace" (new work, M–L, via
  `uartSentSub`).
- **D10. W1 scope** [R1.3, Q-C].  (Rec) re-scope to today's ledgers (W1, fast, Stage 0); (b) also
  schedule W1b (strengthen `pidLedger`/`Kev`; L, serial, shared files) for pid/slot uniqueness and
  page disjointness as exported facts.
- **D11. W1 tie** [R1.4, Q-D].  (Rec) observation-level (β): fork return at `uEnter` vs `PAlloc`
  receipts; (b) state-level (α) on `g2.m` with the lock-free caveat.
- **D12. Which xv6** [R1.9, Q-E].  (Rec) the `verified`-branch fork (chroot + post-`ded23f2`
  allocpid), named in the header's first sentence; (b) upstream master (changes the header, not the
  proofs — and would not match the image).
- **D13. Where the composed theorem lives** [R1.10, Q-F].  (Rec) `Weak/`, audited under `--weak`,
  accepting that the `--weak` audit then builds the full `Xv6` cone; (b) a separate lake library /
  CI lane for the composition if the cost is unacceptable.
