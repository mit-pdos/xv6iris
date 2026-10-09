VERDICT: NOT SATISFIED

# Review R2 of `notes/weak-allocproc-plan.md` rev 2 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R1's 11 required changes applied correctly; (2) a fresh audit of the load-bearing
claims that rev 2 now rests on (the W4/W5 chain, the TsoMem-vs-sRVWMO description, the target
statement).  `file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds run.

## R1 application check

All eleven are in rev 2 and are substantively right: [R1.1] §A.2/§B(3)/§B(11)/D8 (`cpus =
List.finRange NCPU`, `MachCSL/Lang.lean:315-316`; `NCPU = 8`, `MachCSL/TsoMem.lean:54` — the plan
says `:52`, harmless); [R1.2] §A.5/D9 (`Xv6/SpecPanic.lean:11-14`, `:36-41`; `uartSentSub`,
`Xv6/UartTrace.lean:182`); [R1.3] W1 re-scoped + W1b (`Kev`, `Xv6/KallocEv.lean:45-52`; `kmemLedger`,
`Xv6/KallocDefs.lean:220-222`; `Pev`/`liveOf`/`nextOf`, `Xv6/PidEv.lean:50-55,69,77`; `pidTie`/
`pidLedger`/`pidAllocRcpt`, `Xv6/PidLock.lean:88,113-114,118-119`; the "nothing consumes yet"
sentence is at `claude-notes/kernel-defects.md:249-250` as rev 2 says); [R1.4] tie β
(`Obs.uEnter`, `MachCSL/Lang.lean:243-249`); [R1.5] T-alloc quantifies over `Cand` with the
(c)-premises (`Weak/WeakSrvwmoCapstone.lean:76-102`; `execProgOk'`, `Weak/WeakAxRealize.lean:373-386`;
`execWfPfRunProg`, `:802-808`); [R1.6] W4b; [R1.7] reservation serialisation named (`evStep` excl
arms `MachCSL/Lang.lean:366-378`, `blockedStep :395-403`, `anyReserve :539,562`, `MState.store
… resv := none :147-153`, `MState.fence :155-163`); [R1.8] W3 deps (but see [R2.1] — the premise it
concerns is NOT confined to route 9c); [R1.9] the fork + two deltas (`notes/STATUS.md:8-11`,
`README.md:89-90`, `Xv6/ProcGeom.lean:80`); [R1.10] layout (`lakefile.toml:2,27-41`; `Xv6/` imports
`Weak/` in 0 files, `Weak/` imports `Xv6` in 11; `tools/ci/audit.sh:44`); [R1.11] two-column
spike.  One correction to R1 itself: `Xv6/ProofPushoff.lean` and `Xv6/ProofPopoff.lean` DO exist,
so rev 2's callee list ("file names as on disk") is right and R1's remark was wrong; the eleven
files `Proof{Allocproc,Kalloc,ProcPagetable,Mappages,Walk,Uvmcreate,Memset,Freeproc,Acquire,
Release,Mycpu}` total 10,682 lines (`wc`).

Also confirmed: `Xv6.Allocproc` (`Xv6/LinkAllocproc.lean:14-16`) = `allocproc_proof`
(`Xv6/ProofAllocproc.lean:3623-3639`), instantiated in both audited cones (`Xv6/LinkSyscall.lean:84`,
`Xv6/LinkMain.lean:53`); `wp_allocproc_body`'s premise list is as the plan states
(`Xv6/SpecAllocproc.lean:204-224`); `xv6FsAdequacy_closed` (`Xv6/LinkSystemAdequacyClosed.lean:20-26`)
has exactly the hypotheses `g.gen = 0`, `g.pow = false`, `diskOf g.m.devs = fsImgDisk`, and a
`-<κs>->ₜₚ^[n]` run from `([Expr.power], g)`; baseline axioms/opaques (`tools/audit/baseline.json:11-14`,
`notes/adequacy_axioms_baseline.md:19-45`).  sRVWMO as cited (`Weak/WeakAxiomatic3.lean:2050-2071`,
`srvwmoRealizable :2074-2079`); the divergence table (`Weak/WeakSrvwmoLitmus.lean:1663-1695`).
The pf-machine fence spot checks (`Weak/WeakMem.lean:669-686`, `storePost :634`) and the `classify`
/ `itvPostMachCSL` sharing (`Weak/WeakInterp.lean:306,376-379`) are as stated.

## REQUIRED changes

**[R2.1] The lift T1 → `epfRun` DOES use the fetch-view premise; §B(4), W3, W5 and the T-alloc
premise list are wrong about it.**  Evidence: the run-level lift `wpPfRtcEpfRtc` takes
`(∀ ρ, rtc epfRun (P, σ) ρ → efetchItvOk ρ.1 ρ.2)` (`Weak/WeakEvCapstone.lean:1008-1011`), and
`xv6SrvwmoSafe`'s FIRST conjunct — the one W5 says it will "reuse, needs none of the WP-package
premises" — calls it with `Hcov` (`Weak/WeakSrvwmoCapstone.lean:116`), i.e. with premise (b')
(`:88-89`).  So "route (M) (W4/W5) never uses `efetchItvOk`/`fetchSrcOk`" (§B(4)) and "Stage 1 does
not need W3" (W3) are false as the chain is written.  Moreover (b') cannot be discharged weak-side
on route (M): it quantifies over ALL `epfRun`-reachable states, including interleavings no
candidate realizes, and "text never written" is kernel-verification content that only the MachCSL
state interpretation carries.  Change: (i) W5 must NOT go through `epfRun`/`wpPfRtcEpfRtc`; it
starts from `execWfPfRunProg`'s `rtc (wpPfRun pstepEv pclsEv) (wpInit …) c`
(`Weak/WeakAxRealize.lean:802-808`, with `wpPfRunPinSub` as at `WeakSrvwmoCapstone.lean:115`), and W4
is a projection of `wpPfRun` runs (the pf machine WITH program, `Wpcfg Pexv6 Efab`), not of
`epfRun`; (ii) W3's LEMMA becomes a Stage-1 dependency of W2/W4: the pf fetch is admissible at
floor 0 (`ifetchOk cfg.pcImg cfg.pcLog 0 base tvs`, `Weak/WeakPromiseBridge.lean:448`) while TsoMem
fetches at `σ.itv cpu ≤ tvn` (`MachCSL/Lang.lean:349-351`), so the (↓) case for `LIFetch` needs
"the fetched bytes have no log write" at the related MachCSL state — that is exactly
`kernelTextUnwritten` applied to the MachCSL prefix run; (iii) rewrite §B(4): the premise is
carried by BOTH weak capstones (`xv6SrvwmoSafe` (b') and `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:195`), and route (M) removes it only by bypassing the event-language
lift; (iv) W3's "closes owner Q4 only at Stage 2" → "Q4 closes at Stage 1 for the composed
theorem; for the weak capstones it stays a premise unless re-proved weak-side"; (v) D5: W3 is no
longer optional — it is on the Stage-1 critical path.

**[R2.2] The target statement is unprovable as written: σ0 is unconstrained, so `xv6FsAdequacy_closed`
does not apply to the projected run.**  `xv6FsAdequacy_closed` starts from `([Expr.power], g)` with
`g.pow = false`, `g.gen = 0`, `diskOf g.m.devs = fsImgDisk` (`Xv6/LinkSystemAdequacyClosed.lean:20-26`);
its first step is `PowerOn`, which hands over a state with `bootFacts` — `σ.mem = imgFlat bootImage`,
empty log, zero views, register files from the boot program, `devrt = init` — and `devs =
g.m.devs.reset` (`MachCSL/Lang.lean:294-306`, `bootWitness :310-314`).  T-alloc-RVWMO quantifies
`∀ (σ0 : WGState)` with only `c.cdImg = imgZ σ0.wgimg`; `xv6SrvwmoSafe` itself asks only
`wgpow/wggen/wglog/wgws` (`Weak/WeakSrvwmoCapstone.lean:81-83`).  Nothing ties `σ0.wgimg` to
`bootImage`, the register files to the boot program, or the disk to `fs.img` — so W4 cannot
produce a run of the shape `xv6FsAdequacy_closed` consumes.  The weak tier already has the right
predicate: `wbootFacts` (`Weak/WeakLang.lean:482-490`: `wgimg = bootImage`, boot-program register
files, `∃ ds, wgdev = ds.reset`, `wgitv = 0`, `wgrt = init`).  Change §A T-alloc-RVWMO's premises
to: `wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk)` plus the
(c)-premises; change W4's milestone to "the projected run, PREFIXED by the `PowerOn` step from
`([Expr.power], ⟨…, ds, …⟩, gen 0, pow off)`, is a `-<κs>->ₜₚ^[n]` run of MachCSL whose state after
`PowerOn` is the projection of `σ0`" (the image tie `imgZ bootImage` ↔ `imgFlat bootImage` is part
of the relation `R`).  Say in the header that the composed theorem is SINGLE-ERA: `epowerFork`
forks no power thread (`Weak/WeakEvLang.lean:201-204`), so `xv6FsAdequacy`'s multi-era conclusion
(power cycles, durable recovery across them) is NOT transported — only the one era from the given
boot.

**[R2.3] (↓) is refuted on arbitrary pf runs; W2/W4/W5 must be stated over REALIZED runs (exclusive
halves adjacent), and W5 must carry that shape.**  The event instance SPLITS every exclusive access
(AMO and LR/SC alike) into `LExLoad`/`LExStore` (`Weak/WeakEvInst.lean:323-331,350-364`); a
foreign hart's plain store to the reserved footprint between the halves is ENABLED in WeakMem
(`PFStore` has no reservation guard; the loser's `PFExStore` then fails `exclOkTs`,
`Weak/WeakPromise.lean:324-326`, and the loser takes the memory-blind RETRY SELF-LOOP forever,
`WeakEvInst.lean:360-364`), while in TsoMem that store is BLOCKED (`othersReserve`,
`MachCSL/Lang.lean:366-369,395-403`).  So at that step WeakMem has a transition TsoMem lacks — the
STOP condition of W2 — and it is the common case of every contended `amoswap.w.aq` acquire.  A
lagging/stuttering relation does not rescue it: once the retry loop is entered the weak hart's
expression is frozen at the `memWrite` continuation forever and no TsoMem run matches.  What saves
route (M) is that the runs W5 obtains are REALIZATIONS of fused `LRmw` candidates
(`Lbl`, `Weak/WeakAxiomatic.lean:87-92`, has no split exclusive): `execProgOk'` realizes one
candidate step per trace index by ONE agent — the exclusive read, an `admStar` of the SAME agent,
the conditional write (`Weak/WeakAxRealize.lean:373-386`, `lblRealizesPair :305-313`,
`execPrefixPfRunProg :745-751`) — so in a realized run nothing foreign intervenes between the
halves, the `LExLoad` at "the 0 floor" (`Weak/WeakPromiseBridge.lean:422-423`) in fact read the
bytes `exclOkTs` certifies as foreign-unwritten, and the retry arm never fires.  Change: (i) W2's
`pfStepTso` is stated for pf steps under a shape predicate `pairAdjacent` (between an agent's
`PFExLoad` and its `PFExStore` only that agent steps, and the `PFExStore` is the realization
arm, not the retry arm), with the relation `R` tracking "agent `i` is mid-pair"; the spike's
per-label table gets a row for each half; (ii) W4 projects `pairAdjacent` `wpPfRun` runs; (iii)
W5 needs a SHAPE-CARRYING variant of `execPrefixPfRunProg` (the existing one returns only
`∃ c, rtc …`) — a new theorem in `Weak/` (M), not a change to `WeakAxRealize`; (iv) W4b
(receptiveness on arbitrary weak interleavings) is NOT available on route (M): the configurations
the composed theorem can speak about are the realized ones, and weak-side `Reducible` on
non-realized interleavings would need the weak WP package.  Restate (a) honestly: conclusions are
about the realizing MachCSL run (`Reducible` of the MachCSL configuration, `xv6TracePure`); add
"the realized pf run never enters the retry self-loop" (free from the shape) if a weak-side
sentence is wanted; drop W4b from the roadmap or mark it "only with a weak WP package (none for
xv6)".  Update D7: the WeakMem-vs-TsoMem divergence on split exclusives is now KNOWN, and the fix
is the shape restriction, not a MachCSL or WeakMem change.

**[R2.4] "No hart stuck" must name the two reducible spin arms, and §B(11) must list the i-cache
model.**  §A.5 names `blockedStep`; add the weak side's memory-blind retry self-loop
(`Weak/WeakEvInst.lean:360-364`) — a hart that lost an exclusive pair spins forever, reducibly —
so "no hart stuck" on either side excludes neither a panic nor a lost-exclusive spin.  §B(11)
omits the instruction-fetch model: fetch at any view `≥ itv` by an agent that never authors a
store (no forwarding), only `fence.i` raising `itv`, `itv ≤ tv` not invariant
(`MachCSL/TsoMem.lean:34-39`, `Lang.lean:349-351`, `MState.fence :157-163`) — a modelling choice
beyond RVWMO's text (Zifencei) that the composed theorem inherits; list it beside Svadu and DMA.
Also list that exclusive writes never FAIL at the memory in either tier (TsoMem: blocked or
appended; WeakMem: `exclOkTs` or retry) and that SC failure is the Sail opaques' program-side
decision (`tools/audit/baseline.json:13`) — an xv6 expert will ask what a failing SC means here.

**[R2.5] Non-vacuity of T-alloc-RVWMO must be certified.**  The statement quantifies over
`srvwmoConsistent c ∧ execProgOk' … (candExec c)` candidates of the xv6 boot; the tree has no
theorem that any exists (the `WeakRvwmoConfWit*` witnesses are two-event `rvwmoMinusDepsConsistent`
graphs, `Weak/WeakRvwmoConfWit2.lean:1-40`, not program-conformant sRVWMO candidates of a boot
prefix).  Without one, an expert cannot distinguish the theorem from a vacuous implication.  Add
**W5c `Weak/SrvwmoXv6Witness.lean`** (M): a concrete `Cand` for a boot prefix (the `sw &started`
handshake of `main`, as `WeakEvStarted`/`WeakRvwmoConfWit2` build it) with `srvwmoConsistent` and
`execProgOk'`, built with the snoc machinery that already exists (`snocConsistent`,
`execProgOk'Snoc`, `Weak/WeakRvwmoCert2.lean:961-975`).  Register it beside W5 in
`roots-weak.txt`/`baseline-weak.json`.

## SUGGESTIONS

- [R2.s1] Cite hygiene: `Xv6/NiTrace.lean:138` (prose about `wait` windows) → the register
  extraction at `:542,556` (`gprsA0`); `claude-notes/kernel-defects.md:243-247` → `:245-246`;
  `MachCSL/TsoMem.lean:52` → `:54`; `MachCSL/Lang.lean:315-319` → `:315-320`.
- [R2.s2] §0 F1 "exactly the sRVWMO strengthening": say "the same ppo residue (rules 1–5, 7, 14),
  checked by reading, not by theorem" — there is no theorem relating TsoMem to `srvwmoConsistent`,
  and after [R2.3] none is needed (the composed statement names `srvwmoConsistent`, and TsoMem's
  strength matters only through the simulation).
- [R2.s3] W2's relation `R` should be fixed in the spike report, not left to the L file: TsoMem
  `tv ↔ wVrNew`, `rv ↔ wVrOld`, `ownPub ↔ wVwOld`, `coh ↔ wCoh`, `itv ↔ wgitv` (the pf machine has
  no `itv`; carry it in `R` as "the MachCSL `itv` is below every fetch's view", which is where
  W3's lemma enters), `resv ↔ wRes` only while mid-pair.
- [R2.s4] Order Stage 0 as W3 lemma → W2 spike (needs W3's statement for the `LIFetch` row) ∥ W1.
- [R2.s5] The two-era question ([R2.2]) deserves an owner line: a multi-era composed theorem would
  need the weak language's power thread (`WExpr.power`, `Weak/WeakLang.lean:471`) in the pool and
  `wbootShape` at each `PowerOn`; size M on top of W4, not needed for allocproc.

## Owner questions the plan is missing

- Q-G. Single era: is "one boot, no power cycles" acceptable for the composed theorem's header, or
  should W4 include the power thread (M)?
- Q-H. With W4b gone ([R2.3](iv)), is "conclusions about the realizing MachCSL run" an acceptable
  reading of (a), or is a weak-side sentence ("the realized pf run never spins in the retry arm")
  wanted?
- Q-I. Is the non-vacuity certificate W5c a publication gate (recommended) or a follow-up?
- Q-J. Should the header disclose the SC-failure model (opaque predicates; memory never fails an
  exclusive write) as a named assumption, given user code is in the theorem?
