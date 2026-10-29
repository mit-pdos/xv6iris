# PROGRESS — S1M-def (machine v2 + emission v2 as definitions)

Worker: Opus (S1M-def). Workspace `/home/bsdinis/dev/xv6iris-pcsl`. Plan of record `~/dev/weak-orch/promising/plan.md`
rev 7; owner rulings [OWN.P1] (faithful permissive behaviours), [OWN.P2] (FENCE.I/fetch faithful), [OWN.P3] (OQ-1
punted: translation deferred; first increment = small M-mode programs).

## STOP-AND-ASK items (non-blocking; everything else proceeds; spec first)

**SA-1. Misaligned access: the "raise an exception" choice is a platform constant the instance cannot change.**
- Text: rv32.adoc:694–696 (FE-5) "Loads and stores whose effective address is not naturally aligned … have behavior
  dependent on the EEI"; machine.adoc:3103–3105 (PMA-6) "either an exception is raised, or the access proceeds but is
  not guaranteed to be atomic"; :3106–3107 (PMA-7) access-fault instead of address-misaligned.
- Sail: `plat_misaligned_exception` (VmemUtils.lean:219–228) reads the CONCRETE config constant
  `plat_misaligned_access.load_store = none` (sail-config-rv64d.json:295–297) inside `vmem_read_addr` /
  `vmem_write_addr` (VmemUtils.lean:262–275, :345–358), before any event the instance sees.
- What v2 does: the "access proceeds" branch, with every decomposition ([OWN.P1] (2), done: `Emit.splittable`).
- Options: (a) per-platform: the theorem is about this EEI (misaligned handled) — STRONGER relative to the union
  over EEIs; (b) make the constant an opaque platform hook in the model's extras file (D51 pattern; a model-file
  change outside S1M-def's write scope) — FAITHFUL (union over platforms); (c) instance-level trap injection
  (replace the residual Sail program by its exception path at a misaligned access) — FAITHFUL, ~0.5–1k lines,
  fragile (reimplements Sail's trap sequencing). Default while waiting: (a).

**SA-2. Unrealised platform hooks are irreducible axioms; no instance can answer them.**
- Sail/tree: `plat_term_read`, `get_16_random_bits` (Zkr `seed`) and the softfloat `riscv_f*` family are root-level
  `axiom`s (fork `RiscvExtras.lean`; not overridden in `model/Xv6Extras.lean`, whose header says "a hart that reaches
  one stays stuck"). A hart whose residual monad is headed by an axiom has no provable `hnodeStep`.
- Text: Zkr `seed` returns entropy (any 16 bits + status); `plat_term_read` is a platform device read (any byte); FP
  results are fixed by IEEE 754 (deterministic).
- Options: (a) realise them in `model/Xv6Extras.lean` (master copy) as `choose`-based answers — FAITHFUL for
  `seed`/term-read, WEAKER for softfloat (or port a real softfloat: FAITHFUL, large); (b) keep stuck and add a scope
  predicate "no hart reaches an unrealised hook" (SCOPE: the theorem covers fewer executions); (c) keep stuck
  silently (STRONGER, not acceptable under the fidelity rule). Default while waiting: (b)-in-spirit (nothing emitted;
  the predicate is not yet written).

**SA-3. The `.error` arm (Sail `internal_error` / `Error_not_implemented` / `sailThrow`).**
- These are model-internal failure paths (e.g. `Error_not_implemented "load.rl"`, Mem.lean:493–496; hypervisor
  `internal_error`s); the manual has no corresponding behaviour, so "every behaviour the text permits" is undefined
  there. v2 keeps the arm `False` (stuck), as today.
- Options: (a) scope predicate `noModelError` (SCOPE, explicit); (b) havoc after the error (any later behaviour;
  WEAKER, sound, heavy for proofs); (c) audit each reachable site and fix it per site. Default: (a) (predicate not
  yet written).

## Increment order (after [OWN.P3], 2026-10-29)

1. **I1 — Machine v2 core — DONE, green.** `Weak/Prom/Machine.lean`.
2. **I2 — Emission v2 (translation off) — DONE, green.** `Weak/Prom/Emit.lean`.
3. **I3 — CMO (Zicbom inval/clean/flush; Zicboz tearing) — DONE, green** (machine `cmo` arm + `invalRead`;
   emission at the instruction boundary; `cbo.zero` via `splittable`).
4. **Next (not started):** answers to SA-1..SA-3; then the deferred translation items below (only when OQ-1 is
   un-punted); then the disk agent / PLIC wire for xv6 (`pstepDisk`/`pstepPlic` analogues).

## Done (all green on the VM; `lake build Weak.Prom.Emit` ≈ 4 s warm, cold first build of the workspace ≈ 5 min;
lint: only the expected drift rows for the two new files)

`Weak/Prom/Machine.lean` (741 lines): messages `PMsg`/`PClass` (plain/rel/excl/cmo; class checked at fulfil, N-10),
`PState` (v2 fields; `wPub`/`wRelp`/`wTbank` dropped), `PLabel` (no `lat`, SR-31; `LAmoLd`/`LAmoSt`, `LExFail`,
`LFenceI`, `LCmo`), `memStep` (one constructor per arm: silent, load, store, rmw, amoLd, amoSt, fence, fenceI, dev,
regW, ctrl, instr, lr, sc, scFail, fetch, cmo), `pmStep`/`pmSteps` labelled by `PEvt` (traces), `pmInit`,
`noPromises`, `validRun`, `pmBehavior`, `traceOf`, `fulfilsOf`, `traceWf` ([R7.s4]: covers LR reads and fetches),
`psBounded`/`promWf`/`cfgWf` ([R7.s1]: bounds `wRmw` and the fetch views).
- M0 (i) (iv) (v): `amoPost`; M1: exclusive forward view = `ts`; M2: forward view = addr ⊔ data; M3: LR address view;
  M4: SC `wLdv ⊔= ts`; M5: rule 8 via `rvView` = LR post-view; M6: TSO halves (emission); M7 kept; M8 uncertified;
  M9 closed form (`loadOk`, `nonFwdMax`), forwarded bytes exempt; M10 `wRmw` slot, aq from the read half; M14 no bank
  (walks deferred; `va` alone reaches `vcap`); M15 no gate; M16 reservation lifetime (no clears at loads/stores/
  fences/AMOs/boundaries), mismatched pairs, `LExFail`.
- [OWN.P2] fetch: `fetchByteOk` (PA-0, floor `wIfl` only, stale allowed, per byte), `fenceIPost` (floor :=
  `vrOld ⊔ vwOld ⊔ wIfr`), PA-1f via `wIfv` in `ldPre`/`stPre` with own-fulfilled-store exemption.
- [OWN.P1] CMO: `invalRead` (cmo.adoc:259–274 bullets 1–3), `cmoPost` (rule 1 / overlap rule via `coh`, W for fences).

`Weak/Prom/Emit.lean` (415 lines): `v2Roles` (DEC-6 sret/mret control dropped), `regSrcs` (M19, D-S0-4, M4/[R3.s2]),
`Ix` channel, `HState`, `bndStep` (end-of-SC `LExFail` unless trapped (FC-5, D-S0-5); optional failed-`amocas`
write-back (ZC-5); Zicbom operation; `LInstr`), `ramRead` (fetch / LR / AMO read / chunked plain load, D-8 fixed),
`ramWrite` (SC success or `.Err ()` failure (FC-1) / AMO write / chunked plain store), `regWriteStep` (nextPC ↦
syntactic `LCtrl` (FC-4); tracked registers ↦ `LRegW`; `mcause`/`scause` set `trapped` (FC-5)), `hnodeStep` (one arm
per `Outcome`; MMIO with nondeterministic answers where no device; `getCycleCount` any value; announce banks bits
only), `hstep` (parked TSO half), `pstepV2`, `satpBare`, `reachH`, `translationOff` (the [OWN.P3] scope predicate),
`hartInit`.

## Decisions (with marks; each also in the docstring at its site)

- D-v2-1 Fetch own-store exemption for PA-1f: an own already-fulfilled source contributes nothing to `wIfv`.
  WEAKER-or-FAITHFUL (the text does not say whether a fetch may forward from the store buffer; mirrors PA-1).
  Alternative: no exemption (Table S §14's formal PA-1f form) — STRONGER if the reference admits forwarding.
- D-v2-2 FENCE.I floor includes `wIfr` (earlier fetches' sources), from zifencei.adoc:77–80's fetch→fetch ordering.
  FAITHFUL under the multi-copy-atomic reading of "visible" (same reading as PA-3); quoted; formal form pending S0.
- D-v2-3 Decomposition chunks are emitted in increasing address order. Order is unobservable on the machine
  (disjoint-byte components: stores fulfil at independent timestamps, loads read at independent points); S0-P
  probes (G5-MIS1/2, CMO-TEAR) decide. Page-crossing order (AD-21) needs translation: deferred.
- D-v2-4 `cbo.inval` is always emitted as an invalidate; under `CBIE = 01` the text says flush: WEAKER there.
- D-v2-5 `invalRead` does not raise the load's post-view to the invalidate's timestamp: WEAKER.
- D-v2-6 MMIO with no device: any read value, any write accepted, fabric unchanged (FC-3, [OWN.P1]): WEAKER-or-
  FAITHFUL (an I/O region's read value is device-defined).
- D-v2-7 `getCycleCount`: any value (C-S constant row): WEAKER-or-FAITHFUL.
- D-v2-8 Failed SC rd: `[]` ([R3.s2]); non-destination tracked register writes: `[]` (D-S0-4 default).
- D-v2-9 M0 (ii)/(iii): the fused AMO's read pre-view includes the address view (rule 9 on the single op); rl is
  not added to the read (D-S0-7 default: subsumed by the write's pre-view and `exclOk`).
- D-v2-10 M16 optional refinement (other-hart stores to SC bytes outside the LR's bytes) not taken: WEAKER.
- D-v2-11 Failed `amocas` (no write) is a load only for ppo (N-12, ZC-6 "treated as an AMO for … PPO"): WEAKER.
- D-v2-12 Dropped `Wstate` fields `wPub`/`wRelp` (INERT) and `wTbank` (M14); class `rel` kept as INERT tag.
- D-v2-13 Instruction-width table `accWidth` covers base/FP loads/stores and the C/Zcb forms; a misaligned access by
  an instruction outside it (e.g. vector) is not decomposed further than Sail's pieces: STRONGER for those forms
  (none in xv6 or the litmus suite); listed for S0-P's C-D audit.

## Deferred by [OWN.P3]: what adding each requires (nothing is assumed meanwhile; scope = `translationOff`)

- **Walks (M14, M18):** label `LWalk base tvs`; `PState` field `wWv` (per-access walk bank) consumed by the next
  explicit access's pre-view (`ldPre`/`stPre` argument beside `va`) and `wLdv`, reset by that access, by `LIFetch`
  (fetch walks are sink-free) and by `LInstr`; admissibility = PA-3 floor `wSfv`/`wSfc` + single read point, no
  `coh`; own-fulfilled sources contribute nothing (D-S0-8); emission: `isTtw` reads become `LWalk` (today stuck).
- **SFENCE.VMA:** label `LSfence (global : Bool)` at the sfence announce (`Weak.sfAnnB`), setting `wSfv := vrNew`,
  `wSfc := wCoh` (D-S0-1 floor `max(vrNew, coh a)`); scoped forms leave it (WEAKER); `cfgWf` must bound it.
- **A/D (M20):** `PClass.ad`; labels `LAdRd`/`LAdWr`; arm `WPAd` (pre-view = read sources only, `exclOk` against ALL
  writes, no COH, no post except `wRmw := none`); emission: the online classifier of M10(1) (next exclusive read
  after a leaf `Read_ttw` with `update_PTE_Bits ≠ none`), A/D writes answered `.Ok (some true)` only; `WPAspec` via a
  speculative `translate` at the `.pure` boundary gated on satp active (SUP-112); lemmas `adData`, `PF.noWCad`.
- **Translation cache (M21):** `regRead tlb` answered with any entry-wise sub-vector (an `hnodeStep` premise).
- **DTctx / DEC-5/6/7:** nothing to add — syntactic sources already exclude them.
- **PBMT, disk agent, PLIC wire, `Efab`:** port `pdiskProg`/`pdiskUart`/`pstepPlic` onto `PLabel`.
- **Page-crossing misaligned portions (AD-21):** with walks; needs either order of the two portions.

## Next

Await SA-1..SA-3 answers; S0-P will extract Table C rows from these files (C-A = `memStep` constructors, C-E =
`hnodeStep` arms + `bndStep`/`ramRead`/`ramWrite` disjuncts, C-F = `PState`/`PAgent`/`PCfg`/`PMsg` fields).
