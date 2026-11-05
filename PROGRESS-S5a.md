# S5a progress — hart lift and register leaves on track (a) (plan rev 7 §7, §8 S5 first item; [OWN.P14])

## Status (top): GREEN, STOPPED at the [OWN.P3] satp trigger (2026-11-05)
- STOP (brief: "Translation stays off ([OWN.P3]) unless a register leaf needs satp facts; then stop and report"):
  the INSTRUCTION-level register leaves AxReuseProbe needs (`wp_s_add`, `wp_s_addiw`, `wp_s_jal`, over `kctx`)
  need satp facts.  `kctxL lent cpu k` (MachCSL/KCtx.lean:874) contains `kConf cpu k.tier k.root …` =
  `confCells … (sConfOf tier root …)` with `satp := satpOf tier root` (SConfDefs.lean:70; Sv39 at `kpt`,
  SConfAtDefs.lean:31–36) and `transSlot cpu k.tier k.root`; the S-mode cycle fetches through
  `swp_translateAddr_tier` (WpSmodeFetch.lean header) at the context's tier.  xv6 runs these leaves at `kpt`.
  Over machine v2 a walk read is STUCK, and `wpA` is MaybeStuck, so a `kpt` leaf would be provable VACUOUSLY
  (`wpHP_walk`, `wpHP_error` make this explicit).  Not attempted; awaiting the owner (OQ-1).
- Second finding (affects S5 sizing even at the `bare` tier): MachCSL proves those leaves through a Sail-cycle
  tower over `MachCSL.swp`/`wpHart` — the closure of `MachCSL.WpSmodeRegOps` is 74 MachCSL files, 42,050 lines
  (`swp_run` automation keyed on MachCSL rule names, `execSpecPP` stage specs, `confCells`/`mConf` bundles,
  fetch/PMP/dispatch/tick specs).  None of it is parametric in the hart wp, so it cannot be re-instantiated over
  `wpHP`/`swpP`; replaying it needs either a parameterisation refactor of MachCSL (an event-rule interface
  class; edits to many existing files) or a rebuild (≫ 8k).  K5a (S5-probe) could not be evaluated: the probe
  needs the instruction-level leaves.
- DONE (PASS part 1 + the event-level part of 2): the hart lift over the REAL Sail emission, its adequacy link,
  and every register / PC / CSR event leaf.  1,161 lines (bound 8k).
- Build: `lake build Weak.Prom.HartAdeq` green (closure HartSwp, HartLift, Emit, OwnAAdeq).
  `#print axioms` of `adequacyS`, `wpHP_lift`, `swpP_readReg`, `swpP_writeReg`, `wpLoopP_restart`:
  propext, Classical.choice, Quot.sound.  No sorry/axiom/native_decide/opaque/implemented_by.
- Workspace edits: NEW files only (`Weak/Prom/HartLift.lean`, `HartSwp.lean`, `HartAdeq.lean`, namespace
  `Weak.Prom.HL`); no existing file touched.  No new named input; translation never enabled.

## The hart-level wp and its adequacy link
- `wpHP cpu m := ∀ rs fn ix, regAuth cpu rs -∗ chanAuth cpu (fn, ix) -∗ wpA g π (hwS cpu) Ψ ⟨cpu, m, rs, fn, ix⟩ True`
  — track (a)'s `wpA` at hart `cpu.val` with program half `pstepV2` (one hart step per Sail event).  Register file
  and channel are ghost-owned, so `wpHP` is indexed by the residual `m` only, as MachCSL's `wpHart`.
  `wpLoopP cpu := wpHP cpu (pure ())`.
- `coreP cpu c` (client resource): the channel's other half + track (a)'s `hartA` (exact views, promises, trace).
  Exposed (not hidden in the wp) so memory leaves see the exact pre-state (plan §7 "kctx must absorb hartSt's
  register views").
- `wpHP_lift` (plan §7 `wpHartP_lift`, MachCSL `wpHart_lift`): one ▷ + £1 per Sail event; callback handed
  `regAuth rs`, the label/successor `pstepV2` allows, the `memStep`, `hartFacts ∨ dshot`, `frontA`; returns
  `stepOk ∨ dshot`, `fulT` at a fulfil, `regAuth h'.rs`, continuation from the new core.  From `wpA_lift` only.
  `wpHP_liftQ`: the same for quiet labels (`quietLab`), obligations discharged once.
- `adequacyS`: every valid run of machine v2 over `pstepV2` from `psOf rs0` (each hart at `hartInit`) meets A0's
  exports (ii)–(v) (Ψ at every prefix, partition, `Valid π img M |M|`, `traceWf`), given `wpPremiseS`: in every
  `PromEnv` the adequacy builds, from the doom box, every `pend`, each hart's initial core and whole register
  file's cells, the client proves every `wpLoopP cpu`.  Proof: allocate register maps + channel ghosts, build
  `PromEnv`, apply `OA.adequacyA`.  (i) termination vacuous (harts never stop, as MachCSL's).

## Leaves proved (HartSwp.lean)
`swpP` (MachCSL `swp` verbatim over `wpHP`) + `swpP_ret/mono/bind/wpHP`; generic `swpP_ev`; `swpP_readReg(_bind)`,
`swpP_readReg_any`, `swpP_writeReg(_bind)` (registers AND CSRs; the Zicsr old-value capture is the read's label
`rdLab`), `swpP_instrAnnounce`, `swpP_branchAnnounce`, `swpP_cycleCount`, `swpP_printEffect`, `swpP_getCycleCount`,
`swpP_choose`, `swpP_barrier`, `wpHP_park`/`swpP_park` (FENCE.TSO second half, M6), `wpLoopP_restart` (`LInstr`
boundary, MachCSL `wpLoop_restartC`); `pcIsP` (MachCSL `pcIs`: PC/nextPC cells, same construction); scope hazards
`wpHP_noStep`, `wpHP_error`, `wpHP_walk`.

## Statements that change (and why)
Event level (vs MachCSL Wp.lean):
1. every event rule takes `coreP cpu c` with `c.fn = none` and returns the core after the step (`qStep`: same
   promises, trace + label, views per `memStep`; channel per the emission) — emission v2's per-instruction channel
   `Ix` and parked fence half; track (a)'s exact hart state.  MachCSL has neither (views in `machInterp`).
2. `swpP_writeReg` drops MachCSL's `hq` (no observed privilege crossing / satp write) and `hk` (no reservation
   kill): v2 observes nothing at register writes, `LRegW` leaves `wRes` alone.  Weaker premises.
3. `swpP_getCycleCount`: every answer (`∀ n`, [OWN.P1]); MachCSL answers 0.
4. `swpP_barrier`: FENCE.TSO's second half is parked (`c'.fn = ebarPark b`), drained by `wpHP_park`.
5. `wpHP_lift`: callback gets `regAuth` + track (a) facts instead of `machInterp`; no reducibility obligation
   (MaybeStuck, plan §2); returns `stepOk`/`fulT`.  No `genCert` (single-boot; plan §7 eras row).
6. Ambient class: `PromEnv` (track (a) names, π, img, M, Ψ with `ψq`, register/channel names), not `MachGS`
   (NA-15 option (ii)); `regP` re-creates `↦ᵣ` at its own ghost map.
Instruction level (AxReuseProbe seam), projected: `Goal := wpLoopP` and `pcIs := pcIsP` survive; `wpNext` survives;
`kctx` CHANGES (definition: core + boundary facts `c.fn = none ∧ bndClean c.ix`, `regP` cells, S5b memory bags
for `stackOwn`/`cpuOwn`/`ctxToken`; `kConf`/`transSlot` only at tier `bare` until OQ-1 — STOP above); `instr`,
`kernelText`, `textInstr`, `kctx_kernelText` CHANGE (fetch = `LIFetch`, a memory event, [OWN.P2]); `wp_s_add`,
`wp_s_addiw`, `wp_s_jal` statements could survive, proofs need the Sail cycle (second finding).

## What S5b needs from here
- Memory events through `wpHP_lift` directly (exact `c.ws`, `memStep`, `frontA`, `fulT`); inversions for the
  `memRead`/`memWrite` arms (`ramRead`/`ramWrite`/devices) in the style of HartLift §4.
- The fetch rule (`LIFetch` with `fetchByteOk`): `instr`/`kernelText` need an owner of the `pend`s of every
  message to text bytes (e.g. a frozen-text invariant); a doomed fetch continues into unknown code, whose later
  fulfils need `fulT` — free mode (`dfree`) or another device; S4a found free mode unusable for xv6 data, so this
  is open.
- `kctx` design: where the core lives at instruction boundaries (plan: inside `kctx`).
- `Ψ` must be quiet-stable (`PromEnv.ψq`; `Ψ = True` works).

## Increment log
1. HartLift.lean (473) — `PromEnv`, `regAuthAt`/`regPtAt` (+ valid/update), `regP`, `regAuth`, `chanAuth`,
   `pcIsP`, `Core`, `coreP`, `qStep`, `hwS`, `wpHP`, `wpLoopP`, `wpHP_lift`, `wpHP_liftQ`, `quietLab`,
   `memStep_q`, `stepOk_q`, `rdLab`/`rdIx`/`wrLab`/`wrIx`, `bndClean`, inversions `pstepV2_*`.
2. HartSwp.lean (475) — `swpP` and the event leaves above; scope-hazard lemmas.
3. HartAdeq.lean (213) — `psOf`, `cpus_idx`, `regCellsAt`, `regsP_alloc_one`, `chan_alloc_one`,
   `namesP_alloc_list`, `wpPremiseS`, `adequacyS`, axiom audit.
