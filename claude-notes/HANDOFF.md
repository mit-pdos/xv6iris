# SESSION HANDOFF — 2026-08-18 (branch `weak-memory`)

**LATEST (2026-08-18, HEAD pushed): everything green; nothing in flight.  The
user is deliberating on the CERTIFICATION ROUTE for Layer 2
(`design/weak-memory-layer2.md` §8/§10 — NO side conditions: early reads
become pf reads via the promise author's certifying run, φ refutes early
reads of owned-unpublished messages, sync bytes by machine facts + the
exported lock-word value protocol) and will say when to start D8.  DO NOT
start D8/E1/L2′ without that go.  Landed since the previous handoff:
`-D SYMBOLIC` model; D2/D3 dependency tracking (D-7 forward bank fixed);
A0/A0′/A0″ premise repairs (`main_premises` = `edges_split_cyc ∧ bad_wf ∧
ee_ok ∧ dev_wit_ok ∧ bytes_ok`, `robust_main_acyc`, `robust_main_l2`);
L2-M1/M2 (`WeakRobustL2.v`, `WeakRobustL2b.v`: SCC skeleton, `U_Qinv`,
`head_prestate_pf_real`, `sf_edges ≡ edges_split_cyc`); M4-1 first slice
(`WeakEvFunnel/Wire/ExecEff/Disk`).  Open technical questions before D8:
(1) whether PARM's `interference_certify` transfers to our machine without
the `RES = ts` view (ANSWERED: `design/weak-memory-layer2.md` §11 + `design/parm-certification-notes.md`
— completeness uses the ARCH-GENERIC restriction lemma, `RES` unused, our
D2 machine suffices; real risks = fabric, lat reads, fused RMW); (2) speculative A-bit
updates vs the acyclicity route (§10).**


**LATEST (end of day): the Sail model is now generated with `-D SYMBOLIC`
(`d978b255`): `riscv_step` emits `InstrAnnounce`/`BranchAnnounce` nodes; 12
one-line proof fixes; tree green; capstone on the 5 axioms.  Plans of
record for what comes next: `design/weak-memory-deps.md` (dependency
tracking in the full machine + a machine-checked Layer 2 — awaiting the
user's go on D2+), `design/weak-memory-premise-discharge.md` (the
`main_premises` findings: `edges_split` and `dev_epoch_ok` are FALSE for xv6
as stated — Track A0/A0′ repairs owed), `projects/weak-memory-m4-retarget.md`
(the `exec_eff` bridge spike PASSED).  Landed the same day after the
capstone: `WeakEvDisk.v` (disk-thread EWP rules), `WeakRobustDisc.v`
(Track A1–A6), `WeakEvExecEff.v` (M4-S1).**


**State: tree green, everything committed on `weak-memory` (NOT pushed —
push when the user wants).  No work in flight.**  Entry point as always:
`README.md` → `durable-notes.md`; then the worklist below.

## What this session did (one paragraph)

THE ONE-MACHINE SOUNDNESS CAPSTONE IS CLOSED: `iris/WeakEvCapstone.v`,
`xv6_ev_weak_robust`, on exactly the five rv64d axioms — event-language
adequacy ∘ (the event language IS a Layer-1 instance, both directions,
every arm) ∘ generalized Layer 1 (`robust_main`), with the promise-free
witness run shown to be a run of the language itself.  Premises: the WP
package (the only Iris-side obligation), four fresh-era facts about σ0,
`main_premises` served at canonical bundles.  Gone relative to the archived
lifted capstone: `rv64d_axiom_shapes`, `rv64d_live_residue`, `img_total`,
`xv6_cone_premises`, `cone_liftable`, and every lift-era glue premise.  It
became possible because the disk was made a genuine weak-memory AGENT (M5,
`design/weak-memory-m5.md`): the virtio device is a read/write/fence monad
program (`iris/VirtioProg.v`) that acquire-loads `avail->idx` and reads/
writes at its own view; driver/device synchronization is message passing
through the rings; the doorbell/ISR are hints.  Layer 1 changed only by the
`pcls` retype (`P → wlabel → wstate → wm_class`) and the fabric-marker
label `LDev`.  Worklist with the per-item record:
`projects/weak-memory-soundness.md`.  Commit range: `4f636d09..HEAD`.

## Findings of the session (all recorded in the worklist/design)

- `ev_dma_harmless` (the fabric worklist's fallback packaging of the disk
  arm) is FALSE for xv6 (fictional DMA memory ⇒ garbage writes anywhere ⇒
  hart violations reachable).
- The flat DMA read was a hardware-fidelity gap (device could never see
  stale ring memory), not just a proof-plumbing one.
- The generated Sail model DROPS FENCE I/O bits (`fence iorw,iorw` arrives
  as `rw,rw`; a bare `fence w,o` is no barrier).  Moot for safety under M5's
  ring-message-passing model; recorded as a device-model assumption.
- `virtio_complete`'s gmap nesting has the reverse precedence of any
  barrier-honouring device on overlapping writes; the map half of the
  device-program equivalence carries a `NoDup`-written-addresses side
  condition (`VirtioProg.virtio_prog_disj`).
- Per-label ⇐ (`epf_step` ⊆ `wp_pf_step` at the same label) is false at
  `fence.i` (`elabel_ok` under-determines the label); the run-level form is
  exact and is all any consumer needs.
- `robust_main` needed a bundle-argument form (`robust_main_bundle`) for
  the retag precomposition; `WeakRetag.ptraces_dev_of_retag` added.
- Proof-engineering: `f_equal` on `WPCfg` equalities is unreliable when
  `simpl` expands `enum CPU`; rewrite pre-established agent-list equations
  instead.

## What is next (in priority order)

1. **C4 — the disk thread's WP** (M4-port track): per-node EWP rules for
   `EDisk` (twins of `WeakEvLift`'s hart rules at `dws`) and the driver
   proof that `DWild` is unreachable — this DISCHARGES the WP package's
   disk conjunct; the capstone takes the package as a hypothesis.
2. **Phase-2 discharge of `main_premises`** (`projects/weak-memory-premises.md`
   phase 2 — exhibit-level, from per-site tokens; now with the fabric
   witness `DS` and `dev_epoch_ok`).
3. **The M4 leaf retarget** to the event interface (spec-preserving
   packaging; budget ≈1.2× time / 1.7× lines per leaf, spike numbers).
4. **RVWMO containment** upgrade of `WeakCompose` §6(5) (`WeakAxiomatic*`).
5. Tidy: move `projects/weak-memory-fabric.md`, `weak-memory-event-lang.md`,
   `weak-memory-premises.md` to `completed/`; retire the lift tree per
   `design/weak-memory-event-granular.md` "What dies" once M4 lands.
