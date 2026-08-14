# The event-granular weak language — design (supersedes the two-machine lift)

**Status (2026-08-14): DESIGN, spike COMPLETE and PASSED
([`projects/weak-memory-event-lang.md`](../projects/weak-memory-event-lang.md)).
The instruction-atomic architecture it supersedes is retained side by side
— [`weak-memory.md`](weak-memory.md), the lift record
([`../completed/weak-memory-lift.md`](../completed/weak-memory-lift.md)) and
the premise-elimination worklist
([`../projects/weak-memory-premises.md`](../projects/weak-memory-premises.md))
— deliberately: its failure record is the evidence for this design.**

## The diagnosis this design answers

Eight sessions of lift/premise work produced ten machine-checked findings
and a premise ledger that changed shape without converging.  The distilled
root cause: **the program logic's machine (instruction-atomic WeakLang) is
not the machine the robustness theorem talks about (the event-granular
promise-free machine), and every glue assumption was a shadow of that one
mismatch.**  `sail_shaped` existed to reconstruct instructions from event
runs; `sail_live`/`rv64d_live_residue` to complete them; `Hcq` to make the
cone replay block-contiguous; `Hseip` to commute deliveries out of blocks;
`Hpriv` to gate completion liveness; the oracle streams (and their
unsatisfiability finding) and `cone_liftable`'s fabric agreement came from
the two machines carrying separate device state; `cls_canonical`/the retag
from the free class binder the reconstruction had to match.  Six of the
findings were refutations of hand-written ∀-statements about a
3000-definition generated model — the characteristic failure mode of
specifying a model's future behavior instead of consuming what its steps
witness.  None of the findings ever touched the promising→promise-free
robustness argument itself (W1–W5 stable throughout): the promise-free
MODEL is right; having TWO machines is what failed to converge.

## The design in one sentence

Make the logic's machine BE the promise-free machine: an Iris language
whose per-thread step is ONE event, defined so that its erased-step
relation is `wp_pf_run (pstep_xv6 riscv_step)` BY CONSTRUCTION (a
definitional bijection, not a simulation), so `pf_violation_free_hart`
falls out of adequacy in a page and the lift ceases to exist as a concept.

## State and expressions (REVISED 2026-08-14: expression-resident monad)

THE PLACEMENT RULE (the user's insight, and the recorded reason): put
control state in the EXPRESSION exactly where control flow is
MODEL-DEFINED, and in σ where it is MEMORY-DEFINED.  The tree's
σ-resident methodology (registers incl. the PC in σ, boring thread
tokens, progress by ghost resources) exists because INTER-instruction
control flow is memory-defined — what runs next depends on a fetch
through a page table into mutable memory, all of which must be proven,
so no stable syntactic continuation exists at instruction granularity.
INTRA-instruction control flow is model-defined: the continuation IS the
Sail monad value given by `riscv_step`, syntactically known and
monotonically consumed.  So:

- σ = today's `wgstate` VERBATIM (no new fields).  The state
  interpretation is `weak_state_interp` unchanged; φ/`no_violation`
  applies literally; no new ghosts.
- Hart expressions: `LoopE gen cpu` (the boundary token — preemption
  points and the unknowable next instruction live here) steps to
  `CycleE gen cpu (m : M unit) (fence : option …)` — the architectural
  execution of ONE instruction, monad and parked fence in the
  expression; the monad rules reduce `m`; `CycleE … (Ret _) …` pops
  back to `LoopE`.  WP-of-an-instruction becomes proof by syntactic
  descent, and composition along the monad is a `wp_bind`-style lemma
  over `CycleE` — the SC side's `wp_exec` pattern at the language level.
- Devices: whole operation state in the expression — `DiskE gen
  (pend : list wmsg) (dws : wstate)` matching the pf `PDisk` agent
  field-for-field (empty buffer = idle; devices have no
  preemption/fetch problem, so nothing forces a boundary form).
- Interrupt delivery is ONLY the PLIC thread's cross-thread σ-register
  write (as in today's WeakLang) — an asynchronous wire that fires
  regardless of the hart's expression form.  No hart-side delivery arm.
- Generation machinery unchanged; `CycleE` gets corpse arms like
  `LoopE`'s.
- The `psail` oracle components (`sp_dev`, `sp_irq`) DO NOT EXIST: device
  arms read the shared fabric σ.dev directly; interrupt delivery reads
  the PLIC wire from it.  The device seam collapses at the definition.
- The pf correspondence gets MORE direct: `wpcfg`'s agents carry their
  program state (`pa_st`), so pool-of-expressions maps to agent-list
  field-for-field.

## The step relation — one arm per event kind

| event | effect |
|---|---|
| boundary | `hs = None` → `Some (riscv_step tick)` |
| silent node (RegRead/RegWrite/announce/Choose/…) | monad advances; registers via σ |
| RAM read | `read_ok` against σ.log + own `ws`; `load_post` |
| RAM write | append `WMsg … (wm_class_of ak ws)`; `store_post` |
| fused RMW | exclusive read + silent window + conditional write, ONE event (`excl_ok` atomic) |
| device read/write | `dev_read`/`dev_write` against σ.dev |
| fence / fence.tso park+fire | `fence_post`; fence in σ |
| irq delivery | `sig_seip := wire(σ.dev)` |
| disk burst / emit | one `wdisk_step` at `wflat σ`, then one emit per step (1:1 with the pf disk agent) |

Three deliberate decisions: the RMW stays FUSED (lock acquires stay
one-invariant-access; `excl_ok`'s window atomic); the store arm COMPUTES
the message class (`wm_class_of` at the hart's own ws — no free binder,
so `cls_canonical` and the retag die by construction); stuck nodes
(`GenericFail`, zero-width writes, undecodable junk) are just stuck — no
`sail_shaped`, no `sail_live`, no decoder postcondition, because nothing
ever completes or reconstructs an instruction: a shape predicate was only
ever a promise about an instruction's FUTURE, and no rule here mentions
the future.

## What the logic looks like

Standard Iris lifting over these steps; the state interpretation is
today's (log auth, per-hart views, C/D/S per byte, device ghosts),
re-established per event — weaker per step than the instruction-atomic
interp (reads don't move the protocol; the store event is the same single
point it always was).  Existing leaves port through ONE generic
INSTRUCTION-CHAIN LEMMA: the current certifications already run the
interpreter through the instruction's monad; the same data unrolls into a
chain of event-WPs.  Whole-function proofs compose leaves as before; the
SC-parity layer (`cobj`/`ctx_view_lb`) is about resources, orthogonal to
granularity.

## What dies / what survives

DIES (archived, not deleted — the failure record): the bracket files and
lift tree (`WeakInterp` wrun-as-language-step, `WeakSailLTS`/`2`,
`WeakSailComplete`, `WeakSailCone`, `WeakRobustCone`, `WeakComposeLang`),
the shape towers (`WeakShape*`), `WeakRetag`, the oracle machinery, both
axiom-shape records, and the lift-induced premises (`Hcq`, `Hseip`,
`Hpriv`, `cone_liftable`, `cls_canonical`).  SURVIVES unchanged: the
promise-free machine and Layer 1 (W1–W5, `WeakPromise*`, `WeakRobust*`,
`WeakCompose`'s headline), the state-interp/protocol design, the parity
layer, the generation/crash machinery.  END-STATE LEDGER:
`main_premises` (the genuine robustness content, discharged by the
exhibit-level route of the premises worklist's phase 2) + the WP package
+ the 5 rv64d axioms + the PARM containment note.

## Bonuses beyond the ledger

- THE WALK-BRIDGE DISSOLVES: "the walk reads its leaf slot twice in one
  step and a kind-blind exec cannot make one memory return two different
  values" was a granularity artifact — two reads are two events.  The
  `WeakStale` stale-memory mirror is unnecessary at event granularity.
- The disk agent matches the pf disk 1:1; the `wa_dd = wgdev` and
  flat-memory-pinning residues disappear.

## Proof engineering: reflective batching is MANDATORY, over TOTAL
## PROJECTIONS AND UNEVALUATED COMPOSITIONS (revised 2026-08-14, post-spike)

THE COMMITMENT: the language's step granularity must not become the
proof's step granularity.  Stepping the proofmode through every bind
(an interp-open per `RegRead`) would be strictly worse than today's
vm_compute-style execution and is forbidden as the proof interface
(measured: ~19 ms of proofmode per node ⇒ ~5.6 s per real instruction,
against ~0.15 s for the same instruction in three batched stretches):

- Per-node rules are the SEMANTICS (for the correspondence and
  adequacy).  The PROOF INTERFACE is one derived rule per SILENT
  STRETCH: a reflective `erun_silent : nat → footprint → regfile → M unit →
  regfile × M unit` (the `DecodeSetU.bval`/`goodbP` mold) computing through
  consecutive non-memory nodes to the next memory event / fence / `Ret`.
  Its soundness lemma and the Iris n-step rule are proven ONCE.
- **THE FORM RULE, and it is load-bearing (spike finding F8): NO CALL SITE
  MAY EVER WRITE A RESIDUAL — OR A REGISTER FILE — DOWN.**  Naming a residual
  monad means reading a VM *closure* back into a term, which re-does the whole
  rest of the instruction symbolically (measured: >110 s, killed, against
  0.1 s for the same run projected to a number); naming the post-boot register
  file costs >3 min.  The durable-notes
  compute-once-into-a-`Definition`-plus-`vm_cast_no_check` recipe was written
  for VALUES and does not transfer.  So the interface is:
    * a CURSOR `ecur = regstate * M unit` with TOTAL steppers
      (`esil n D`, `ecur_read v`, `ecur_write`, `ecur_bar`, `ecur_loop tick`).
      A certification — of one instruction or of a whole sequence — is a
      CHAIN OF APPLICATIONS, never normalised;
    * the batched rule takes **no equation at all**: its successor is the
      unevaluated composition;
    * TOTAL PROJECTIONS with SMALL outputs are what a rule matches on
      (`enode_tag`, `eread_req_at n`, `ewrite_req_at n`, `ebar_at`), each
      per-site fact one `vm_cast_no_check` with a hand-written right-hand
      side, plus ONCE-PROVEN inversion lemmas exhibiting the continuation;
    * per-site cost is then O(1) on BOTH axes: 0.16 s of VM for a whole
      293-node instruction, and no readback but a five-field request record.
  GOTCHA (durable): discharge a cursor equation with
  `have H : … by reflexivity` and PASS `H`.  A bare `eq_refl` inside the
  application hands the problem to the elaborator's unifier, which unfolds
  the stepper instead of the cursor and starts LAZILY EVALUATING the stretch
  (5.3 s, then unbounded).
- **THE FETCH IS A MEMORY EVENT, AND IT GETS ITS OWN DERIVED RULE (finding
  F7).**  Decision 6 ("instruction fetch is declared coherent") is NOT what
  `riscv_step` emits — the fetch request classifies as an ordinary
  `AK_explicit` plain read — so every instruction carries one memory event
  more than its instruction-atomic twin.  The answer is not to change the
  model but to exploit that KERNEL TEXT IS IMMUTABLE: `ewp_ev_fetch` consumes
  the persistent era-image points-to (`WeakInstr.wkernel_text`'s elements,
  windowed as `etext_word`) and concludes the fetch returns exactly the
  certified word, with no caller callback, no `read_ok` obligation and no φ
  payment — because a never-written byte forces every admissible timestamp to
  0 and owes nothing at any floor.  Every leaf that fetches should use it.
- DECODE IS IMPORTED, NOT RE-SOLVED: after the fetch event,
  decode+prologue is one silent stretch = one reflective step; the
  `kd_` catalogue / `decode_bridge_ms` / concrete-state bridge are
  consumed inside `erun_silent`'s computation unchanged.
- CERTIFICATIONS LIFT WHOLESALE: the chain lemma's real form is an
  adapter from today's certification data to `EWP (ECycle …)`, with
  obligations ONLY at memory events (`ewp_ev_seq_load` / `_fetch` / `_store`
  / `_barrier` / `_ret`).
- WHY BATCHING IS SOUND: a silent stretch touches only hart-exclusive
  state (own registers, own expression), so interference neither
  disables it nor changes its result — frame once across the stretch.
  Memory events are exactly the points where the world may act, and
  are NOT batched.
- MEASURED PARITY (S5, both sides re-measured in one session): 1.19× the
  instruction-atomic leaves' time on three whole-function leaves, 1.03× with
  the two-instruction composition, 1.66–1.78× the lines — the line residue
  being the per-event ITEMISATION of the certification in the statement.

## The risks the spike must test (fail criteria, named in advance)

1. MID-INSTRUCTION INTERFERENCE IS REAL SEMANTICS: the log can grow
   between an instruction's own events.  Leaf specs must be
   interference-stable at every event; the view discipline is built for
   this (floors monotone), but this is the load-bearing unknown.
2. INVARIANT GRANULARITY shrinks to one event: anything relying on
   opening an invariant across several events of one instruction must
   move to a ghost protocol (audit: the walker read-then-CAS — two
   events now — and any twice-peeking leaf).  The fused RMW keeps the
   lock cases safe.
3. VOLUME: every weak leaf re-glues through the chain lemma — mechanical,
   and cheaper before the M4 port targets more files at the
   instruction-atomic interface.
