# The event-granular weak language — design (supersedes the two-machine lift)

**Status (2026-08-14): DESIGN, spike in flight
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

## State and expressions (σ-resident thread state)

Per the tree's long-standing methodology — registers including the PC
live in σ, expressions are opaque generation-indexed thread tokens, and
WP proofs track progress through exclusive state resources plus Löb, not
expression structure — ALL thread-private program state lives in σ:

- σ = today's `wgstate` extended with, per CPU: `hs : option (M unit)`
  (the residual instruction monad; `None` = boundary) and the parked
  fence; plus the canonical disk `pend : list wmsg`.
- Expressions stay `LoopE gen cpu` / `DiskLoopE gen` / … tokens, so the
  whole power/generation machinery (corpse arms, PowerOn forking the new
  generation's tokens) is untouched; σ's slots belong to the live
  generation exactly as `wgregs` already works.
- New exclusive ghosts mirror `reg_pointsto`: `hart_prog cpu ↦{1} hs`,
  the fence, `disk_pend ↦{1} _`, tied to σ by the state interpretation.
- The `psail` oracle components (`sp_dev`, `sp_irq`) DO NOT EXIST: device
  arms read the shared fabric σ.dev directly; interrupt delivery reads
  the PLIC wire from it.  The device seam collapses at the definition.

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
