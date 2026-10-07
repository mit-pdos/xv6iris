# Q7: the sfence.vma marker as a graph event (design, 2026-10-07, w4)

Owner ruling Q7 (weak-port-architecture.md, "Q6/Q7/Q8"): `sfence.vma` gets its own
marker label. The label is an LFence-class graph event, so H5' no longer uses the
instruction's fetch as its sfence point.

## What SFENCE_VMA already emits (symbolic model)

`execute_SFENCE_VMA` (model/Lean_RV64D/LeanRV64D/InstsEnd.lean:18009) and `flush_TLB`
(VmemTlb.lean:349) emit only register events. These are `regRead` of rs1/rs2,
`cur_privilege`, `mstatus` and `tlb`, plus `regWrite tlb`. The `tlb_flush_*_callback`
calls are pure `let _` stubs, and there is no `barrier`, `tlbi` or `cacheOp` outcome.
The `tlb` reads are not unique to sfence either: `lookup_TLB` (VmemTlb:311) reads `tlb`
on every translation. So no outcome emitted inside execute can be used as the marker.

The instruction does emit one outcome that carries its identity. Under `-D SYMBOLIC`,
`run_hart_active` emits `instrAnnounce 32 w` for each base instruction (Step.lean:377).
That point is after the fetch and before decode and execute. Nothing between the
announce and the end of execute touches memory. So, in program order, the announce has
the same position as execute.

## Design (a): the weak tier reads the sfence announce as a fence marker

- **Graph label: no new `Lbl` constructor.** The marker is `Lbl.LFence false false false
  false`. This is the original Rocq marker form, already modelled by
  `AxPtProt.gsfence`/`ptwWf`/`AxPtProt2.sfLblB`. It is also what `ebarLabel
  .Barrier_RISCV_i` produces today, so the label is already a hart-node label in every
  tier. `fencePost` with all four bits false is the identity, and the label creates no
  ob edges.
- **Instance label: no new `Wlabel` constructor.** In WeakEvLang, add
  `sfAnnB (n) (w : BitVec n) : Bool := n = 32 ∧ w &&& 0xFE007FFF = 0x12000073`
  (the SFENCE.VMA opcode pattern, any rs1/rs2) and
  `annLabel n w := if sfAnnB n w then LFence false false false false else LInstr`.
  The `pnodeStep` arm for `.instrAnnounce n w` becomes `l = annLabel n w` (the bits are
  banked as before). `WeakRvwmoAdm`'s private interpreter (line 194) changes the same way.
- **Unchanged:** projLbl, lbAdmin, lblIdent and wlFence (the LFence arms already do the
  right thing). AxOpsem gets no new constructor: the marker is realized by the existing
  `AStepFence` against a row item `LFence f f f f`. The AxGraph* predicates and the cat
  checkers do not change.
- **Semantic point to check (W2b).** At an sfence announce, the label `instrPost` (the
  "second LInstr" reset of wLdv/wRes/wTbank) is replaced by the identity fence. The
  reset still happens at the boundary `LInstr`. What it skips is the PTW loads of the
  sfence's own fetch translation. If that reset turns out to be load-bearing, the
  fallback is a new `Wlabel.LSfence` with `instrPost` semantics that projects to
  `Lbl.LFence ffff`. That fallback adds an arm to about 70 exhaustive matches in 25
  files.
- **Faithfulness.** An illegal sfence (U-mode, or TVM set) also emits the marker.
  `gpSf` may leave that marker untagged (`ptwWf` only requires tagged → marker), the same
  as in the fetch form.

## Proofs that break (they treat a generic-word announce as an admin step)

The per-arm fixes are routine: `simp [annLabel]`/`split` in the arms in WeakEvInst
(×7), WeakEvPf, WeakEvProv, WeakEvLift, WeakRvwmoCert2/3b and AxOpsem:608, plus `decide`
on concrete words (WeakRvwmoCycWit, AxFetch*). `pnodeStepCases` still holds, because the
marker is `ebarLabel .Barrier_RISCV_i`.

The real breakage is in the generic "a register-only run is a position-keeping admin
run" lemmas. For a run that announces an sfence word they are FALSE, so each one needs a
"no sfence announce" premise, or its local interpreter must reject sfence announces:

- `AxFetch1.afAdminRunToMemread`/`afAdminRunToMemwrite` (callers: AxFetch2/3/3b/3c);
- `AxFetch3.afAdminRunToEnd`;
- `AxBoundaryWpd.erunGstep`/`erdGstep` (`erun`/`erd` are local, so make them return
  `none` at sfence announces; caller: AxEpiProbe);
- **`AxCjrWpd.epureGstepRtc` (lines 130-134: `.LInstr` + `rfl`).** AxCjrWpd is
  FORBIDDEN for this task, because another worker is changing it. Every variant of
  design (a) breaks this proof.

## AxSfence after the change

- `sfFetch` becomes `sfMark G f := gxLbl G f = some (LFence false false false false)`.
- `gsfenceF`/`ptwWfF`/`ptwModelF` coincide with `gsfence`/`ptwWf`/`ptwModel` (AxPtProt).
  `sfCoversF` keeps Rocq's `e = f` disjunct, which is inert at a no-op fence.
- §3 `ptwModelMarkerIff` reads "fetch form = marker form" and is restated as the identity
  of the two forms.
- §4 delegates to `AxPtProt2.ptwModelB`.
- §5's rows put `LFence f f f f` where `LFetchSf` was, giving AxPtProt2's `gad`/`gsf`/
  `gsfok`. `gAdSoundF`/`gsfNotH5F`/`gsfokSoundF` then hold on the marker (the "(0,1)" tag),
  and `gadmBoth` states the marker graph's model under both tags.
- §1 `sfWord`/`sfWordXv6` stay. They link `sfAnnB` on xv6's word 0x12000073 to the
  Sail decode.

## Status

Design (a) works, but it cannot be implemented green without editing
`AxCjrWpd.epureGstepRtc`. This task forbids that edit, so implementation is deferred
until the AxCjrWpd/WP-step-clause worker lands.

Alternative (b) is a model edit, which is not to be made here. It would add a `barrier`
(or `tlbi`→fence) outcome in `execute_SFENCE_VMA` on the RETIRE path. That puts the
marker at execute, and only on success. The generic admin-run lemmas already exclude
`.barrier`, so none of them break. The SC tier's sfence proofs (MachCSL/WpSmodeSfence,
UExecCtl*) would need one extra barrier step.
