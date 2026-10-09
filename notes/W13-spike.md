# W13 spike: the graph-tier fabric and the dev-order trusted-base item (R5 [R5.1], [OWN.8])

2026-10-09.  Read-only investigation, plus one scratch file `Weak/W13Spike.lean` (145 lines, builds
via lean-gcp, no sorry or axiom).  The `file:line` cites point at this workspace (identical to
`../xv6iris-weak` for every merged file).

## Verdict

**[R5.1]'s vacuity claim is CONFIRMED.  But the item is mis-sized, and [OWN.8]'s axiom, read
literally, is the wrong trusted-base item.**

1. **T2-1c′ already LANDED.**  The review and route-b both say "PARKED", which is stale.
   `Weak/WeakRvwmoLin2.lean` (1,037 lines, "T2-1c′, the trace-flexible linearization") together
   with `Weak/WeakRvwmoFloor.lean` (1,036) prove `gtraceLinearizationMin` (`Lin2:623`): any trace
   extending `po ∪ rf ∪ gmo|W` gives an `srvwmoConsistent` cand.  §7 adds the dev-order version:
   `gfexecConsistent'` (`:761`), `ptraceExistsF` (`:836`), `trDevOrderedOfPtrace` (`:944`), which
   DISCHARGES FabInd's handed-back guard, then `fconfSupply'` (`:995`) and `fconfTraceRealize`
   (`:1012`).  The capstone `xv6RvwmoSafeModuloF` (`Capstone.lean:228-265`) is built on them.
2. **[OWN.8]'s literal axiom (= `gfexecConsistent'`) cannot be a premise of a FULL-RVWMO
   theorem.**  On the quantified graph, `po ∪ rf ∪ gmo|W` acyclic rules out load buffering and
   W→W reordering, even with no devices at all.  Machine-checked: `lbExcluded` shows the LB graph
   is `rvwmoCatConsistent` but fails `gfexecConsistent' ⟨lbgd, []⟩`.  That contradicts [OWN.2].
   It also makes the kill unnecessary: `xv6RvwmoSafeModuloF` carries no `l2Claim` and no
   `walkSupply`.  So it is a robustness ASSUMPTION, not a hardware model.
3. **Any dev-order condition at the block level excludes plain SC executions.**  This is a model
   defect and no choice of axiom fixes it.  `execProgOk'` (`WeakAxRealize.lean:373-384`) folds a
   step's admin star, `LDev` included, ATOMICALLY into the next tagged graph event.  Take
   `w13f = ⟨mpgd', [(0,0),(1,0)]⟩`.  This is SC: MMIO₀, then MMIO₁, then hart 1 stores x, then
   hart 0's load reads x = 1.  `scDevExcluded` shows it is cat-consistent and rule-14, yet it
   fails BOTH `gfexecConsistent'` and FabInd's `gdevAdj ⊆ gmo`.  `scDevUnrealizable` shows that
   NO `ptraceExt` trace visits the blocks in fabric order.  So the realized graph-tier semantics
   cannot represent it.  For the 3-hart version, I checked by hand that every choice of folding
   MMIO onto the previous or the next event fails, so a fix that only changes the attachment
   point is not enough either.
4. **Recommended trusted-base item `ioObAcyclic`** (statement below; in the scratch file).  It
   extends gmo with I/O nodes that are ordered by program order against the issuing hart's
   memory events, and among themselves by the fabric.  At an empty fabric it is free
   (`ioObAcyclicNodev`), so LB and W→W stay in the quantifier.  It admits `w13f` (`w13fIoOk`).
5. **Size: W13 is XL, not "L–XL".**  It needs a realization-interface change (admin-only trace
   steps), a kill that also covers dev edges, and a re-thread of the ~8.6k-line kill pipeline to a
   moving fabric.  About 3.6k lines can be reused as is (Fab, FabInd, Lin2, Floor).

## Evidence: the vacuity ([R5.1], re-confirmed)

- `gdexecQconf` requires `emDevfree em` of every row (`WeakRvwmoSupply.lean:281-289`), and
  `emDevfree em := LDev ∉ emLabels em` (`:273`).
- MMIO and the disk emit `LDev` (R5's cites `WeakEvInst.lean:300-303,335-338,484,502`).  The
  projection drops it: `projLbl _ .LDev = none` (`WeakPromiseBridge.lean:537`).
- Hart 0 runs consoleinit and uartinitone before userinit, so allocproc is unreachable in every
  `gdexecQconf` graph.
- The fabric bundle `gfexecConf` (`Fab.lean:523-535`) is non-vacuous only at `gfDev = []`
  (`gfexecConfOfQconf`, `:648`).  No `LDev`-emitting emission witness exists anywhere in the tree.

## What exists, what it hands back

| piece | file:line | status |
|---|---|---|
| bundle `Gfexec`/`gfexecConf` (dev blocks, `fab`, `hemitf` with two endpoints) | Fab 516-535 | landed, leaf |
| `gfexecConsistent` (`gdevAdj ⊆ gmo`) | Fab 542 | landed; `scDevExcluded` refutes it as a hardware model |
| `supplyOfFconf`/`fconfSupply` | Fab 689, 826 | landed; last premise = the trace visits `gfDev` in order |
| hull/renaming O1–O5, `cycleKillF`, `t2linSupplyF` | FabInd 397-540 | landed; `trDevOrdered` HANDED BACK (`:407`) because `linCand` ignores the fabric (§5, `lbfNotDevOrdered :583`) |
| T2-1c′ + dev version (guard DISCHARGED) | Lin2 623, 761-1037 | landed; premise is `gfexecConsistent'` |
| `xv6RvwmoSafeModuloF` | Capstone 228-265 | landed; premise `gfexecConsistent'` (finding 2); no kill |

**`fconfSupply` audit.**  It has exactly two consumers: `fconfRealize` (FabInd 413) and
`fconfSupply'` (Lin2 995).  Both are sound.  The weak point is upstream, in finding 3.  Every
`fconfSupply` trace step folds the dev block into a tagged step (`supplyOfFconf`'s `hblk'`), so
the supply inherits the defect.

## Consumers that must move from `gdexecQconf` (constant fabric) to the fabric bundle

Counts are measured: lines, then `Qconf` mentions, then constant-fabric (`fun _ => d0`) sites,
then `hemit`/`hartConf` uses.

| file | lines | Qconf | constfab | hemit | role |
|---|---:|---:|---:|---:|---|
| WeakRvwmoSupply | 917 | 35 | 12 | 14 | `topoSupply`, `qconfRows`, Hull/Ren |
| WeakRvwmoLinInd | 327 | 12 | 2 | 0 | `cycleKill`, `hullRealizableOfAcyclic`, `t2linSupply` |
| WeakRvwmoCert4 | 750 | 1 | 2 | 1 | `hullRealizableRowsG` (:151), `cstOk` |
| WeakRvwmoGlue | 620 | 6 | 2 | 0 | `hullRun`, `l2Claim`, `cutSupply`, `certSupply`, `bootTie` (`RunData` is already `dv`-generic) |
| WeakRvwmoGlue2 | 580 | 10 | 1 | 0 | `cycleKillOfL2''`, `walkSupply` |
| WeakRvwmoWalk / Walk2 / Walkb / Walk3 | 928 / 948 / 1116 / 139 | 3 / 26 / 9 / 5 | 2 / 16 / 3 / 1 | 4 / 17 / 2 / 0 | segment replay at constant fabric (`wemit d0`) |
| WeakRvwmoProgress | 437 | 3 | 4 | 3 | `walkSegData` |
| WeakRvwmoPreNorm / PreNorm2 | 814 / 734 | 12 / 4 | 2 / 0 | 0 | Ren transport (twin `gfexecConfRen` exists) |
| WeakRvwmoCapstone | 290 | 10 | 4 | 0 | root restated |

Total: 8,600 lines, about 140 bundle mentions and 52 constant-fabric sites.  The witness files
(Adm, CycWit, ConfWit, ConfWit2) stay as they are and embed through `gfexecConfOfQconf`.
KillArms, Hull and Lin do not change except for the new arms below.

## Recommended design (exact statements)

**(T) TRUSTED-BASE ITEM.**  This replaces [OWN.8]'s literal form.  It is a hypothesis of the
published theorem, named in its header, and it is not a Lean `axiom`.  It is checked in
`Weak/W13Spike.lean:83-95`:
```lean
inductive Ioev | ev (e : Geid) | dv (i k : Nat)   -- dv i k: hart i's I/O between events k-1 and k
def ioOrd (GF : Gfexec) : Ioev → Ioev → Prop
  | .ev x, .ev y => gmoLt GF.gfGd.gdG x y
  | .ev x, .dv i k => (i, k) ∈ GF.gfDev ∧ x.1 = i ∧ x.2 < k ∧ gmem GF.gfGd.gdG x
  | .dv i k, .ev y => (i, k) ∈ GF.gfDev ∧ y.1 = i ∧ k ≤ y.2 ∧ gmem GF.gfGd.gdG y
  | .dv i k, .dv j l => (i, k) ∈ GF.gfDev ∧ (j, l) ∈ GF.gfDev ∧ ((i = j ∧ k < l) ∨ gdevAdj GF (i, k) (j, l))
def ioObAcyclic (GF : Gfexec) : Prop := ∀ x, ¬ tc (ioOrd GF) x x
```
How to read it: riscv.cat's global memory order, extended with xv6's MMIO accesses as I/O
events, is acyclic.  Each I/O event is ordered against its own hart's memory accesses in program
order (strongly-ordered I/O), and I/O events are ordered by the device fabric.  It holds
trivially at an empty fabric (`ioObAcyclicNodev`).  It does not assume `racyD` acyclicity: the
kill still carries that content.

**(I) Interface change: a dev block becomes its own trace step.**  Add `execProgOkA`: the trace is
over `Option Estep`-style items, where an admin-only step for hart `i` runs only `admStar`, which
is allowed to move the fabric.  Add its T1 lift beside `execWfPfRunProg` /
`xv6SrvwmoSafe` (new files).  `gfexecConfA` keys dev blocks by their position `(i, k)` (the
`.dv` nodes) and reuses `hemitf`.

**(L) T2-1c″.**  Generalize `gtraceLinearizationMin` to traces over events ∪ dev positions that
extend `po ∪ rf ∪ gmo'|W ∪ ioOrd|dv`.  The dev items are no-ops for the cand.  Existence: run
`normalizeOfAcyclic` on `L* := topo(racyD ∪ iopo ∪ dev)` restricted to `gmem`
(`topoLinearizes` applies to any `linExtD` order, as `Fab.topoLinearizesF` notes).  Every
`po`-run in a cycle then ends at a write (`gpow ⊆ racyD`) or at a dev node (`iopo`), so the cycle
maps into `L*` and is impossible.

**(K) The kill extended.**  The cycles to rule out are those of `racyD ∪ iopo ∪ dev`.  Dev edges
become a new cross-edge kind, and `iopo` becomes a new same-hart arm, which is still
po-increasing, so `rsameAcyclic` survives.  KillArms' chain composes in `tc (ioOrd GF)` instead
of `gmoLt`.  `gmo` sits inside it, and the dev and `iopo` arms come from (T).  This becomes a
`cycleKillA` over the fabric bundle, threaded through `hullRun`, W11 and W12, so W12's cat arms
are written once against `tc ioOrd`.

**(R) The re-thread** of the table above onto `gfexecConfA` (sibling `*A` files).  Walk segments
that contain no dev block reuse the constant-fabric lemmas through a `hemitf` dev-free reindex
(the twin of `hemitDevfreeReindex`).  Only segments that contain a dev block need new proofs.

**(W) Non-vacuity.**  `xv6ConfS` on `gfexecConfA`, plus an `LDev`-emitting witness:
`uartinitone`'s first `WriteReg`, which is the successor of the `_entry` witness.

## Sizes (estimates, unverified except for counts)

| piece | size |
|---|---|
| (T) + header text | S (done in the scratch: 60 lines) |
| (I) `execProgOkA` + T1 lift | L |
| (L) T2-1c″ (generalizes Lin2 §§3-7) | M–L |
| (K) kill arms + decomposition | M–L |
| (R) re-thread, 8.6k lines across 14 files | L–XL (the bulk) |
| (W) bundle + `LDev` witness | M–L |
| **W13 total** | **XL** (similar in size to the landed kill pipeline) |

## Risks

- **R1, platform.**  The kernel image contains only 4 `fence iorw,iorw` words, all in virtio
  (`Xv6/KernelImage.lean:17301-17451`).  The locks use `fence r,rw` and `fence rw,w`, which do not
  order I/O.  So (T)'s strong I/O ordering is a PLATFORM assumption (QEMU virt behaves this
  way).  It is not RVWMO-spec-guaranteed for xv6's UART and PLIC paths.  `LFence` has no i/o bits
  (`WeakAxiomatic.lean:90`), so a fence-discipline variant cannot even be stated at the graph
  tier.
- **R2.**  (I) changes the T1 interface, and every `execProgOk'` consumer gets a sibling.
- **R3.**  Unlocked cross-hart PLIC claim/complete and `plicinithart` are real fabric races.  (T)
  covers them, but the (K) arms for dev edges whose carriers sit outside any critical section
  need the strong-ordering arm alone.  That is fine under (T), but each such site is a trusted
  use of it.
- **R4.**  Dev nodes adjacent to fences or other non-`gmem` events need care in (L) and (K)
  (`gwf`: gmo contains only `gmem`, `WeakRvwmoGraph.lean:171`).

## Owner questions (all options)

- **Q-W13a, the form of the trusted item.**
  - (a) `ioObAcyclic` (recommended).
  - (b) [OWN.8]'s literal `po ∪ rf ∪ gmo|W ∪ dev` acyclic on the quantified graph.  This drops LB
    and W→W, contradicting [OWN.2], as `lbExcluded` shows.
  - (c) The same, stated only on the internally normalized graph.  It is not a statement about
    the input, so it cannot serve as a trusted base.
  - (d) `gdevAdj ⊆ gmo`.  It excludes SC executions (`scDevExcluded`).
- **Q-W13b, the platform assumption in R1.**
  - (a) Accept it as part of (T) and name QEMU virt / strongly-ordered I/O in the header.
  - (b) Require fence-guarded MMIO.  This needs i/o bits in `LFence` and an xv6 code change, which
    leaves the verified branch.
  - (c) Restrict the claim to platforms with PMA strong ordering.
- **Q-W13c, the realization interface.**
  - (a) Admin-only trace steps (`execProgOkA`, recommended).
  - (b) Make MMIO a tagged inert-fence row event, in the style of the Q7 sfence marker.  This
    changes `projLbl` and the emission proofs, which are merged files.
  - (c) Keep the folded model and prove representability for xv6 per MMIO site ("the carrier is
    hart-private", plus a `cycleKill` over dev cycles).  This is xv6-specific, fragile, and also XL.
- **Q-W13d.**  Retire `xv6RvwmoSafeModuloF` / `gfexecConsistent'` as a published form (keep it as
  an internal lemma on normalized graphs), or keep it with a header warning?
