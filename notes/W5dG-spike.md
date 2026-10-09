# W5d-G spike — fetches on the graph tier (plan rev 5 §C, §B(4)(iii)/(11), D18/D27; [OWN.3], [OWN.6])

*Stage-0 spike, 2026-10-09.  Read-only except the scratch file `Weak/GraphFetchSpike.lean`, which BUILDS
(`lean-gcp … lake build Weak.GraphFetchSpike`: no `sorry`; `#print axioms` = `propext, Quot.sound`).  Line
references are to this workspace.*

## 0. Verdict

**Keep the fetch an ADMINISTRATIVE emission item, and add a relational graph-tier Zifencei condition plus a
"fetch fragment" of ordering edges stored as graph data, the way `gdDeps` stores the store-dep fragment.**
Do not make it a graph event.

- Every `LIFetch` tag becomes a gmo write index, as a read's `ts` is (`0` = image).
- The condition `gzFetch` (§2) names no cut.  It implies a single-cut form (`fetchCutOk`, ∃ q with
  `itv ≤ q ≤ next-own-write`) on the normalized graph, and that form gives exactly the pf / W5d check at the
  realizing position (`fetchCutPrefix`, proved).
- Semantically this is the [R4.s1] "IF read event at a gmo position", with the position encoded as an
  existential cut.  Making the fetch a real event gives the same edges at much higher cost: a `Lbl`
  constructor matched exhaustively in ~38 files (Stage C measurement, `notes/weak-port-o2-stageC.md` §B),
  fetch events in `gxGmo`, new arms in `gwf`/`gloadValue`/Xchg/Topo/Lin, and a `linCand` trace label that
  the pf machine must then treat as a stutter.  So D27(a) is realizable in the admin form.

**Size.**
- W5d-G proper (G1–G5): **L**, about 1.8–2.2k lines.
- The `pstepPin` re-thread (G6) is shared with W11 (iii).
- The new kill-arm class (G7) goes in W11/W8: **L**.

The plan's "L–XL unverified" becomes **L, plus one XL risk**: hull closure (R1).

## 1. Evidence: where the pin lives and what consumes it

| fact | where |
|---|---|
| graph fetch oracle = image at ts 0 | `fetchPin` `Weak/WeakAxRealize.lean:160-167`; `pstepPin` `:184-187`; `fetchPinIfetchOk` `:168-178` (pf-admissible at ANY log, view 0) |
| emission clause | `emFetchImg` `Weak/WeakRvwmoSupply.lean:277`; in `gdexecQconf` `:281-289`; stable under renaming only because `wlblRen π (LIFetch b tvs) = LIFetch b tvs` (`Weak/WeakRvwmoConf.lean:147`, its deviation 3 / Q-C4) |
| fetch = admin item before row slot k | `hemit` `WeakRvwmoConf.lean:712-722` (`eadm ls ++ (l, some k) :: …`); `lbAdmin` `WeakAxRealize.lean:130-134` |
| pf checks fetches at view 0 only | `PFIFetch` `Weak/WeakPromiseBridge.lean:444-450`; `WPIFetch` `Weak/WeakPromise.lean:728-732` |
| the i-view lives in the Ev state | `elabOk (LIFetch)` = `ifetchOk … (σ.wgitv c)` `Weak/WeakEvInst.lean:564`; `eitvApply` `:612-615`; `itvPost` `Weak/WeakInterp.lean:363-364`; `itvPostMachCSL` `:378-384`; `amo_acq_fenceI` `Weak/WeakFence.lean:399-401` |
| TsoMem twin | fetch at `σ.itv cpu ≤ tvn ≤ σ.top`, one `tvn`, i-cache agent `MachCSL/Lang.lean:360-362`; `MState.fence` raises `itv` `:157-163`; no forwarding `MachCSL/TsoMem.lean:34-39` |
| **fence.i and the sfence.vma marker have the SAME label** | `ebarLabel .Barrier_RISCV_i = LFence false false false false` (`WeakEvInst.lean:272-275`, `ebarNow .Barrier_RISCV_i = none` `Weak/WeakEvLang.lean:745`); Q7 marker `annLabel` = `LFence false false false false` at an sfence announce (`WeakEvLang.lean:418-419`) |
| realization order | `linCand`: each event sits in the segment of its next own write `gnxw` (`Weak/WeakRvwmoLin.lean:440-453`), so the log prefix at slot (i,k) is exactly the writes with `gwix < gwix (gnxw (i,k))` |
| live normalization | `normalizeOfAcyclic` re-times by any linear extension of `racyD` (`Weak/WeakRvwmoTopo.lean:594-607`, `racyD` `Weak/WeakRvwmoAcyc.lean:196-201`).  Write indices are renamed **non-monotonically** (`tren`), so no max-based or cut-based condition transports.  Only conditions on rf, co and `racyD`-ordered pairs do. |
| hull induction | `cycleKill`/`t2linOfCycleKill` `Weak/WeakRvwmoLinInd.lean:155-237`; `hullOk` is rf-closed `Weak/WeakRvwmoHull.lean:557-560`; `gdHull` filters deps `:714-716` |

Measured sites:

| pattern | files | occurrences |
|---|---|---|
| `pstepPin` | 19 | 121 |
| `emFetchImg` | 10 | 41 |
| `gdexecQconf` | 18 | 124 |
| `tc (racyD` | 16 | 52 |
| `gdDeps` | 31 | 133 |
| `wlblRen` | 3 | 41 |

`racyD` is destructured directly at only 3 sites (`WeakRvwmoGlue.lean:205,209,223`, via `racyDSplit` / `racyDDecompose`).

## 2. The trusted-base item (exact Lean shape)

Proved in the scratch file: `fetchCutOk`, `fetchCutPrefix`, `fetchCutEdge`, `fetchRelOk`, `fetchRelCut`,
`fetchPinCutOk`.  Stated there but not yet proved about: `gzFetch`, `gzFetchCut`, `emZifencei`, `gfcut`,
`gwlog`.

```lean
-- graph's write log in gmo order (what linCand realizes)
def gwlog (G : Gexec) : List Wmsg := (gwrites G).filterMap (WeakRvwmoLin.gmsg G)
def gfcut (G : Gexec) (i k : Nat) : Nat :=            -- below the hart's next own write at/after slot k
  match gnxw G (i, k) with | some w => gwix G w - 1 | none => (gwrites G).length

/-- fence.i contributors at slot k (variant (b), §5 Q-G2): own writes po-before a fence.i site
before the slot, and rf-sources of the hart's reads po-before it. -/
def gzContrib (G : Gexec) (fi : Nat → Bool) (i k : Nat) (c : Geid) : Prop :=
  ∃ f, f < k ∧ fi f = true ∧
    ((c.1 = i ∧ c.2 < f ∧ gisW G c = true) ∨
     (∃ r a t v, r.1 = i ∧ r.2 < f ∧ greadsByte G r a t v ∧ gwriteAt G t = some c))

/-- THE TRUSTED-BASE ITEM, one fetch item (hart i, row slot k). -/
def gzFetch (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ j t v, tvs[j]? = some (t, v) →
    logByte G.gxImg (gwlog G) t (base + j) = some v ∧                                -- (Z1) value
    (∀ w n, gwriteAt G t = some w → gnxw G (i, k) = some n → gmoLt G w n) ∧           -- (Z2) not from the future
    (∀ w' v', gwritesByte G w' (base + j) v' → t < gwix G w' →                        -- (Z3) fresh past fence.i,
       (∀ c, C c → gmoLt G c w') ∧                                                    --      one cut per label
       (∀ l tl vl wl, tvs[l]? = some (tl, vl) → gwriteAt G tl = some wl → gmoLt G wl w'))

def emZifencei (G) (C : Nat → Geid → Prop) (i) (em : Hemission) : Prop :=   -- xv6ConfS's fetch clause
  ∀ n base tvs, em.emItems[n]? = some (.LIFetch base tvs, none) →
    gzFetch G (C (slot n)) i (slot n) base tvs     -- slot n := #row items among em.emItems.take n
```

Plain-language reading, with each conjunct's hardware justification:

- **(Z1)** Each fetched byte is its source write's byte, or the image's.
- **(Z2)** The source is gmo-before the hart's next store at or after the fetch.  Stores are not performed
  before earlier instructions are fetched.  The i-cache reads memory and does not forward from the store
  buffer.
- **(Z3)** Every write to a fetched byte that is co-after its source is gmo-after:
  - every write the hart had written or read before its last `fence.i`.  `fence.i` makes those visible
    before it invalidates the I$.
  - every other byte's source.  A parcel is filled from one line at one instant.  The Sail model fetches
    4-byte words when the pc is 4-aligned and 2-byte parcels otherwise
    (`WeakRvwmoConfWit2.lean:44`, Q22).

There is no reference model, because riscv.cat has no fetches.  The item must be NAMED in §B(11) with three
hardware readings:
- (H1) a no-forwarding I$ with one fill instant per label;
- (H2) `fence.i` completes the hart's earlier stores and reads before later fetches;
- (H3) stores are non-speculative relative to fetch.

(H2) for own stores is the "drain" reading that TsoMem already builds in (`itv ≥ ownPub`), which goes
beyond the spec text.

**The fence.i sites `fi`** come from the emission, not the graph, because the two all-false fences share a
label.
- `emFenceI em f`: the row item at `f` is `(LFence false false false false, some f)`, AND the latest
  `LInstr`/`LIFetch` in the admin block before it is `LInstr`.
  - fence.i: boundary `LInstr`, fetch, announce `LInstr`, barrier.
  - sfence.vma: boundary `LInstr`, fetch, marker.
  - (`WeakEvInst.lean:283-287,369-370`; `WeakEvLang.lean:418`.)
- Soundness lemma `emFenceISound` over `hemit`/`pstepEv`: M.

**Kernel-text instance.**
- With tag 0, image bytes and no write to the bytes, (Z1)–(Z3) hold vacuously (no `w'`, no source event).
- `fetchPinCutOk` proves the cut form.
- So `candKfetch` + W3's history fact discharge `gzFetch` for every kernel fetch.
- **Kernel-only executions get an empty fetch fragment: no new edges, no new kill arms.**

## 3. How it is consumed (the W5d-G proof route)

1. **Edges.**
   - From `gzFetch` on `GD` read off the fetch fragment `F`:
     - E1: src → nxw;
     - E2: c → w';
     - E3: src_l → w'_j.
   - Every edge is `gmoLt` on `GD` by (Z2)/(Z3), so adding `F` to `racyD` adds only gmo-respected edges, as
     with deps.
   - Store `F` as data: `Gdexec.gdFetch`, or a `racyD` parameter (Q-G3).
   - xv6ConfS requires `F_em ⊆ GD.gdFetch` (mirrors `rowDeps ⊆ gdDeps`, `WeakRvwmoSupply.lean:289`).
   - `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188-191`) stays untouched: the fetch fragment is NOT part
     of riscv.cat.
2. **Retime.**
   - `L ⊇ racyD ∪ F` together with `grule14 GD'` gives `fetchRelOk` at `GD'`, with `cs` = the contributors'
     new indices.
   - The contributor SET is retime-invariant, because it is defined by rf and po.
   - Its bound `≤ gfcut` is DERIVED from gpow / rf;gpow, not assumed.
   - Then `fetchRelCut` (proved) gives `gzFetchCut`.
3. **Realize.**
   - The fetch at slot k is replayed just before (i,k)'s step, where the log is `gwlog.take (gfcut)` (new
     rank lemma `linPrefixLog`).
   - The pf/Ev itv there is `≤ lmax cs` (floor bound over the realized `ews`; `WeakRvwmoFloor` style).
   - `fetchCutPrefix` (proved) gives `ifetchOk img prefix itv` AND a single view q.  That q is the
     `candSca`-for-fetches that W5d/W4 need: TsoMem reads at `tvn := q`.
4. **W5d interface (fix now).**
   - W5d's M2 fetch clause should be the cut form `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log q base tvs`,
     not per-byte `ifetchOk … itv`.
   - The per-byte form tears (§B(9) [R3.4]), and the cut form is what W5d-G produces.

## 4. Change list and sizes

| item | files : sites | size |
|---|---|---|
| G1 statement: `gzContrib`, `emFenceI` + `emFenceISound`, `emZifencei` in xv6ConfS / `gdexecQconf` (replacing `emFetchImg`) | `WeakRvwmoSupply.lean:277-352` (+ `emFetchImgRen/Prefix` → retime/hull versions), `WeakRvwmoFab.lean:516-522` (`Gfexec` conf), `WeakEvInst`/`WeakEvLang` (lemma only) | M (~350) |
| G2 tags = gmo indices: `wlblRen` renames `LIFetch` tags (reverts Q-C4); `pstepEvWren`/`projLblWren` LIFetch arms (`pstepEv`'s i-cache arm is ts-free, `WeakEvInst.lean:304-312`); `emLabelsRen`; M1 pin kept via `π 0 = 0` | `WeakRvwmoConf.lean:57-66,147`, Supply | S (~100) |
| G3 fetch fragment as data: `gdFetch`; `racyD` disjunct; `racyDSplit` arm (cross-hart, `gcross`); `gdHull` filter; `retime` keeps it; Gdexec literals | `WeakRvwmoGraph.lean:613`, `WeakRvwmoAcyc.lean:200`, `WeakRvwmoGlue.lean:205-223`, `WeakRvwmoHull.lean:714`, `WeakRvwmoTopo.lean:120-129,594-607`, ~31 literal sites | M (~300, partly mechanical) |
| G4 `retimeZifencei` (§3.2) + contributor invariance + gwlog/gwix bridge | Topo (new section) | L (~600) |
| G5 `linPrefixLog`, floor bound, `supplyOfQconf` producing the M2 fetch clause | `WeakRvwmoLin.lean`, `WeakRvwmoFloor.lean`, `WeakRvwmoSupply.lean:743-883` | M–L (~500) |
| G6 re-thread `pstepPin` → `execProgOk'S` (stars as label-carrying `admRun`s with the cut clause) | AxRealize 26, Supply 14, Cert 9, Cert2 8, Fab 7, Cert3 7, SrvwmoCapstone 6, CycWit 6, Cert4 6, AxAdequacy 6, Cert3b 5, LinInd 4, Lin2 4, FabInd 4, Capstone 3, Glue 2, ConfWit2 2, Glue2 1, AxRunGV 1 (`RunData.rdProg` `Glue.lean:279`, `cstOk` `Cert4.lean:372`, `t2linSupply` `LinInd.lean:240-250`, `topoSupply` `Supply.lean:865`) | **shared with W11 (iii)**, one pass |
| G7 kill arms for cycles through E1/E2/E3 ("fetch-entry segments") | `cycleKill` consumers; W8 vocabulary (user-text page ownership; exec/fork → p->lock → userret `fence.i`) | L, in W11/W8 |

The witness files with literal fetch items (`WeakRvwmoConfWit2` `ldEmFetchImg`/`evEmFetchImg`,
`WeakRvwmoAdm`) need only a re-proof: the pin implies `gzFetch`.

## 5. Risks and owner questions

- **R1 (the XL risk): hull closure.**
  - `hullOk` is rf-closed but knows nothing of fetch sources.
  - A kept fetch at slot k whose next own write was cut away can lose its source, and then
    `hullRealizableOfAcyclic` cannot realize it.
  - Options:
    - (a) also anchor sources to every po-later memory access (E1′: src gmo-before every memory event at
      or after the slot).  This is a stronger (H3) ("an instruction's accesses follow the fetches of all
      po-earlier instructions"), but it is still gmo-true.  `hullOk` then gains "kept fetch item ⇒ source
      kept", which follows from racyD-closure.
    - (b) keep E1, and let hulls cut each hart only directly after a memory event.  This needs t2linAux's
      cut selection re-checked.
  - Recommend (a).  Budget M if the cut selection is racyD-driven, XL if t2linAux must be re-proved.
- **R2: non-vacuity.**
  - The D18 user-fetch witness is still open and is now W5d-G's gate too.
  - R5's disk-row vacuity (W13) comes first: without it `exec("/init")` never completes.
- **Q-G1 (fence.i identification).**
  - (a) Recommended: the emission-structural `emFenceI` + soundness lemma (M).
  - (b) Give fence.i or the Q7 marker distinct fence bits.  `(f,f,f,t)` changes only `wRes`, but it
    perturbs Q7 and the AxSL pins.
  - (c) A new `Wlabel`.  XL.
- **Q-G2 (contributor set).**
  - (a) Recommended: the superset "everything the hart wrote or read before fence.i".  It is simple to
    audit and retime-invariant, but its trusted reading is stronger: (H2) covers plain loads.
  - (b) The exact `itvPost` set (aq reads, `pr∧sr`-fenced reads, address views, own stores).  It is
    spec-minimal and equal to TsoMem's, but needs a symbolic view fold: +M.
- **Q-G3 (where F lives).**
  - (a) Recommended: a `Gdexec.gdFetch` field, mirroring `gdDeps`, so hull, retime and acyclicity carry it
    for free.
  - (b) A parameter of `racyD` / `cycleKill`.  The ~31 constructor sites are untouched, but 16 files'
    statements change.
- **Q-G4 (pinned milestones).**
  - Keep `pstepPin`/`fetchPin` as the M1 kernel-text instance (`fetchPinCutOk`), or delete them after G6?
  - Recommend: keep until M2 lands.
