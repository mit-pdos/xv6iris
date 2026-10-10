# W2 spike — `Weak/TsoOfPf.lean`: promise-free runs into TsoMem (risk report)

Plan: `notes/weak-allocproc-plan.md` §C Stage 0 "W2" (rev 11). Inputs: W5b (`Weak/PfRunShape.lean`, merged:
`pfRunS`, `pairAdjacent`, `scaOk`/`candSca`, `candKfetch`); W3's `textPristine` taken as a HYPOTHESIS with the
plan's definition. Lean spike: `Weak/TsoOfPf.lean` (239 lines incl. a 27-line header; green; axioms
`propext`/`Classical.choice`/`Quot.sound`; no sorry/axiom/native_decide).

## Verdict: D7 STOP

Under the plan's position-preserving log identification, shaped pf runs (`pfRunS` + `pairAdjacent` + every
plain load `scaOk`) have WeakMem steps with no TsoMem step that reads the same bytes. Three separate gaps:

| | gap | what it is | Lean | level |
|---|---|---|---|---|
| **G1** | the `.aq` "off-by-one" | after `amoswap.aq` (read of lock-word timestamp `t`, write at `top+1`), TsoMem's floor is `top+1` (`MachCSL/Lang.lean:151`); WeakMem's `wVrNew` is only `max(wVrNew, t)` (`exloadPostRunD`, `loadPostAt` aq arm). A later plain load of a byte written in `(t, top]` reads stale in WeakMem; TsoMem cannot. Not an off-by-one: it is off by `top − t`. | `TsoOfPf.g1Run`, `g1Shape`, `g1Tso`, `tsoAqPairTv` | lockstep only (another TsoMem schedule exists) |
| **G2** | mixed-size coherence floors | TsoMem stamps EVERY footprint byte's `coh` with the load's view `tvn` (`HRead.afterLoad`, `MachCSL/TsoMem.lean:268`); WeakMem stamps each byte with its own source (`loadPostAt`). Two overlapping loads with different footprints, reading the shared byte from the same write, split the two models. | `TsoOfPf.g2Run`, `g2Shape`, `g2Tso`, `tsoAfterLoadCoh` | **outcome**: TsoMem is stronger than RVWMO/riscv.cat here |
| **G3** | DMA reads | TsoMem's DMA read is at the TOP (`dmaView`, `MachCSL/Lang.lean:185`); the disk row's `DRead` is `LLoad aq false` (`WeakEvInst.lean` `pdiskProg`) at the disk agent's own floor. `virtioProg` (`Weak/VirtioProg.lean:606`) reads the avail ring and the descriptors with no fence after START, so a stale read is pf-legal. | prose (same mechanism as a stale hart load) | **outcome** at the graph tier too, see below |

G1 is in the xv6 kernel itself. The image's `acquire` is `amoswap.w.aq; sext.w; bnez; jal mycpu; sd a0,16(s1); ld ...`
(`Xv6/KernelImage.lean:2265-2290`). There is NO fence after the swap, so the whole critical section runs in G1's
window. `release` is `fence rw,w; sw zero` (`:2361`), and that fence does not raise `wVrNew`. The window
therefore lasts until the next `fence rw,rw` or aq pair, i.e. also past the release.

### The witnesses (proved; the most permissive program `anyStep`, because W2's lemma is per-label for any `pstep`)

* **G1** (`g1St`): B `sw x=1` (ts 1). A `LExLoad aq y` reads ts 0, `LExStore y` (ts 2), then `LLoad x` returns
  the IMAGE byte 0. `g1Run` builds the `pfRunS` (every step a `wpPfStep`; the load's `scaOk` holds at view 0).
  `g1Shape` proves `pairAdjacent`. `tsoAqPairTv` shows that TsoMem's floor after any aq pair is `top+1` (= 2 here).
  `g1Tso` shows TsoMem then reads `x = 1` at every view ≥ 2.
  The candidate is sRVWMO-consistent by inspection. `acqPo` gives `rmw →ppo ld`. `axOrd` needs only
  `pub(rmw read) = 0 < ts(x:=1) = 1`. No `ob` edge returns from B's store to A. It is also RVWMO-consistent:
  put gmo = AMO, `ld x`, `x:=1`.
* **G2** (`g2St`): B `c:=1` (ts 1), then `a:=1` (ts 2). A `lh (a,b)` reads `(1,0)` (SCA at view 2), then
  `lh (b,c)` reads `(0,0)` (SCA at view 0). `g2Tso` shows that under `R` the first load runs at a view ≥ 2,
  `tsoAfterLoadCoh` stamps `coh b ≥ 2`, and so TsoMem's second load reads `c = 1`.
  riscv.cat agrees with WeakMem: `gppo2` (`Weak/AxGraphCat.lean:151`) needs DIFFERENT sources for a common byte,
  and here `b` comes from the same write in both loads. So gmo = `lh(b,c)`, `c:=1`, `a:=1`, `lh(a,b)` is
  consistent. No TsoMem schedule gives the outcome: B's stores are ordered, and A's loads run in program order.

## Per-label (↓) table

Question per row: does a `wpPfStep` from an `R`-related state, under `pairAdjacent` + the `execProgOk'S` shape +
`candSca`, map to a TsoMem step with the same bytes, landing in a related state?
"(★)" is the side condition defined in §R below.

| label (source) | pf step | TsoMem match | (↓) |
|---|---|---|---|
| `LSilent` (regRead, choose, retry self-loop of a lost SC) | `PFSilent` | 0 TsoMem steps (stutter). The retry arm keeps the same monad node, so the program relation is unchanged. | ✓ (W4 must allow 0-step matches) |
| `LInstr` / `LRegW` / `LCtrl` | `instrPost` / `regwPost` / `ctrlPost` (dependency views only) | cycle boundary / regWrite (registers are W4's) | ✓. None occurs mid-pair (`lbAdmin false` excludes `LInstr`; `LRegW`/`LCtrl` leave `wRes` alone) |
| `LIFetch`, M1 | `PFIFetch`, `ifetchOk … 0` + `candKfetch` | ifetch agent at `tvn := itv` | ✓ given `textPristine` + R-hist. Pristine bytes are written by no log message, so `t = 0` and `v = img a`, which TsoMem reads at every view (`Wp.lean:1478,1490`). |
| `LIFetch`, M2 (cut) | `∃ q ≤ |log|, ifetchOk img log q` | ifetch agent at `tvn := q` | **conditional**: (i) `R` needs `itv_T ≤ q` (pf has no `itv`; W5d must supply it). (ii) NEW: `ifetchByteOk … q` admits `t > q` (empty window `(t, max t q]`), and TsoMem at `q` cannot read that. Either the cut form adds `t ≤ q` per byte, or a torn fetch slips through. |
| `LLoad` (hart, plain) | `PFLoad`, `readOkD` per byte + `scaOk` | plain read at `tvn := max(tvn_sca, F_T)` | ✓ **iff (★)**. Fails exactly at G1 (`F_T` = aq debt), G1′ (`rv := top` after an exclusive, then `fence r,_`) and G2 (coh stamps). Tearing is closed by `candSca`. |
| `LLoad` (disk `DRead`) | as above, disk floor | `dmaRead`: top bytes | **G3 ✗** unless the read is latest (`lat = true`) or (★) holds with `F = top` |
| `LStore` (hart) | `PFStore`, append | `MState.store`, `excl = false` | ✓. Same position, author and bytes. `¬ othersReserve` holds because only a mid-pair hart reserves, and `pairAdjacent` puts no foreign step mid-pair. |
| `LStore` (disk `DWrite`) | append by agent `NCPU` | `storeDma` (disk agent), `¬ anyReserve` | ✓ (same argument) |
| `LFence pr pw sr sw` (`ebarNow b`) | `fencePost` | `MState.fence b` | ✓ for the floors (`TsoOfPf.fenceRow`, all 10 non-`fence.i` kinds, given `tv ≤ wVrNew`, `rv ≤ wVrOld`, `ownPub ≤ wVwOld`). |
| `LFence` false×4 (`fence.i`, sfence marker) | identity | `fence.i` raises `itv` | ✓ in the memory fields; `itv` feeds only the fetch row |
| parked `fence rw,w` (`fence.tso`'s park) | `wVwNew`, `wRelp`, `wRes := none` | none (stutter) | ✓. Pf stores have no view check (`PFStore`). `wRelp`/`wPub` are inert. Not `lbAdmin`, so never mid-pair. **Suspect closed.** |
| `LExLoad aq` | `PFExLoad`, `readOk` at the plain floor, `wRes := some` | excl read, top bytes, resv, `tv := top` if aq | bytes ✓: `exclOkTs` at the ExStore + `pairAdjacent` (no foreign step) + `coh ≥` own writes make `t` the latest, i.e. TsoMem's `topBytes`. `¬ othersReserve` ✓. **Views ✗ (G1/G1′).** |
| `LExStore` | `PFExStore`, append, `wRes := none` | `store … true`, `tv := top+1` if `acq`, resv cleared | ✓ (bytes, position) |
| `LDev` (hart MMIO) | `PFDev`, `devRead`/`devWrite` on `efDev` | the MMIO arm, the same `devRead`/`devWrite` on `σ.devs` | ✓ given R-dev |
| `LDev` (disk START/COMMIT, UART/PLIC moves, PLIC pin) | `PFDev` at the disk row | device-thread steps (`devStep`, `devrt`) | structural (D51 one-row model vs threads): W4/W13, not memory |
| `LRmw` | `PFRmw` | none (TsoMem has no one-step RMW) | N/A: `pstepEv` never emits it |

Suspect outcomes: *fence-clears-reservation* is vacuous on shaped runs (no fence or `LInstr` between the halves;
outside a pair TsoMem's `resv = none`). *Tearing* is closed by `candSca`. *Parked release fence* is closed.
*`.aq` off-by-one* is REFUTED as sized: it is G1.

## `R` (with the `.aq` correction)

* **R-log / position / author**: `σ.log.length = |c.pcLog|` and `σ.log[k] = (c.pcLog[k]).wmTid` as an agent.
  Hart `i` is `hartAgent i`, the disk row `NCPU = diskAgent`; i-fetch agents author nothing.
* **R-hist (per-byte history)**: for RAM `pa`, `σ.mem[pa]? = histOf img log (paZ pa)` (`TsoOfPf.histOf`: entry
  timestamp = log position + 1, author = `wmTid`, image entry `⟨0,0,v⟩`, cf. `imgFlat`). Class `wmAk` has no
  TsoMem image: W8/W11's `protReg`/`badSeg` read it on the pf log only.
* **R-img**: `c.pcImg = imgZ` with the RAM filter of `imgFlat`.
* **R-view (per hart)**: `ownPub_T = wVwOld` (equality). `rv_T ≤ max wVrOld X` with `X` = top at the hart's last
  exclusive read. `tv_T ≤ max wVrNew A` with `A` = write timestamp of the hart's last aq pair. `coh_T a ≤ rv_T`.
  `X`/`A` are the G1/G1′ *debt*. The plan's `tv ↔ max wVrNew (own last store)` is wrong: WeakMem loads ignore
  the own last store for other bytes.
* **R-resv / acq**: `resv_T c = none` unless `c` is mid-pair, in which case the snapshot is the read's bytes and
  `hr.acq` is the read's `aq`.
* **R-itv**: unconstrained at M1 (pristine text); at M2, `itv_T ≤ q` for every later cut (from W5d).
* **(★) for a plain load of hart `i`**: no write by another agent to byte `base+j` in `(t_j, F_T]`, where
  `F_T = max(tv_T, coh_T over the footprint)`. For a DMA read, `F_T = top`. With (★), `tvn := max(tvn_sca, F_T)`
  is a legal TsoMem view reading exactly `t_j`. Own later writes are excluded by `coh_W ≥` own write timestamps,
  later foreign writes up to `tvn_sca` by `scaOk`, and those up to `F_T` by (★). Without debt, (★) follows from
  `readable` + `scaOk`.

## Log identification (W8/W11 vocabulary)

A pf log message `k` is a TsoMem store at timestamp `k+1` with the same author, footprint and bytes. Each byte's
history is the projection (R-hist). Classes stay on the pf/graph side. Under this identity map the TsoMem floor
facts become **log-level facts about one load**: (★) says "no foreign write to the bytes I read between my source
and my floor". That is the export shape W8's design gate needs. For a lock-protected, own, or pristine byte, (★)
holds by discipline (the lock's protected bytes are not written between the release store `t` and the acquirer's
pair). For a racy byte (W8 (ii)/(iii): `PCall`/`PResidue`, e.g. `panicked`) it does not hold in general.

## Options (spec-first)

| gap | option | w.r.t. RVWMO |
|---|---|---|
| G1 | **(e) gmo-ordered log** (recommended): require the candidate's log order on writes to extend ob/gmo, and strengthen `candSca` to *SCA at a view ≥ the TsoMem floor* (`candScaT`). At Stage 2 it follows from `gloadValue` when W11's linearization lists writes in gmo order: AMO.aq `<gmo` the later load, so the load's gmo view is ≥ the AMO's position. At M1 it is a new premise. Touches W5b, W11 (iii). | faithful |
| G1 | (a) D7 (Rec): the weak exclusive read takes TsoMem's view (`wVrNew := |log|`) | stronger; breaks T1 realizability for G1 candidates |
| G1 | (b) MachCSL: aq floor := the read bytes' source timestamps | faithful direction (weaker TsoMem); re-opens `WpLock`'s view receipt and its clients; owner-gated, serial |
| G1 | (c) (★) from W8 discipline, per load | faithful; fails at racy sites |
| G2 | (a) MachCSL: `afterLoad` stamps `coh a` per byte (its source), not `tvn` | faithful direction; re-opens `cohOk` users; owner-gated |
| G2 | (b) W8 export: no overlapping different-footprint loads of concurrently written bytes | faithful (program fact); sites unknown |
| G2 | (c) strengthen `candSca` | NOT derivable: cat allows G2 (`gppo2`) |
| G3 | (a) disk `DRead` with `lat = true` + graph twin: W13 `ioResidue` gains (R2′) "an I/O event po-before a DISK-row RAM read ⊆ gmo" | stronger than (a′), device-model text (D51), realization-necessary; without it the graph allows stale descriptor reads after START, which the TsoMem side never realizes |
| G3 | (b) MachCSL: DMA reads at a disk view | weaker; re-opens the virtio driver proofs (XL) |

Recommendation: G1 (e). G2: decide between (a) and (b) once W8 counts the sites. G3 (a), folded into W13 (R).
Each fix keeps the plan's shape. G2 and G3 are new TsoMem strengthenings over RVWMO that are missing from §0 F1's
list (i)–(ii). G2 is a mixed-size (N10-adjacent) issue, but it is a REALIZABILITY gap, not a fidelity gap: a
G2-shaped xv6 graph has no realizing MachCSL run.

## Not claimed / open

(↑) is not claimed. W14's SC run is unaffected: at SC every load reads at the top, so G1–G3 do not arise there.
The positive rows are argued, not proved; only `fenceRow` is in Lean. A full `pfLoadRow` under (★) needs
FlatMem ↔ `histOf` lemmas (L).
