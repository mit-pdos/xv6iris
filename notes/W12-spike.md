# W12-spike: the kill arms over riscv.cat (D25 route (a))

Stage-0 spike, 2026-10-09.  Plan rev 5 §C "W12-spike", §B(9), D25; owner ruling [OWN.5] = route (a).
Scratch file: `Weak/CatOfMinusSpike.lean` (399 lines, BUILDS on the VM, no `sorry`; Lean-only, not part of the
chain).  No merged file was edited.

## Verdict

**Route (a) is sound for the KILL, and its size is L at the low end (~1.2–1.8k lines, M–L).**  Both of the plan's
gates close by changing hypotheses only, and the scratch file proves this.  The spike also found **two things the
plan does not cover**:

- **(F1) The published quantifier `rvwmoCatConsistent` is not riscv.cat.**  It is STRONGER than riscv.cat.  Its
  rule 12 (`gppo12`) ranges over the untagged `gdDeps`, so it also orders `ctrl;[W];rfi;[R]`.  The tree already
  proves this and calls it "UNSOUND for safety": `Weak/AxDeps.lean:12-18` and `twNotCatForget` (`:883`) together
  with `twCatT` (`:876`).  The plan's statement (`weak-allocproc-plan.md:103`) has to quantify over the TAGGED
  model `rvwmoCatConsistentT GT` (`AxDeps.lean:208`).  The chain then runs on `forget GT`.
- **(F2) There is a third gate, the certification walk's floor kit (W10's toolkit).**  Its invariant does not
  hold under cat, so changing the hypothesis is not enough here: the invariant has to be redesigned.  See
  "Gate 3" below.

## Where RVWMO⁻ is consumed (grep over the capstone/Walk3 import closure)

There are 26 files in the closure with `rvwmoMinus*`/`gppoGmo` uses.  Classified by what they actually project out
of the hypothesis:

| Consumer | Projections used | Under cat |
|---|---|---|
| `normalizeOfAcyclic`/`topoExists`/`topoLinearizes` (`Topo.lean:188-193,585,594`), `racyDMem` (`:558`) | `gwf`, `gloadValue`, `gatomicity`, `gdepsWf`. Never ppo. `linGppo` (`:319`) gets the OUTPUT's ppo from `racyD` | **survives as is**. Generalise the section hypothesis to a core |
| `topoSupply` (`Supply.lean:866`), `hullRealizableOfAcyclic` (`LinInd.lean:162`), `hullRealizableRowsG` (`Cert4.lean:153`), `hullRun` (`Glue.lean:272`), `topoLinearizesF`/FabInd `:433` | pass the hypothesis to Topo, plus `hullDepsConsistent` | survives (core), apart from the hull lemma |
| `rule14Linearization`, `WeakRvwmoLin` (47 `hppo`), `Lin2`, `Norm`, `PreNorm*`, `Xchg` | run on the NORMALISED `GD'`, which is RVWMO⁻ + rule 14 by construction | **untouched** |
| `racyDSplit` (`Glue.lean:103-110`), `gcrossGmo` → `grfGmo` (`KillArms.lean:270-275`, `Acyc.lean:218-233`) | `gpoloc` W→R (forwarding) | **needs the rfi case** (gate 1) |
| `certGmo`/`chainGmo`/`cycleKillArms` (`KillArms.lean:298-332`), `cycleHasEvent` (`Glue2.lean:141`) | only through `gcrossGmo` | survives once `gcross` is rfe ∪ co ∪ fr. Then needs only `gwf` + load value |
| `segPinGmo` (`Glue.lean:233-240`) | rules 4, 5, deps | survives as is. Generalise it (see design) |
| lock kit: `acqSrc` (atomicity), `acqTsLt` (`Lock.lean:200`, W→W = rule 1), `acqSrcRel` (lv), `acqFoldFree`, `csChained` (`KillArms.lean:499`: `acqGmoAfter` rule 5, `fenceGmoAfter` rule 4, cross edge into the entry is cross-hart, so rfe) | rules 1, 4, 5 | **survives**. Re-proved verbatim in the scratch |
| `lockPoGwix` (`Lock.lean:235`, rule 1), `csKill`/`winExcl*` | rule 1, 4, 5. Not on the kill path (LockWit/ProbeSwap only) | survives |
| `hullConsistent`/`hullDepsConsistent` (`Hull.lean:579,724`) | ppo⁻ part via `gxhGppo` (`:447`) | **needs a cat twin** (6 arms + rule 12 through `hren`) |
| `cyBackwardNotAq` (`Cert4.lean:588`) | rule 5 | survives |
| non-vacuity witnesses (`lkw`/`lkw2` `KillArms.lean:798,1166`, `mpwd`, `mpgd`, `ergd`, `lbgd`) | proofs of RVWMO⁻ | **no re-proof needed**: `catADOfMinus` (∘ `minusImpliesCat`). This corrects [R5.s1] |
| **Floor/Cert3 kit**: `finv`/`gvisUb` (`Floor.lean:100,624`), `finvStep` (`:605`), `greadSrcUb` (`:442`), `cinvReplay`/`floorOfCgraph`/`certFloorOk`/`cpolRead` (`Cert3.lean:311,393,430,470`), consumed by `wblkPolAt` (`Walk.lean:700-731`) | `gpolocGmo` (W→R, R→R), `grelacqGmo` (rule 7 RCpc) | **BREAKS** (gate 3) |
| residual premises `l2ClaimAt`, `cutSupply`, `certSupply`, `walkSupply`, `walkPolicy` (`Glue.lean:440,481,487`, `Glue2.lean:453`, `Walk3.lean:86`) | take the hypothesis as an ANTECEDENT | re-hypothesised. Their discharges (W8–W11) must now handle forwarding graphs |

None of the dropped ppo rules (W→R po-loc, R→R same-source, `grelAcq` RCpc) is used on the kill path.  Lock is used
at rules 1/4/5 (`:120,125,200,235`), KillArms at `:537,586`, and the Hull uses are the ppo-preservation proof.

## Gate 1 (rfi) and gate 2 (lock kit): closed in `Weak/CatOfMinusSpike.lean`

- `rvwmoCatAD GD ad` (§0) is the chain's hypothesis: cat's six arms, lv, atomicity, `gdepsWf`/`gdepsGmo`, and
  rule 12 over a sublist `ad ⊆ gdDeps`.  It has three entry points:
  - `catADOfCatT`: TAGGED, on `forget GT` with `ad := gtAd`.
  - `catADOfCat`: the untagged model.
  - `catADOfMinus`: RVWMO⁻.
- `grfiLex`: under cat, same-hart rf is po-forward, using rule 1 alone.
- `racyDSplitC`: rfi goes to `rsameC`, and the cross arms become `gcrossE` = rfe ∪ co ∪ fr.
- `rsameCAcyclic` holds.
- `gcrossEGmo` needs only `gwf` + lv (`grfeGmo`, `gcoGmo`, `gfrGmoLv`).
- `segPinC`: a same-hart CHAIN of `pinStep`s (the six cat arms ∪ deps ∪ rule 12 over `ad`), with `segPinCGmo` and
  `pinStepOfSegPinArm` (today's arms embed).
- `segPinCForward` is the new case. A dep-pinned entry whose store is forwarded inside the segment is closed by
  rule 12.  This is why `ad` must be the TAGGED addr/data edges.
- `CertC`/`chainC`/`cycleKillArmsC`: the kill needs only `gwf` + lv.
- `acqSrcC`/`acqTsLtC`/`acqSrcRelC`/`acqFoldFreeC`/`csChainedC`: the lock kit over cat.

## Gate 3: the walk floor (NOT in W12 as planned; it lands on W10)

`gvisUb G r n` means "every write of index ≤ n is gmo-before r".  `finv` asserts it for `coh ws a`.  Under cat, an
own store `w` to byte `a`, forwarded to the po-later read `r`, can be gmo-AFTER `r`.  So `gvisUb G r (gwix w)` is
false, and `finvStep`'s coh hook (`Floor.lean:619`, `gpolocGmo`) and `greadSrcUb`'s po case (`:453`) cannot be
re-proved.

The FLOOR itself still holds: `t = gwix w`, and co-maximality covers the po-visible writes.  But it needs a
per-byte coherence invariant (the SC-per-location argument through rules 1/2) in place of `gvisUb`.

Two smaller mismatches:

- **wVRel hook.** It uses `grelAcq` (rule 7 RCpc), which this cat model lacks (`grcsc` needs both bits,
  `AxGraphCat.lean:163`).
- **Forwarded acquire loads.** WeakMem's forwarded ACQUIRE load raises `vrNew` to the store's index
  (`fwdView ws true a t = t`, `WeakMem.lean:585-613`).  So for a forwarded plain `LLoad aq` the machine is
  stricter than cat.

Both are vacuous for the kernel's rows: release is `fence rw,w; sw` (`Xv6/ProofRelease.lean:83-86`), and acquire
is the RMW `amoswap.w.aq`.  They are open for user rows under [OWN.3].

Size: a rework of Floor §4–§6 and Cert3 §2–§3, about 0.5–1k lines (M–L).

## Recommended design for W12 (`Weak/CatLin*.lean`)

1. **Core predicate.** Add `rvwmoCoreD GD := gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf`.  Restate `topoLinearizes`'
   section variable, `topoExists`, `racyDMem`, `normalizeOfAcyclic(')`, `topoSupply`, `hullRealizable*`, `hullRun`,
   `topoLinearizesF` over it.  These are statement edits only (S).
2. **Kill definitions.** Copy the scratch's §0–§3 into the new files, plus the Glue §1 decomposition re-instantiated
   at `rsameC`/`gcrossE`: `rawChainC`, `crunC`, `cycleSegmentsC` (S–M).
3. **Hull lemma.** `hullCatAD`: the hull of a `rvwmoCatAD GD ad` graph is `rvwmoCatAD (gdHull GD cs)
   (ad.filter cut)`.  It needs a `rowsRelGppoCat6` (rule 2's `t1 ≠ t2` and rule 3/12's `grfAt` through the
   injective `hren`) (M, the one real proof).
4. **Restated chain.** `cycleKillC`, `t2linAuxC`, `t2linOfCycleKillC`, `t2linSupplyC`, quantifying
   `∀ GD ad, rvwmoCatAD GD ad → …`.  Then `l2ClaimAtC` (`segPinC ∨ csHyps[gcrossE] ∨ Bad`), `rawChainChainC`,
   `cutSupplyC`/`certSupplyC`/`walkSupplyC`/`walkPolicyC`, `cycleKillOfL2C`, `t2linOfL2'''C` (S–M).
5. **Published capstone.** `xv6RvwmoSafeModuloT`:
   ```
   ∀ GT : GdexecT, rvwmoCatConsistentT GT →
     gdexecQconfT boot d0 im nh GT →            -- rowDepsT edges ∈ GT.gtDeps (tags); ⇒ gdexecQconf (forget GT)
     (∀ x, ¬ tc (racyD (forget GT)) x x) ∧ …    -- conclusions unchanged
   ```
   The proof is `catADOfCatT GT h` fed to the C-chain.  `gdexecQconfT → gdexecQconf (forget GT)` comes from
   `rowDepsSubT` (`AxDeps.lean:690`) (S–M).
6. **Non-vacuity.** Reuse the existing witnesses via `catADOfMinus`.  Add ONE forwarding witness that is
   cat-consistent but not RVWMO⁻ (e.g. SB+rfi-pos; `AxGraphCat`'s `epc`/`isw` are candidates) through `rvwmoCatAD`
   (S).

`WeakRvwmoLin*`/`Norm`/`PreNorm` are untouched.

Knock-ons:

- **W9a.** The pin bridge targets `segPinC`.  One-step pins lift by `pinStepOfSegPinArm`.  Segments merged
  across an rfi need a rule-12 chain (`segPinCForward`) when the entry pin is PDep (M on W9a).
- **W8–W11.** They now discharge premises over cat graphs.  TsoMem forwards, so W8's exports should carry over.

## Risks

- `hullCatAD`'s rule-2 clause depends on `hren` being injective on the cut's sources.  It is believed true
  (`hrenWix`) but not yet built.
- Gate 3 is a redesign, not a re-proof.  Unless it is scheduled, W10 is L, not M–L.
- The tagged conformance (`gdexecQconfT`) is new trusted-surface text, so it needs review against `rowDepsT`'s
  correction (5) (`AxDeps.lean:56-60`).

## Owner questions

1. **The published model (F1).**
   - (a) Recommended: tagged `rvwmoCatConsistentT`, chain on `forget GT`.
   - (b) Untagged `rvwmoCatConsistent`, with "rule 12 also over ctrl/translation deps" NAMED as a strengthening of
     riscv.cat.
   - (c) Drop rule 12 from the published model.  This is sound, but the kill then loses `segPinCForward`, and
     W9a must split PDep pins at every rfi.
2. **Rule 7.**
   - (a) Make `grcsc` riscv.cat-faithful: RCsc = any aq/rl on AMO/LR/SC.  First check that the decoder emits
     `LStore rl`/`LLoad aq` only for atomics.
   - (b) Keep the weak rule 7 plus a conformance side-condition "no rl-annotated write followed by an aq read".
     This is vacuous for the kernel.
   - (c) Leave it, and carry the Bad-arm burden in user rows.
3. **Gate 3 ownership.**
   - (a) W10 absorbs it (W10 → L).
   - (b) A new item W12b `Weak/CatFloor.lean` (M–L), scheduled with W12.
   - (c) Restrict the walk to kernel rows and defer the user-row aq/rl cases.
4. **Forwarded `LLoad aq`.**
   - (a) A row side-condition "no plain `LLoad aq`" (true for the kernel).
   - (b) Change WeakMem's `fwdView` for aq, which ripples into T1.
   - (c) Accept it as a named gap for user code.
