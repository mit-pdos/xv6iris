# MachZiccid — machine v2's fetch arm becomes Ziccid's ([OWN.P22] "Ziccid rule now")

Brief: `~/dev/weak-orch/promising/MachZiccid_prompt.txt` (+ `MachZiccid-advice.md`, `wave4_common.txt`).

## Status (top): GREEN (2026-11-18)

* `lake build Weak` green (3947 jobs; baseline before any edit: 3945, green).  `Weak.Prom.SailS0Fetch` is now in it.
* `tools/ci/lint.sh`: all lints passed (it FAILED at baseline: drift on SailS0Check/SailS0Fetch, see edits).
* `tools/ci/audit.sh --build` (builds Xv6 MachCSL): exit 0, 0 `sorryAx`, no axiom outside the baseline kinds.
* `tools/ci/audit.sh --build --weak`: exit 0, 0 `sorryAx`.
* Axioms of every new theorem: `propext, Classical.choice, Quot.sound`.  No sorry/axiom/native_decide/opaque/
  implemented_by.  No kill fired (no arm reads `prom` beyond fulfil membership; repairs ≪ 3k lines).
* Probe re-run for `fence.i` flips: 541 flips (all `fence.i`, all eq → STRONGER), see "Findings".

## The arm (Weak/Prom/Machine.lean `memStep.fetch`, quoted)

```
| fetch (prom : GSet Nat) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (vf : Nat) :
    max ws.wIfv ws.wIfl ≤ vf →   -- [MachZiccid]
    vf ≤ log.length →   -- [MachZiccid]
    bytesAll (fetchByteOk img log vf) base tvs →
    memStep prom ws (LIFetch base tvs) none
      { ws with
        wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
        wIfv := vf }   -- [MachZiccid] was `max wIfv (fetchView …)`, reset at `LInstr`
      prom
def fetchByteOk (img) (log) (vf : Nat) (a) (t) (v) : Prop :=
  memByte img log t a = some v ∧ t ≤ vf ∧ ¬ writesIn log a t vf
def fenceIPost (ws) := { ws with wIfl := max ws.wIfl (max ws.wVrOld ws.wVwOld) }   -- was `… ⊔ wIfr`
| instr … : memStep prom ws LInstr none { ws with wLdv := 0, wRmw := none } prom    -- no longer `wIfv := 0`
```
`ownDone` and `fetchView` (the own-store exemption) are deleted.  `ldPre`/`stPre` unchanged (keep `wIfv`).
Docstrings quote ziccid.adoc Ziccid_fetch_global_order / _fetch_value / _fetch_before_access / _fence-i_op /
_model_scope, mark FAITHFUL (Ziccid), STRONGER than the Zifencei-only letter [OWN.P22], and state: (i) every later
explicit access is above every earlier fetch (consequence of order + before_access, not stronger); (ii) FENCE.I thereby
orders all older accesses before all accesses of subsequently fetched instructions (Ziccid :123–137), STRONGER than
Zifencei (EX-FENCEI-1/[OWN.143] "not a data fence" = Zifencei letter only); fetch-free `litStep` does not see this
(MachLitmus.lean reworded); (iii) scope: every `LIFetch` is a main-RAM read (`ramRead`), RAM taken as coherent +
cacheable; a device-address fetch is an `LDev`; (iv) the cmo.adoc invalidate clause names loads only, not applied to
fetches; (v) liveness (:109–114) and the bounded buffer not modelled, WEAKER.  Header :27–29 amended as the brief says.
`vf` is a constructor argument (as the load arm's `vi`); label and `PEvt` unchanged; `vf` = post-state `wIfv`.

**`wIfr`: KEPT, still updated by the fetch, INERT** (no arm reads it; FENCE.I no longer does).  The smaller safe
change: track (b)'s NF_R files (NfrPre/NfrRun `fetchBounded`, `soloQ_ofImg`) state and prove facts about `wIfr`;
removing it would refactor them.  Invariant `wIfr ≤ wIfv` = CoreFwd's new `fetchInv`.

## Theorems (Weak/Prom/MachZiccidCyc.lean, new; imported from Weak.lean)

* `memStep_ifv_mono` :81 — `wIfv` non-decreasing under EVERY arm.
* `memStep_fetch_src` :113 — a fetch sets `wIfv ≥` each source.
* `memStep_fulfil_gt` :120 — every fulfil (store, rmw, amoSt, sc, cmo) has `wIfv < ts`.
* `pmStep_ifv` :138, `pmSteps_fulfil_gt` :157, `pmSteps_fetch_lt` :180 — in ANY run (any `pstep`, any fabric) every
  timestamp a hart fetched is below every timestamp it fulfils later.
* `no_fetch_own_then_fulfil` :213 — the S-0 cycle is impossible; `no_fetch_cross` :221 — the two-hart cross cycle
  (A fetches B's promise and later fulfils its own, B fetches A's and later fulfils its own) is impossible.
* NON-VACUITY: `fetch_image_ok` :251 (never-written text, image bytes, EVERY `vf ∈ [max wIfv wIfl, |log|]`),
  `fetch_image_vf0` :272 (`vf = 0`, against ANY log), `fetch_image_psInit_mpFF` :293 (mpFF's first word, log
  overwriting it: the stale image fetch is still admissible).
* Weak/Prom/SailS0Fetch.lean: `fetch_own_then_fulfil` (now unprovable) REPLACED by
  `fetch_own_then_fulfil_impossible` :46 (same shape — fetch `tvsAt t m.data`, `LInstr`, any write fulfilling `t` —
  from any state, conclusion `False`) + the mpFF-instance `example`.
* `fetchBounded` (NfrRun :727) is now provable (`t ≤ wIfr ≤ wIfv < r`): NOTE only, not refactored.

## Edited files + reason (every edit tagged `[MachZiccid]`)

| file | reason |
|---|---|
| Weak/Prom/Machine.lean | the arm, `fetchByteOk vf`, `fenceIPost`, `instr`, `ownDone`/`fetchView` deleted, header + docs |
| Weak/Prom/MachZiccidCyc.lean | NEW: impossibility + non-vacuity |
| Weak.lean | import MachZiccidCyc (new) and SailS0Fetch (rewritten proof module; the drift lint failed on it) |
| tools/ci/lint_allow.txt | allow row for Weak/Prom/SailS0Check.lean (`#eval` only; pre-existing drift failure) |
| Weak/Prom/SailS0Fetch.lean | lemma replaced by its impossibility (brief (2)) |
| Weak/Prom/MachWf.lean | fetch case (`wIfv := vf ≤ |log|`), instr case |
| Weak/Prom/MachFactor.lean | fetch case of `memStep_extend`; `ownDone_ext` removed; header |
| Weak/Prom/MachExplore.lean | `fixPost LInstr`; new `fetchOkB` |
| Weak/Prom/MachSound.lean | `memStepF` (vf = max wIfv wIfl), `memStepL` (every vf ∈ [max wIfv wIfl, |log|], `fetchVfs`), soundness |
| Weak/Prom/MachComplete.lean | `memStepL` completeness for the fetch; `memStep_reads` pattern |
| Weak/Prom/MachSail.lean | explorer `succFetch` enumerates vf |
| Weak/Prom/MachLitmus.lean | doc :34–35 reworded (fetch-free level WEAKER for fence.i programs) |
| Weak/Prom/Emit.lean | docs :60, :333, :427 (monotone fetch view; Ziccid scope = RAM) |
| Weak/Prom/CoreFwd.lean | `plainFloor` uses `wIfv`; `fetchInv := wIfr ≤ wIfv`; `fetch_srcs_le` (was `fetchView_le`) |
| Weak/Prom/CoreRules.lean, CoreKit.lean, CoreKitV.lean, CoreRun.lean | `LInstr` post; `instrR_ifv`; `fwdMono_bound` hyp; fetch pattern |
| Weak/Prom/CmpInv.lean, CmpStep.lean, CmpSimN/F/Ld/S/SC/LA/A/WB.lean | `instrE` keeps `wIfv`: `SimInv.ifv` is CARRIED (`hinv.ifv`), not re-established by rfl |
| Weak/Mini/EqMachMem.lean | `relWs_instr` (`hR.ifv`) |
| Weak/Prom/NfrStep.lean | `bnd` uses `wIfv` (was `wIfr`); `memStep_restrict` takes `hvf` (fetch view in the prefix); `memStep_bndN` takes `hvf`; fetch/instr cases |
| Weak/Prom/NfrRun.lean, NfrPre.lean | `hbz` via `memStep_fulfil_gt`; `hvf` args; fetch patterns; `fetchBounded` note |
| Weak/Prom/NfrFetch.lean | `fetchPost vf`, `fetchAt`, `fet` takes `vf`; `fetchView_cut` removed |
| Weak/Prom/NfrAd.lean, AdMachine.lean | the variant's fetch arm = v2's (`ownDoneV`/`fetchViewV`/`…_cut`/`…_ext` removed) |
| Weak/Prom/OwnLang.lean, OwnWpF.lean, OwnBE4Lang.lean, OwnAd.lean, OwnAAdMP.lean, OwnAAdWp.lean | prophecy-fed fetch takes `vf`; `ownDoneV_eq`, `fetchViewV_le` removed |
| Weak/Prom/ProbeCov.lean | `fetchG` logs the new premises p1–p3 |
| Weak/Prom/TableCv2.lean | rows: C-A.fetch.p2/p3 added; C-A.instr.w.wIfv, C-A.br.fetchView.if1, C-A.br.ownDone.m1.* removed; fetch/FENCE.I rows re-marked `PF:ziccid.adoc … FAITHFUL (Ziccid), STRONGER than the Zifencei-only letter`; `wIfr` rows INERT |

## Findings (fence.i flips — reported, NOT repaired)

Probe matrix re-run on the VM after the change (`ProbeRun.lean` G1 (48 shards), G1b, G1w, G1lxs, G3, G5, TS, ROW;
`ProbeG2.lean`; `notoday`), compared with the 2026-11-03 v2 results `~/dev/weak-orch/promising/litmus/s0rest/res-*.txt`:
* **541 probes changed, every one `SR=eq → SR=STRONGER`** (Sail level loses exactly the outcome(s) the reference
  allows), and every one has a `fence.i`: 540 G1 probes `<shape>:<ev>:fi:<ev>` (shapes 2+2W 77, Rr 66, Sr 59, MPr 50,
  Rw 50, IRIW 50, SB 45, Sw 43, LB 36, WRC 33, MPw 31; of 3650 G1 `fi` probes; the Co* shapes never change) and
  **ROW `iriwCtrlFi`** (RefTests row 25, repo `SAFE/IRIW+ctrlfenceis`, text ALLOWED): Sail-level verdict A → **F**,
  the only text-verdict change.  Cause: Ziccid's FENCE.I (`wIfl ⊔= vrOld ⊔ vwOld`, next `vf ≥ wIfl`, every later
  access above `vf`) orders every older access before every access of a later-fetched instruction — the stated
  consequence (ii), FAITHFUL (Ziccid :123–137), STRONGER than RVWMO+Zifencei (whose reference/herd allow them).
* Label level (`MR`, fetch-free `litStep`) unchanged everywhere (all `eq`), as stated in MachLitmus.lean.
* No non-`fence.i` probe changed.  G2: 988 eq / 41 WEAKER (baseline file 1002 / 42 over 1044 probes; the family is
  1029 probes in this tree); one difference, `csrchain:ssp` (now `oos=[trap]`, outs=0), is a CSR trap with no fetch
  view involved — it predates this stage (the baseline file is older than the current G2 family), not a flip.
* NOT re-run: the litmus-corpus Sail oracle (`MachSailOracle.lean`; corpus + herd logs are not in this workspace).
  In its baseline 991 `fence.i` tests ran through Sail, 471 with Sail verdict `Sometimes` — the candidates to flip.
* Consequence to flag: for programs with `fence.i`, machine v2 at Sail level is now STRONGER than the RVWMO
  reference (completeness reference ⊆ machine fails there; [OWN.P22] accepted STRONGER than the Zifencei letter).
* Performance: `succFetch` enumerates `vf ∈ [max wIfv wIfl, |log|]`; the probe matrix took tens of minutes wall on 48+
  shards (was ≈ 4 min on 90).

## Increment log
1. Machine.lean edits; MachZiccidCyc.lean; core files (MachWf/Factor/Sound/Complete/Sail/Explore, NfrStep, CoreFwd).
2. Nfr*/Own*/AdMachine/SailS0Fetch/ProbeCov/TableCv2; Cmp* (`SimInv.ifv` carried).  `lake build Weak` green.
3. lint (SailS0Fetch imported, SailS0Check allow row), audit --build, audit --build --weak: green.
