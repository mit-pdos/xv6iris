# E-b progress — G4 deciding experiment E-b: track (b)'s NF_R without (P2) `fetchBounded`

Owner ruling [OWN.P11] (context.md item 18, "G4. Do B"); brief ~/dev/weak-orch/promising/Eb_prompt.txt;
G4-review.md §4(1), §5 B-1, §6.  Workspace /home/bsdinis/dev/xv6iris-pcsl4.

## Status (top): PASS — GREEN (2026-11-04).
- `Nfr.F.nfRF` (plan §3 class) and `Nfr.F.nfRF_pre` (S4b3 `relClassPre`): every valid machine-v2 run (`D = Unit`)
  has an NF run with the same final configuration and traces — NO fetch premise, no other premise.
- `Own.ownAdequacyF`: `ownAdequacy` with the same client premises, NO `fetchBounded`.
- G4 verdicts re-derived from it: `Own.X.L1c.g4_lock1cF` (G4 (1c)+(3), xv6 text), `Own.MPL.g4_mpOwnLF` (G4 (2)).
- `#print axioms` (Weak/Prom/EbCheck.lean) of all five: propext, Classical.choice, Quot.sound.  0 named inputs.
- Lines: 1,376 new (NfrFetch 951 — of which ≈600 the adapted NfrRun schedule; OwnWpF 268 — ≈180 the adapted
  `nf_sim`; OwnG4F 157 — the two theorem bodies, only the adequacy call changed) + 12 edited lines (below).
- Builds: `lake build Weak.Prom.NfrFetch`, `lake build Weak.Prom.OwnG4F` green; the whole dependent set (every
  module importing an `Own*`/`Nfr*` module, /tmp/eb_mods.txt) rebuilt — see "Build of dependents" below.

## The new arm
- Language (OwnLang.lean, [E-b] edit): `hstepO.fetch` — a fetch whose bytes are `fetchByteOk w.img w.M ws`
  (value and FENCE.I window read in the FINAL memory `M`), post = Machine.lean's fetch post with
  `fetchView (M.take σ.n) h (σ.pr h)`; no language-state change.
- NF run shape (NfrFetch.lean `nfStepsF RC pstep M`): NfrRun's `prom`/`st`/`rel` + `fet` (same arm on configs).
- `fetchView_cut`: the prefix/cut-promise fetch view equals the solo run's (an own message above the prefix is
  still promised, so `ownDone` is false on both sides).

## What changed in nfR / adequacy
- Self bound `bndF ws := vrOld ⊔ vwOld` (drops `wIfr`); invariant `fwdB` (forwarded timestamps ≤ `bndF`) replaces
  `psBounded`.  `memStep_selfF`: every NON-fetch read and every fulfil ≤ `bndF` of the post-state.  A release at
  `r` has `bndF < r` from its class alone (`RCOk.lt_`), so (P2)'s `wIfr < r` is no longer needed; fetch steps of
  the segment are replayed by `fet`.
- Schedule generic in the release class (`RCOk`: `none_`, `lt_`, `reads_`); instances `rcOk_plan`, `rcOk_pre`.
- `nf_simF` = `nf_sim` + the `fet` case (one `hstepO.fetch` step).  `ownAdequacyF` = `ownAdequacy` via `nfRF`.

## Review sketch checked against the definitions
- TRUE: `ldPre`/`stPre` contain `wIfv` (Machine.lean:270–278); `LInstr` resets `wIfv` (:646); `wIfr` is read only
  by `fenceIPost` (:503) and `wIfl` only by `fetchByteOk` (:473); no-access labels (`LRegW`, `LCtrl`, `LFence`,
  `LFenceI`, `LInstr`, `LExFail`) move no view from `wIfv`.
- FALSE (not load-bearing): "the FENCE.I window inside the prefix since wIfl ≤ bnd".  Counterexample: a hart
  fetches an ALU instruction whose byte was written at timestamp 5 by another hart (stale-or-fresh fetch is
  allowed), executes FENCE.I (`wIfl := max … wIfr ≥ 5`), then a release store at r = 3 (its views are ≤ 2).  The
  segment before r runs against `M[..2]` while `wIfl = 5`.  Harmless: the arm reads the window in `M`, exactly as
  the solo run against `M` did.
- IMPRECISE (not load-bearing): "machine v2 orders a fetch before every explicit access of its own instruction" —
  the machine orders only accesses that FOLLOW the fetch before the next `LInstr` (abstract `pstep`; Sail's
  emission order is what makes it per-instruction), and `fetchView` exempts own fulfilled stores (≤ `vwOld`).
  A zero-byte release load (`LLoad … rl … []`) copies `ldPre ⊇ wIfv` into `wVRel`, which survives `LInstr`.  None
  of this is used: the proof never reasons about which instruction a fetch belongs to — any access whose pre-view
  absorbed an above-r fetch view has a post-view (hence `bndF`) above r, which the release class excludes.

## Edits to existing files (minimal, tagged [E-b])
- OwnLang.lean: + constructor `hstepO.fetch` (10 lines).  `nf_sim` unchanged (old adequacy unchanged).
- OwnKit.lean: `hstepO_cases` gets an auto-discharged premise `hnf` (label is not a fetch); `hstepO_pstep` by
  `cases`; `hstepO_quiet` passes `hnf`.  Statements of every downstream kit lemma unchanged.
- OwnMPDefs.lean / OwnMP.lean (part-1 label-level MP, superseded): `tp_fetch` (tpStep never fetches) + one
  `| fetch` alternative in each of the 5 direct `cases` on `hstepO`.

## Walks (P3) and A/D (P4) outlook (not modelled: translation off, [OWN.P3])
- Walks: same shape as fetches — a walk reads, writes nothing, and its view goes to a bank consumed by the
  access's pre-view (M14/M18) and never by `ctrl`.  Needed: a prophecy-fed walk arm (bytes against `M`, the
  SFENCE floor `wSfv` read in `M` like `wIfl`), the walk bank kept out of `bndF`, `fetchView_cut`'s analogue for
  any own-store exemption.  Expected a near-copy of the fetch arm (≈0.3–0.6k) once the machine arm exists.
- A/D: an A/D update is a WRITE (a message with a timestamp), so reading `M` does not help.  If its arm raises
  `vwOld` to its timestamp, NF_R needs nothing (the release class then puts it below r).  If a speculative A update
  has no view effect (review A-2's case), its timestamp is unbounded by `bndF` and the segment would fulfil a
  message above the prefix.  Two candidate fixes: (i) a prophecy-FULFIL arm for the INERT class `ad` (the hart
  fulfils `M[ta]` early; the agent appends it later as already fulfilled — needs pre-fulfilled bookkeeping in
  `OSt`); (ii) defer the A/D step to when the log reaches `ta`, if its post commutes with the hart's later steps
  (it raises `coh` on PTE bytes only; floors above the prefix are restriction-safe).  Looks feasible (engineering,
  ≈1–2k), not demonstrated; it depends on the exact WPAd/WPAspec arms, which do not exist yet.

## Build of dependents
- `lake build` of all 69 modules importing an `Own*`/`Nfr*` module (tracks (a) and (b), RepairCheck, MachFixCheck,
  the new files): green, 521 jobs, 0 errors.  The old `ownAdequacy`/`nfR` and every old G4 theorem still build.
