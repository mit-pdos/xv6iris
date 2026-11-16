# PROGRESS — InfWit (gap G5: a Lean vacuity witness for `inf_mpLoop`)

Owner 2026-11-16 (verbatim): "Start with G5" — CutReview.md §2(ii)/§4 "no Lean vacuity witness `infExec tLoop
E_SC`".  Worker: Opus, workspace pcsl8.  Files (new only): `Weak/Prom/InfLoopWit.lean` (namespace
`Weak.Prom.InfLoop.Wit`).  No root edits, no edits to existing files.

## Status

**GREEN — PASS (2026-11-16).**  `lake build Weak.Prom.InfLoopWit` succeeds (via lean-gcp), no warnings in the new
file; 624 new lines in 1 new file.  Not imported from the `Weak` root (no root edits; coordinator to add
`import Weak.Prom.InfLoopWit`).

* `E_SC` (InfLoopWit.lean:216) — the SC interleaving of `tLoop`, run forever.
* `infExec_witness : infExec tLoop E_SC` (:568) — EVERY conjunct of `infExec` (PfxDefs.lean:247).
* `inf_mpLoop_exercised` (:580) — the statement from the brief verbatim: `E_SC`, hart 1, `i = 3` (2nd-iteration
  flag load, returned `[1,0,0,0]`), `j = 5` (data load); `k = 4` (the fence) is the only index between.
* `witness_concl` (:594, direct computation) and `witness_concl_thm` (:598, from `inf_mpLoop`):
  `(E_SC.ev (1, 5)).rdat = [1,0,0,0]`; `inf_mpLoop_exercised_concl` (:609): premises and conclusion together.
* `witness_first_flag` (:575): hart 1's first flag load `(1, 0)` reads `[0,0,0,0]` (the initial value).
* `#print axioms` of all four headline theorems = `[propext, Classical.choice, Quot.sound]`.  No
  sorry / axiom / native_decide / opaque / implemented_by.
* Optional item (3) skipped (not required).

## Construction

* Run: `stS h k` = `k` iterations of `nxt` (the `stepL` result on the instruction at `pc`; the TAKEN side of
  `beq zero,zero,0`'s fork).  Invariant `J` (:91): `pc = k % 4`, `ii = k`, `ctl = []`, `evs` = the first
  `cnt k = 3⌊k/4⌋ + min (k%4) 3` events of the closed form `evF h i = evP h (i/3) (i%3)`, `x12 = X`, `x13 = Y`,
  `x6 = 1` (hart 0), every path condition is `beq 0 0` taken.  `J_step` (:159): 8 cases (hart × pc), each via
  InfLoopRef.lean's `stepL_store`/`stepL_load`/`stepL_fence`/`stepL_br`; it also yields the `LStep`.
* gmo: `rkS (h, i) = 2·(2⌊i/3⌋ + (i%3)/2) + h` on memory ops (`i % 3 ≠ 1`).  ν: `(1,0) ↦ [0,0,0,0]`, else
  `[1,0,0,0]`.
* `ppoAxI`: every ppo / I/O-order edge carries `poS`; po = `ii` order = rank order on a hart (`po_gmo`).
* `loadValueAxI`: candidates of hart 1's load are hart-0 stores to the same address with smaller rank
  (`cand_fwd`/`cand_bwd`); the latest one is explicit (`i-1` for a flag load `i ≠ 0`, `i-2` for a data load);
  load `(1,0)` has none → initial value 0.
* `atomicityAxI`/`scAxI`: vacuous (no event has kind `lr`/`sc`).  `progressAxI`: pigeonhole `no_inj_bound`
  (an injection `Nat → [0, 6·rk e)` is impossible).
* No conjunct was unsatisfiable.  None was materially harder than expected; the load value axiom is the longest
  part (~100 lines).

## RVWMO first

`infExec` is the reference's notion of an execution (rvwmo.adoc:307–310, the progress axiom :350–351, loops via
`stepL`); the witness is an SC interleaving, which every RVWMO-allowed-behaviour reading admits (SC executions
satisfy every ppo rule because gmo extends po).  FAITHFUL — the witness only instantiates the reference; it adds no
modelling input.
