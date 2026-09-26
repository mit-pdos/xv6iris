# `#print axioms` baseline for the system theorem (8-5 SA-7)

The Lean analogue of Rocq's "adequacy-print baseline".  Check with
`#print axioms Xv6.xv6FsAdequacy` / `Xv6.xv6FsAdequacy_xv6GF` (the last lines of
`Xv6/SystemAdequacy.lean`); both print the same set.

Measured 2026-09-26 on the main tree (lean-v2 e87d4f78e + SA-7's files).

## Expected (anything else is a regression)

1. Lean core: `propext`, `Classical.choice`, `Quot.sound`.
2. The six Sail platform externs (`LeanRV64D/RiscvExtras.lean`):
   `cancel_reservation`, `load_reservation`, `match_reservation`,
   `valid_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`.
3. `<decl>._native.bv_decide.ax_*`: the per-lemma trust in the compiled
   `bv_decide` checker (`Lean.ofReduceBool` class).  416 at this measurement
   (388 at `Xv6.UserretClosed`, de4a093f3); the count grows with the proofs.

`USER`, `Himg` (and, until the environment knot is fixed, `Hknot`) are
HYPOTHESES of the statement, not axioms.  The reset table is inside
MachCSL's language definition (trusted by construction until wave 9).

## Found at this measurement (flag, pre-existing)

* `Xv6.Kvm.dcounts._native.native_decide.ax_1_1` -- a `native_decide`
  axiom (`Xv6/KvmCounts.lean:46`), reached through `LinkMain`.  It is not a
  `bv_decide` axiom, so by the brief's rule it is "another `_native` kind":
  either accept it into this baseline (same trust class: the compiled
  evaluator) or re-prove `dcounts` by `decide`.

No `sorryAx`, no `Xv6.*`/`MachCSL.*` plain `axiom`.

## How to re-measure

```
lake env lean Xv6/SystemAdequacy.lean 2>&1 | tr ',' '\n' | grep -v '_native.bv_decide.ax_'
lake env lean Xv6/SystemAdequacy.lean 2>&1 | tr ',' '\n' | grep -c '_native.bv_decide.ax_'
```
