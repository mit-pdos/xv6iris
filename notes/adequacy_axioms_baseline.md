# `#print axioms` baseline for the system theorem (8-5 SA-7)

The Lean analogue of Rocq's "adequacy-print baseline".  Check with
`#print axioms Xv6.xv6FsAdequacy` / `Xv6.xv6FsAdequacy_xv6GF` (the last lines of
`Xv6/SystemAdequacy.lean`); both print the same set.

Measured 2026-09-26 (U0-M, D51: branch off lean-v2 459a051cb, GCP full build).
Previous measurement: lean-v2 e87d4f78e + SA-7's files.

## Expected (anything else is a regression)

1. Lean core: `propext`, `Classical.choice`, `Quot.sound`.
2. `<decl>._native.bv_decide.ax_*`: the per-lemma trust in the compiled
   `bv_decide` checker (`Lean.ofReduceBool` class).  416 at this measurement
   (388 at `Xv6.UserretClosed`, de4a093f3); the count grows with the proofs.

That is all.  `USER`, `Himg` (and, until the environment knot is fixed,
`Hknot`) are HYPOTHESES of the statement, not axioms.  The reset table is
inside MachCSL's language definition (trusted by construction until wave 9).

## The Sail platform hooks are definitions (D51, 2026-09-26)

The six Sail platform externs that used to be listed here
(`cancel_reservation`, `load_reservation`, `match_reservation`,
`valid_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`)
are no longer axioms.  As in Rocq (`model-xv6iris/xv6iris_extras.v`), the
generated model is left alone: the hand-written `model/Xv6Extras.lean` is fed
to sail as a second `--lean-import-file` by `tools/regen_sail_model.sh`, and
its definitions in `LeanRV64D.Functions` take precedence (namespace priority)
over the fork's root-level axioms of the same names in `RiscvExtras.lean`,
which stay declared but unused.  Realisations (Rocq's): the two effectful
reservation hooks and `plat_term_write` are `pure ()`, experimental extensions
are `false`, and `match_reservation` / `valid_reservation` read the `opaque`
constants `xv6_resv_matches` / `xv6_resv_is_valid` (Rocq's `Parameter`s
`resv_matches` / `resv_is_valid`: arbitrary but fixed, never unfolded, so every
proof handles both answers).  Being `opaque` (inhabited, with a hidden value)
rather than `axiom`, they do not show in `#print axioms`; that is the one
difference from Rocq's audit, which lists its two `Parameter`s.  Term-level
equations: `MachCSL/SailHooks.lean` (Rocq `ResvAxioms.v`).

Still axioms in the fork's `RiscvExtras.lean`, deliberately NOT realised (as in
Rocq; results are consumed, so a realisation would fabricate data) and NOT
reached by the system theorem: `plat_term_read`, `get_16_random_bits`, the
softfloat `riscv_f*` family.  Their appearance here would be a regression.

## Resolved since the previous measurement

* `Xv6.Kvm.dcounts._native.native_decide.ax_1_1` (`Xv6/KvmCounts.lean`) no
  longer appears.

No `sorryAx`, no `Xv6.*`/`MachCSL.*` plain `axiom`.

## How to re-measure

```
lake env lean Xv6/SystemAdequacy.lean 2>&1 | tr ',' '\n' | grep -v '_native.bv_decide.ax_'
lake env lean Xv6/SystemAdequacy.lean 2>&1 | tr ',' '\n' | grep -c '_native.bv_decide.ax_'
```
