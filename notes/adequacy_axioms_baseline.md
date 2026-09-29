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

## USER proved (Sept 26 2026, lane U4; `hZkr` removed Sept 29, see the last section)

`Xv6.userProof (hZkr : ∀ C P, UclCsrZkr C P) : USER` (Xv6/ProofUser.lean) and the USER-free corollary
`Xv6.xv6FsAdequacy_closed` (Xv6/LinkSystemAdequacyClosed.lean; a Link file because it imports ProofUser):
hypotheses `hZkr`, `g.gen = 0`, `g.pow = false`, `diskOf g.m.devs = fsImgDisk`.

| theorem | besides propext / Classical.choice / Quot.sound |
|---|---|
| `Xv6.userProof` | 58 `_native.bv_decide.ax_*` |
| `Xv6.xv6FsAdequacy_closed` | 470 `_native.bv_decide.ax_*` |
| `Xv6.xv6FsAdequacy_xv6GF` | 426 `_native.bv_decide.ax_*` |

`hZkr` covers only the user CSR rows for 0x747/0x757 (mseccfg/mseccfgh): today the model has NO step there
(the Lean backend's eager `&&` reaches `currentlyEnabled Ext_Zkr`, whose clause is missing because the Zkr
module isn't compiled). It disappears under either fix: Sail's one-line Zkr clause in regen_sail_model.sh,
or the backend's short-circuit fix (upstream patch prepared in /shared/sail-upstream). User decision pending.
BootReset phase 3 (Sept 29 2026): the `MachCSL.resetVal` register reset table is GONE. `bootFacts`' register
clause is a run of `bootProg` from arbitrary power-on garbage (Rocq `boot_facts`); axioms of the three
theorems unchanged in kind (propext, Classical.choice, Quot.sound + bv_decide certificates; 958 -> 962 lines).

## `hZkr` gone: the model short-circuits `&`/`|` (Sept 29 2026, lane ZKR-SC)

The model is regenerated with the short-circuit Sail Lean backend (sail 5745ea9e + the
`lean-short-circuit` commit d0ef9371 of /shared/sail-upstream; see tools/regen_sail_model.sh). The
hypothesis is discharged, not assumed: the CSR rows for every csr number (0x747/0x757 included) are plain
walks of the model's `check_CSR_result`.

    Xv6.userProof : Xv6.USER
    Xv6.xv6FsAdequacy_closed : ∀ {hlc} (g : GState), g.gen = 0 → g.pow = false →
      diskOf g.m.devs = fsImgDisk → ∀ n κs t2 g2, NSteps n ([Expr.power], g) κs (t2, g2) →
        (∀ e2 ∈ t2, Reducible (e2, g2)) ∧ xv6TracePure fsimgCov fsimgSb.sbLogstart g2

Measured on lean-v2 e3ba2e72e + the lane's commit (GCP full build, 2476 jobs):

| theorem | besides propext / Classical.choice / Quot.sound |
|---|---|
| `Xv6.userProof` | 70 `_native.bv_decide.ax_*` |
| `Xv6.xv6FsAdequacy_closed` | 484 `_native.bv_decide.ax_*` |
| `Xv6.xv6FsAdequacy_xv6GF` | 428 `_native.bv_decide.ax_*` |

No `sorryAx`, no plain `axiom` of Xv6/MachCSL. (The extra certificates are the per-branch `bv_decide`s of
`UWalk.uwk_pte_is_invalid`, whose walk now splits on the entry's bits.) The model's `currentlyEnabled`
still has no `Ext_Zkr` clause; no proved path reaches it (see notes/coord/user_residuals.md).
