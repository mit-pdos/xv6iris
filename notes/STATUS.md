# Lean xv6 port — status

**2026-09-30.**  All three top theorems are closed, in step with Rocq main (456141b5b) except the
noninterference work (Rocq drift themes I+J, deliberately not ported):

- `Xv6.xv6FsAdequacy_closed` — the system theorem (hypotheses: generation 0, power off, disk = `fs.img`).
- `Xv6.userProof : USER` — the user-mode machine layer, no hypotheses.
- `Xv6.unionAdequacyClosed` — union adequacy for init/sh/cat/grep/echo/seccomp/sync, concluding
  `unionPhiSync`; with `Xv6.unionSyncCutNeg` and `Xv6.unionResults`.

Their axioms are `propext`, `Classical.choice`, `Quot.sound` and `bv_decide` certificates only; CI checks
this (`tools/ci/audit.sh`, baseline `tools/audit/baseline.json`).

- **CI**: `.github/workflows/lean-ci.yml` (branch `lean`); every step is `tools/ci/run_all.sh <step>`
  (`make ci`); see README "Continuous integration".
- **Design and project notes** (imported from the Rocq tree; the design this port follows):
  `claude-notes/` — start with `claude-notes/LEAN.md`, then `claude-notes/README.md`.
- **Design rulings** cited in source comments: `notes/design-rulings.md`.
- **Rocq drift survey** (what moved 1900b8a43 → main, what was ported): `notes/rocq_drift.md`.
- **Axiom baseline history**: `notes/adequacy_axioms_baseline.md`; cone re-audit: `notes/cone_reaudit.md`;
  device conformance: `notes/device-conformance.md`.
