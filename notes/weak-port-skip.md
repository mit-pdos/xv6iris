# Weak port: files NOT ported (archive / superseded, needed by no live file)

Owner decisions: skip superseded files; D5 skip the archive (WeakSailLTS*, WeakCompose*, WeakShape*). Computed as the archive/superseded candidates minus those a live file imports (transitively). Archive/superseded files that ARE imported by live files (AxCondM*, AxRelease4/5, AxSymMem3, WeakRobustL2, WeakSailLTS, WeakSailLTS2) are ported, possibly only the parts live files use.

- WeakCompose
- WeakComposeLang
- WeakRobustL2b
- WeakSailCone
- WeakShape
- WeakShapeAst
- WeakShapeDec
- WeakShapeExec
- WeakShapeExecGen01
- WeakShapeExecGen02
- WeakShapeExecGen03
- WeakShapeGen01
- WeakShapeGen02
- WeakShapeGen03
- WeakShapeGen04
- WeakShapeGen05
- WeakShapeGen06
- WeakShapeGen07
- WeakShapeGen08
- WeakShapeGen09
- WeakShapeGen10
- WeakShapeGen11
- WeakShapeGen12
- WeakShapeGen13
- WeakShapeGen14
- WeakShapeGen15
- WeakShapeLive
- WeakShapeMem
- WeakShapeOverrides
- WeakShapeOverrides2
- WeakShapePeel
- WeakShapeTop
- WeakShapeWin
**Added 2026-10-06:** `WeakSailLTS`, `WeakSailLTS2` — archive. Their only live consumer is `WeakSailComplete`, and the ~180 live files importing `WeakSailComplete` use only its register-file section (`regs_agree*`, `seip_reg`, `register_lookup_set_ne`; `coh_fence_post` / `wp_pf_step_inv` are same-named copies elsewhere). So `WeakSailComplete` is ported as its register-file section only (the rest is archive), and the LTS chain is not ported. (A full port of `WeakSailLTS` exists but is not merged: under O2 its `sailShaped` premise is false at every fetch, so its theorems would be vacuous.)
