# AxDeps.v §3-REPORT: unmasking load address dependencies

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../claude-notes/LEAN.md)).

Full text moved out of `iris/AxDeps.v`'s header (which now carries only a
short pointer to this file) so the header stays readable. Context: LB/AxSL
G0.5, the tagged-dependency file `iris/AxDeps.v`
([`design/weak-memory-lb-axsl.md`](../design/weak-memory-lb-axsl.md) §0/§2).

Nothing below has changed since it was written — it documents an existing
gap (D-8) in the tree's emission, not anything this file's soundness fix
touched. **UPDATE (soundness fix):** the last bullet below ("MEANWHILE the
fold below recovers the general rule 13 WITHOUT the unmasking through F5'")
described a feed that was in fact UNSOUND and has since been REMOVED from
`dstep_t`'s `LRegW` arm — see `iris/AxDeps.v`'s header correction and
`row_deps_t_r13_masked` (now `[]`, matching the tree's `row_deps_r13_masked_gap`).
The general rule-13 edge is recovered only once D-8 below is unmasked, exactly
like rule 9's load half.

## §3-REPORT: UNMASKING LOAD ADDRESS DEPENDENCIES

- WHO EMITS THE `LLoad` LABEL'S `asrc`: `WeakEvInst.pnode_step`'s plain
  RAM read arm (WeakEvInst.v:314-315) writes the LITERAL `[]` —
  `LLoad aq false pa tvs []` — and the language twin
  (`WeakEvLang.emonad_step`, the `MemRead` arm ~:900-945) applies
  `load_post_run` with NO address view; the exclusive read one arm
  below carries `deps_asrc (deps_of_ib (ib_bits ib))` and the
  σ-effect `exload_post_run_d … (srcs_view ws0 (deps_asrc (edeps σ
  c)))` (WeakEvLang.v:936). Shape lemmas hard-code the `[]`:
  WeakEvInst.v:466, 729, 811, 1094, 1226-1275.
- WHY `[]` TODAY (D-8, WeakEvLang.v:751-760; `WeakDeps.deps_asrc`): at
  the `MemRead` node the walker's PTE read and the load's data read
  are indistinguishable (both `AK_explicit` plain, `va = None`, the
  model emits no `TranslationStart`/`TranslationEnd`), so attaching
  `rs1` would attach it to the PTE reads too. The decoder HAS the
  operand: `WeakDeps.deps_addr (ORload _ rs1) = dsrc_of_num rs1`;
  `deps_asrc` masks the `ORload` arm to `[]`.
- THE BITS ARE AVAILABLE AT THE NODE: `InstrAnnounce` records the
  opcode (`ib_ann (ib_of_bvn ob)`, WeakEvLang.v:1021-1027) and the
  store arm at the SAME `MemRead`/`MemWrite` node already reads
  `deps_of_ib (ib_bits ib)` (WeakEvInst.v:328,344), so `rs1` is
  available exactly where the load label is built.
- TO UNMASK: (i) `WeakDeps.deps_asrc`: drop the `ORload` mask (or add
  `deps_asrc_ld`); (ii) WeakEvInst.v:314: `[]` ↦ `deps_asrc
  (deps_of_ib (ib_bits ib))`; (iii) the language arm's σ-effect:
  `load_post_run` ↦ a `_d` variant taking `srcs_view ws0 (deps_asrc
  (edeps σ c))` as the exclusive read does, then `WeakEvLift` (:1426,
  :1951) and the `[]`-shaped lemmas above; (iv) accept that the
  instruction's PTW reads get `rs1` (and `satp` via `DTctx`) too —
  that IS the design's row-level D-8 lifting ("every `MemRead` of an
  instruction depends on its decoded address registers and on
  `satp`"), a strengthening the design adopts knowingly.
- ~~MEANWHILE the fold below recovers the general rule 13 WITHOUT the
  unmasking through F5': a load's result write is `LRegW rd (DLdRes ::
  addr-srcs)` (`WeakDeps.deps_rd`'s `ORload` arm; `DLdRes` appears in
  no other role's `rd` sources), so at an `LRegW` naming `DLdRes` the
  `DReg` entries are the load's address sources and feed `dt_adr`
  (`row_deps_t_r13_masked`).~~ **THIS WAS UNSOUND AND HAS BEEN REMOVED**:
  `DLdRes` appears in the emitted label's `erw_srcs` too — the DYNAMIC
  set of every carrier register the instruction read, which for AMO/SC
  includes the DATA register (rs2) — not only in the decoder's address
  role, so feeding `dt_adr` off any `LRegW` naming `DLdRes` adds a
  `[R];data;[AMO];po;[W]` ordering riscv.cat does not have. A load into
  `x0` has no `LRegW` and was missed by that route regardless (sound:
  fewer ppo edges); the label route (`row_deps_t_r13`) catches it once
  unmasked, honestly. Rule 9's load half (`DTaddr` into the load itself)
  needs the label too.
