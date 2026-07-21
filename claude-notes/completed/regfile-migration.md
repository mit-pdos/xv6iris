# Register file: gmap → function migration

**Goal.** Replace the register-map representation `gmap regidx (mword 64)` with a
total function `regfile := regidx → mword 64` (RegFile.v). Motivation and
evidence: see the top bullets of [`../optimization.md`](../optimization.md) — the
5–7 s funnel `iApply`s in WpSconfWalk are ~67–80 % **register-map lookup peeling**
(`peel_reg` over a deep `<[Regidx k := v]>` gmap chain, each layer a full
ssreflect `rewrite lookup_total_insert{,_ne}`), not the proofmode (`pm_reduce`
is 2.5 %). A function rep resolves `M !!! Regidx j` in one `vm_compute` over the
concrete-key if-chain. **Measured: one funnel's 9 lookups over a 20-deep chain:
1.22 s (gmap peel) → 0.072 s (function rep), ~17×.** Uses funext (acceptable).

## Status: DONE — the whole tree is on `regfile`

The migration is complete: the only remaining mention of `gmap regidx (mword 64)`
in the tree is `RegFile.v` itself (the `rf_to_gmap` bridge and its comments). The
recipe and gotchas below are kept for reference — they apply to any new file that
touches the register map.

- **DONE — `RegFile.v`** (new base file, in `_CoqProject` after RiscvLang.v; builds).
  Defines `regfile`, `rf_upd`, `Insert`/`LookupTotal` instances (so `<[k:=v]> f`
  and `f !!! k` syntax is UNCHANGED), `upd_eq`/`upd_ne`/`upd_upd`, `Finite regidx`,
  the `rf_to_gmap` bridge + `rf_to_gmap_lookup`/`_dom`/`_upd`, and the `reg_lookup`
  tactic (the `peel_reg` replacement).
- **DONE — `WpGpr.v`** `gpr_file` ported to `regfile` (folds over `rf_to_gmap f`;
  `dom` conjunct kept — now trivially true — so `[%Hdom Hfmap]` destructuring
  survives). Added `gpr_file_lookup_acc` / `gpr_file_insert_acc` accessors.
- **DONE — `VcGen.v`** (the tricky boundary): `vregs_den` now returns `regfile`
  (`fun r => sval_den ρ (m !!! r)`, with `Inhabited sval`); `vregs_den_insert`
  and `vregs_den_init_agree` reproved via funext (dropped the now-vacuous
  `∀ r, r ∈ dom m` premise on the latter — callers no longer pass it).
- **DONE — wave 2** (16 files, ported by Sonnet subagents): `WpGprCsrr{A,B}`,
  `WpGprCsrw{A,B}`, `WpMmode{Addiw,Itype,Jal,Jalr,Load,Mret,Mul,Rtype,Shiftiop,
  Store,Utype}`, `WpSpinNew`.
- **Recurring subagent workaround:** where a leaf feeds `gpr_pt_value` the value
  `m !!! Regidx r`, pass `m (Regidx r)` (raw application) instead — the `!!!`
  notation races `LookupTotal` instance resolution against the accessor's
  application form; the two are definitionally equal so downstream closes fine.
  (Could be designed away by stating `gpr_file_lookup_acc` with `f !!! i`.)
- **DONE — the remaining ~65-file sweep**, driven by `make -k`: it rebuilt the
  non-port files and surfaced each next wave as compile errors. Waves went to
  parallel Sonnet subagents; `VcGenS` (gpr_matches + block lemmas) and the
  whole-function threading proofs (`WpSconfWalk`, `WpKvmmap`, `WpMappages`,
  user-mode) were done by hand.
- **Surviving local `peel_reg`s** (`WpSconfWalk.v`, `WpSconfMappages.v`) are NOT
  leftovers: they are re-defined post-migration to peel via the `upd_eq`/`upd_ne`
  LEMMAS, keeping values opaque. Use that variant instead of `reg_lookup` where
  the target is a symbolic HIT (e.g. `M !!! csp = spr` with `spr = add_vec sp0 …`)
  — `reg_lookup`'s `vm_compute` would try to reduce the `add_vec` and hang. Over
  the compact `rf_upd` spine it is still ~2.5× faster than the old gmap peel.

## CRITICAL: [rf_upd] TRANSPARENT + always discharge with [reg_lookup]

`rf_upd := fun j => if bool_decide (j=k) then v else f j` is TRANSPARENT. That is
what makes `reg_lookup := rewrite ?rf_lookup; vm_compute; reflexivity` a single
fast `vm_compute` (9 lookups over a 20-deep chain = **0.04 s** vs gmap peel 1.22 s,
~30x), and it is SAFE on symbolic register values — iota discards the unselected
`then`-branches, so a miss bottoms out at `base j` without ever reducing e.g.
`add_vec p …` (which would hang). (Tried and rejected: sealing `rf_upd` behind a
module — it forces `reg_lookup` to reveal the tower at tactic level, which costs
~as much as the gmap peel, i.e. no win; a `vm_compute`-first sealed variant is
fast but HANGS on symbolic `add_vec` values.)

The ONE hazard of transparency: a whole-function proof's **async `Qed`** re-reduces
the deep update-tower whenever a `callee_saved` conjunct was closed by bare
`reflexivity` / `repeat split` (kernel conversion over the tower ×14 conjuncts) —
pathological (~9 min / >1 GB on `WpSconfWakeup`). **Fix: discharge every such
conjunct / lookup side goal with `reg_lookup`, never `reflexivity`/`repeat split`.**
A `reg_lookup` proof term is a vm-cast the kernel re-checks cheaply.

Diagnosis gotcha that hid this: `coqc -time` does NOT count the async `Qed`
`rocqworker`, so it under-reports (14 s sentence-sum while wall was 9 min). It is
NOT machine contention — measure with `/usr/bin/time -v coqc …`, and reap any
orphan/zombie `rocqworker` (`ps -eo pid,ppid,stat,comm | grep rocqworker`) before
re-measuring (see durable-notes.md profiling).

Consequence for ports: several subagent ports DELETED `callee_saved` bullets
because `repeat split` auto-closed them by conversion (transparent) — those
compile but poison the `Qed`. Re-add an explicit `reg_lookup` discharge (e.g.
`... repeat split; ... ; all: reg_lookup`, or one `reg_lookup` per open conjunct).

## Per-file port recipe

1. `Require Import RegFile.` (once, near the RiscvLang import).
2. Type annotations: `gmap regidx (mword 64)` → `regfile` in every lemma
   statement / `Context` (mechanical; the `<[]>`/`!!!` bodies are unchanged
   thanks to the instances).
3. Register-map lookups in side-goals: `peel_reg` → **`reg_lookup`**. Delete each
   file's local `peel_reg`/`reg_neq` Ltac (now provided as `reg_lookup`). Inline
   `rewrite lookup_total_insert` → `upd_eq`; `lookup_total_insert_ne; [|reg_neq]`
   → `upd_ne` (its side goal is `j ≠ k`, dischargeable by `reg_neq`/`vm_compute`);
   `insert_insert` → `upd_upd`.
4. Leaves that destructure `gpr_file` (`iDestruct "Hfile" as "[%Hdom Hfmap]"` then
   `big_sepM_lookup_acc`/`big_sepM_insert_acc`): either keep using the raw
   `big_sepM_*` but derive the lookup fact with `rf_to_gmap_lookup f (Regidx r)`
   (instead of `apply lookup_lookup_total_dom; apply Hdom`) and bridge the output
   with `rewrite rf_to_gmap_upd`; OR switch to the ready-made
   `gpr_file_lookup_acc` / `gpr_file_insert_acc` (preferred — fewer moving parts).
5. Other register-map predicates fold the same way (`rf_to_gmap`): **`sie_cap`**
   (IntrDefs.v — depends on `m` only via `m !!! Regidx csp_rs1`, so `sie_cap_retarget`
   stays), **`callee_saved`** (CalleeSaved.v — pointwise register equalities,
   unchanged shape), **VcGen/VcGenS** register-map recovery. Port these Layer-1
   definition files before their consumers.

## Suggested dependency order

Layer 0 `RegFile` ✓ → Layer 1 defs (`WpGpr` ✓, `CalleeSaved`, `StackOwn`,
`IntrDefs` `sie_cap`, `VcGen`/`VcGenS`) → Layer 2 leaves (`WpSmodeGpr`, `WpMmode*`,
`WpSconfAlu`/`Mem`/`Btype`/`Ctl`/`Csr`, `WpGprCsr*`, …) → Layer 3 threading/funnels
(`WpSconfWalk`, `WpKvmmap`, `WpMappages`, `WpMemset*`, user-mode `User*`). Build
after each layer. `grep -rl "gmap regidx (mword 64)"` (84 files at start) tracks
the remaining set.

## Validation harness

Scratch benchmarks (in the session scratchpad, not committed): `reg_bench.v`
(gmap peel = 1.22 s), `reg_bench2.v` (function rep = 0.072 s), `reg_bench3.v`
(`reg_lookup` over a real 20-deep `set`-chain, <5 ms/lookup), `RegFileProto.v`
(the full core + gpr_file bridge, since promoted to RegFile.v/WpGpr.v).
