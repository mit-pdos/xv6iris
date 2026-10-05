# The model is generated with `-D SYMBOLIC` (2026-10-05)

Owner decision (notes/weak-port-architecture.md §B, "Owner decisions"): the Lean
model is regenerated with Sail's `-D SYMBOLIC` flag, as the Rocq weak line did on
2026-08-17, at the SAME sail-riscv pin (`070832a1`) and the same patched sail
(`5745ea9e` + the short-circuit cherry-pick).

## Why

Without the flag, `sail_instr_announce` / `sail_branch_announce` are pure no-op
stubs (`let _ : Unit := …`), so the event stream has no node carrying the
fetched opcode.  The weak tier needs one: Rocq `WeakEvInst` BANKS THE ANNOUNCED
BITS (`wgib`) and emits the second `LInstr` at that node (the reset that keeps
the fetch's own read view out of `w_ldv`), and `WeakDeps.deps_of_bits` decodes
the RVWMO operand roles from them.  The branch announcement is label-free in
Rocq-weak (the `LCtrl` label is emitted at the `nextPC` write) and is carried
along only because the flag brings it.

## What moved

**Model diff** (`model/Lean_RV64D`, ignoring the renumbered `k_exNNN_` binder
names, which also appear in a few signatures but are never referenced):

- `Step.lean` (`run_hart_active`, both fetch arms): `let _ : Unit :=
  sail_instr_announce h` → the monadic `(instr_announce h)`.
- `PcAccess.lean` (`set_next_pc`): `let _ := sail_branch_announce xlen pc` →
  `(branch_announce xlen pc)`.
- `Common0.lean`: the no-op stubs (`sail_*_announce`, `sail_reset_registers`,
  `sail_synchronize_registers`, `sail_mark_register(_pair)`, `__monomorphize*`)
  are gone (they are externs now); `sail_ignore_write_to` / `sail_pick_dependency`
  call the extern `mark_register`.
- `Defs.lean`: `Register` gains `__monomorphize_writes` / `__monomorphize_reads`
  (`Bool`), 180 → 182 constructors; `Inhabited RegisterRef` defaults to the new one.
- `ReadWriteV1.lean`: the two `def __monomorphize_* : Bool := false` are gone;
  `LeanRV64D.lean` (`sail_model_init`) writes both registers `false` first.
- Import lists: `Step`/`PcAccess` no longer import `Common0`; `LeanRV64D`
  imports `ReadWriteV1`.

Nothing else (no other function body changed).  Implied by the flag and not
needed: `reset_registers`, `synchronize_registers`, `mark_register_pair`,
`monomorphize` are declared as externs but never called by the riscv sources.

**Support:**

- `vendor/lean-sail` `Outcome`: `instrAnnounce (n) (w : BitVec n)`,
  `branchAnnounce (n) (pc : BitVec n)`, `ret = Unit`; emitters
  `PreSail.instr_announce` / `branch_announce`; the sequential interpreter
  ignores them.
- `model/Xv6Extras.lean`: the backend spells the externs by their names and
  lean-sail does not specialise them, so `instr_announce` / `branch_announce`
  (abbrevs onto the emitters) and the no-op `mark_register` are defined here
  (Rocq: `tools/riscv_extras_symbolic.v`).
- `MachCSL`: silent `evStep` arms (`σ' = σ`); `blockedStep` false and
  `hartObs` silent by computation; `swp_instr_announce` / `swp_branch_announce`
  (Wp); `swp_step` dispatch, `stepableHeads` and the unfold denylist (Tactics);
  skip arms in every walker (`bootRun` + `bootFin_*Announce` + `boot_peel`,
  `runRead`, `runReadP` + `udecode`, `runRW` + `urw_*Announce` +
  `runRW_*_announce_bind`, `uwk_run`) and in `vtest-lean`'s two interpreters.
  `allRegs` is 182 long.
- SC proofs: `UCycleDefs.ucAfterFetch` gains the announce (its equation with
  `run_hart_active` one more `congr`); `UCycle.uc_afterFetch_{base,rvc}` simp
  past it.  Everything stepping `set_next_pc` / the fetch through `swp_run`
  needed no edit.
