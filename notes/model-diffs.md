# How this tree's machine model differs from upstream

The machine model is upstream's Sail RISC-V model compiled to Lean; this note tracks EVERY place
where what the proofs are about differs from upstream, and why.  Keep it current: a fork commit, a
compiler patch, a post-generation patch, a module-list or configuration change, or a change to how
MachCSL runs the model goes here in the same commit.

**The rule (owner, 2026-10-19):** follow the model.  Fix it only where it is clearly a bug, and
record the fix here.  The tiers a deviation may fall in, and what each requires, are in
`notes/model-policy.md` (section 4).  Upstream status: the A/D update is upstream PR #1860 (open,
deferred by the maintainers) and the two cherry-picked compiler fixes are PRs #1750 and #1774
(open, by their original authors); this project files nothing (owner, 2026-10-19: it keeps its own
fork; the upstream status of every row is "owner decided not to file").

"Upstream" is:
- the model: [riscv/sail-riscv](https://github.com/riscv/sail-riscv) 0.16, `e5acebb0`;
- the compiler: [rems-project/sail](https://github.com/rems-project/sail) `sail2` (its development
  branch; `master` is a 2019 remnant) `e4982101`;
- the Lean runtime: lean-sail v7 (`01bb54c7`), used unmodified.

To see the diffs themselves:

```sh
cd sail-riscv && git log --reverse --format='%h %s' e5acebb0..xv6 && git diff e5acebb0 xv6 -- model
cd /work/toolchain/src/sail-v2 && git log --no-merges --format='%h %an | %s' e4982101..xv6
```

## 1. The model fork: `dongjaelee1/sail-riscv`, branch `xv6`

Pinned by `SAIL_RISCV_REV` in `tools/regen_sail_model.sh`.

| # | Commit | Change | Tier (`notes/model-policy.md` §4) | Why |
|---|---|---|---|---|
| 1 | `2dfb4844` | The PTE A/D-bit update is an atomic read-check-write (exclusive re-read, re-check, conditional write). | **T5** spec-motivated strengthening (the owner's named exception, bump decision D3) | The privileged spec requires the A/D update to be atomic; upstream writes back the walk's copy with a plain write, which can resurrect a PTE another hart changed.  Sequential execution is unchanged except on the TLB-hit path when the PTE changed without an SFENCE.VMA.  Kept from before the bump (bump decision D3).  Known gap: the fresh PTE is re-checked but not compared with the value the walk used (the spec's step 7 compares and, on a mismatch, walks again), so if another hart installs a different valid leaf the access uses the walked translation while A/D are set on the new PTE; an open owner decision (section 6).  Depended on by `MachCSL.TsoMem`'s exclusive PTE kinds (`akPteRe`) and the page-walk leaves (`WpPtWalk`, `WpPtWalkOwn`).  The A/D accesses are exclusive only through their read/write kinds (`Read_RISCV_reserved`/`Write_RISCV_conditional`, which `MachCSL.TsoMem.akExcl` keys on), not under 0.16's `ak_is_exclusive` (`LoadReserved`/`StoreConditional`).  The commit also drops `pmaCheck`'s `assert(not(res_or_con))` for PTE accesses and adds two constant `termination_measure`s (inert in Lean; compiler commit `b72d7e842` emits none). |
| 2 | `3fdb4bca` | `external_interrupts_pending` reads the pin registers `sig_meip`/`sig_seip` whether or not the Simple Interrupt Generator is configured. | **T2** platform integration | Upstream has no knob for it: the SIG is its only external-interrupt source and the pin registers are private.  Since upstream #1899 the pins are ignored without the SIG, and the SIG's MMIO window collides with xv6's PLIC base, so it is off (configuration deviation 1).  Restores the pre-#1899 behaviour for a platform that drives the pins itself (bump decision D6). |
| 3 | `69ed097e` | `MemoryTriggerPayload` carries its value zero-extended to 16 bytes plus its width, instead of an existentially width-indexed vector. | **T3** representation | The Lean backend cannot represent an existentially typed union constructor (the generated model did not elaborate).  `compare_value` computes what it computed before; trigger matching is unchanged.  Sdtrig is disabled in this configuration anyway. |
| 4 | `9da94b63` | The Zaamo after-trigger tests the result with a pattern (`Retire_Success()`) instead of `==`. | **T3** representation | `ExecutionResult` has no equality in the theorem-prover backends.  Identical behaviour. |
| 5 | `d2cb43fc` | `postlude` no longer requires `FD_instructions`; `transformed_instruction` drops its `LOAD_FP`/`STORE_FP` arms. | **T1** module selection (a `requires` edit) | 0.16's postlude requires the F/D instructions (for the H extension's transformed FP loads/stores in mtinst/htinst), which compiles the whole F/D family, and with it the softfloat externs, into the model whatever `model/sail-modules.txt` selects.  Before the bump the F/D instructions were not in the model; the module subset (section 4), the hook policy (section 5: the softfloat externs stay unrealised) and the audit (no audited theorem may reach them) all assume so.  With H disabled the dropped arms are unreachable.  Accepted 2026-10-19. |
| 6 | `f0ef9813` | `getPendingSet` ignores `hideleg` when H is not enabled, as it already ignores `mideleg` when S is not. | **T4** bug fix (precedents: `mideleg` ignored without S, `hedeleg` without H; upstream's own Lean emulator notes that H's registers are read without H) | Without H no write reaches `hideleg` (its legaliser lets only the VS bits be set) and nothing resets it, so only an unspecified power-on value can set its S bits, which would route a delegated supervisor interrupt to VS, where a hart without H never takes it.  Approved 2026-10-19. |

Commits 1-5 are pushed; commit 6 awaits the owner's push (a fresh clone cannot check it out until
then).

## 2. The compiler fork: `dongjaelee1/sail`, branch `xv6`

Named in `tools/regen_sail_model.sh`'s header (merge `b49c997e`; the merge with commit `b72d7e842`
awaits the owner's push).

| Commit | Change | Kind |
|---|---|---|
| `518f0df34` (zeldovich, upstream PR #1750) | Boolean `&`/`|` short-circuit when an operand has effects. | Backend bug fix: without it the generated Lean always runs an effectful right operand, which changes the model's semantics. |
| `2331f11e6` (zeldovich, upstream PR #1774) | Non-atomic operands of type-level arithmetic are parenthesised. | Backend bug fix: without it `flen` prints as 8 bits. |
| `ad1ada173` (ours) | Lean command keywords (`prefix`, `infix`, ...) are escaped in identifiers. | Names only: the generated `DeviceTree` did not elaborate. |
| `b72d7e842` (ours) | `termination_by` is emitted only on a standalone definition that calls itself. | No semantic change: the dropped measures were unused (Lean warned). |

## 3. Post-generation patches (`tools/regen_sail_model.sh`)

Each is conditional and reports itself in the regeneration log.
- **A.** `(pure (print_ ...))` becomes `discard <| pure (print_ ...)`: the same meaning, avoiding
  a Lean elaboration-time blow-up.
- **B.** The widths `if (64 = 32 : Bool) then a else b` are folded to `b` (xlen is 64).
- **C.** None needed: Sail now emits `sail_assert`.

## 4. What is compiled and how it is configured

- **The module subset**, `model/sail-modules.txt`.  Upstream 0.16 builds `--all-modules` by
  default; this tree keeps its own selection (the pre-bump one, plus Sdtrig, which `sys` requires).
  Not in the selection: the F/D instruction family (`FD_instructions`, see fork commit 5), the vector
  instructions (`V_instructions`, the `Zv*` extensions), scalar crypto (`Zbkb`, `Zbkx`, `Zkn`,
  `Zkr`, `Zks`), `bfloat16_core`/`Zfbfmin`, `Zibi`, `Zilx`, and the non-model modules (`main`,
  `rmem`, `unit_tests`).  Some unselected leaves arrive anyway through `requires` (e.g. H's
  instructions with the selected `H` group).  Pre-existing and worth knowing: `misa` advertises F
  and D (and the configuration Zfh and scalar crypto) whose instructions are not compiled, so they
  decode as illegal; the kernel uses none of them (it never enables FS).  Tier T1.  Since
  configuration item 8, `misa` no longer advertises F and D; the remaining advertised-but-uncompiled
  extensions are the configuration's scalar-crypto ones.
- **The configuration**, `model/sail-config-rv64d.json`: upstream's `config.json.in` resolved for
  rv64d, with the deviations listed in its header (items 1-8) and marked "xv6iris" inline
  (restored on review: item 7, the misaligned-AMO fault, had been dropped by the first refresh).
  Tiers (the policy's T0): items 1, 2, 4 and 8 are platform and ISA-profile choices (reason (a));
  3, 5 and 6 are forced by `config_is_valid` once H and Sdtrig are off (a); item 7 is continuity
  (b): the user tier's misaligned-AMO arms depend on the pre-0.13 behaviour, which the spec
  permits.  Item 8 (owner decision 2026-10-19): F off -- D with it, since the model derives D's
  support from F's -- and the F-dependent Zfa, Zfbfmin, Zfh, Zfhmin, Zcd off: the kernel never
  enables `mstatus.FS` and the module subset compiles none of their instructions, so `misa` now
  advertises what is compiled (the derived `misa` value changed accordingly; `mstatus.FS` is
  read-only zero; the floating-point CSRs are illegal).

## 5. Where MachCSL's semantics meets the model

- **Power-on** (`MachCSL/ArchReset.lean`): every register starts with an arbitrary value, then
  the board's short list of obligations, then the model's own `init_model` (configuration assert
  and `reset`), then the firmware step.  The model's own register initialisers (`sail_model_init`)
  are deliberately NOT run; that file's header gives the reason (they would pin ISA-unspecified
  registers to simulator values).  A register joins the board list only if some consumed fact does
  not follow from `init_model` over an arbitrary file.  The 0.16 bump added one:
  `written_trigger_index = none` (the model's own Sdtrig bookkeeping, no hardware counterpart, Sail
  initial value `None()`; with Sdtrig disabled nothing writes it, and every cycle's end asserts
  it is none; decided 2026-10-19).  In the policy's terms (section 5 there) a model-bookkeeping
  board line: upstream's own code relies on the declared `None()`.
- **The driver** (`MachCSL.riscvStep`): before the bump `try_step 0 false` plus a
  nondeterministic tick.  Upstream runs two schedules of its own: the Sail `loop` (and its Lean
  emulator) passes `exit_wait = true` at every step, and its C++ harness waits a bounded number of
  ticks (`platform.max_time_to_wait`) and then passes `true`.  `exit_wait = false` means a hart in
  WFI waited for an interrupt and never took the model's forced WFI exit (fewer behaviours than
  upstream's drivers).  Since 2026-10-19 (owner decision) the driver is `try_step 0 ew` with `ew`
  chosen nondeterministically like the tick, so the theorems cover every schedule: a waiting hart
  may be left waiting or forced out in any cycle (`notes/model-policy.md`, section 5).
- **Platform hooks** (`model/Xv6Extras.lean`, installed as `model/Lean_RV64D/LeanRV64D/Xv6Extras.lean`): realised exactly where the
  hook has no effect on modelled state; the reservation predicates are opaque parameters; the
  hooks whose results are consumed (`plat_term_read`, `get_16_random_bits`, the softfloat family)
  are deliberately left unrealised, and the audit (`tools/audit`) fails if an audited theorem
  reaches one.
- **lean-sail's rendering of Sail constructs** (interface facts the theorems inherit; none is on
  a kernel path): `undefined_int`/`undefined_nat`/`undefined_string` fail (a stuck hart) where V1
  chose a value; `undefined_range lo hi` chooses in `[lo, hi)` although Sail's `range` includes
  `hi`, and has no answer when `lo = hi`; `exit` and a failed `sail_assert` are not caught by a
  Sail `try` (only user exceptions are); `print_*` are no-ops; a register without an initialiser
  is first read from the environment (MachCSL's state), since the model's initialisers are not run.
- **The language** (`MachCSL/Lang.lean`'s header): how the semantics consumes the model's events.

## 6. Open decisions

Decided by the owner 2026-10-19 (`notes/model-policy.md`, section 8); each item is planned work,
not an open question:

- Fork commit 1 does not compare the fresh PTE with the walked one (section 1, row 1): the
  recorded gap stays for now; a lane after the bump's leaves completes the update with the spec's
  step-7 comparison (a fork commit under T5).
- The driver's `exit_wait` is nondeterministic since 2026-10-19 (section 5); the WFI leaves cover
  the forced-exit arm as they are ported.
- Nothing is filed upstream; the project keeps its own fork.
- F and D are off in the configuration since 2026-10-19 (item 8, section 4).
