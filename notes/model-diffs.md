# How this tree's machine model differs from upstream

The machine model is upstream's Sail RISC-V model compiled to Lean; this note tracks EVERY place
where what the proofs are about differs from upstream, and why.  Keep it current: a fork commit, a
compiler patch, a post-generation patch, a module-list or configuration change, or a change to how
MachCSL runs the model goes here in the same commit.

**The rule (owner, 2026-10-19):** follow the model.  Fix it only where it is clearly a bug, and
record the fix here.  Nothing below has been reported upstream yet.

"Upstream" is:
- the model: [riscv/sail-riscv](https://github.com/riscv/sail-riscv) 0.16, `e5acebb0`;
- the compiler: [rems-project/sail](https://github.com/rems-project/sail) master `e4982101`;
- the Lean runtime: lean-sail v7 (`01bb54c7`), used unmodified.

To see the diffs themselves:

```sh
cd sail-riscv && git log --reverse --format='%h %s' e5acebb0..xv6 && git diff e5acebb0 xv6 -- model
cd /work/toolchain/src/sail-v2 && git log --no-merges --format='%h %an | %s' e4982101..xv6
```

## 1. The model fork: `dongjaelee1/sail-riscv`, branch `xv6`

Pinned by `SAIL_RISCV_REV` in `tools/regen_sail_model.sh`.

| # | Commit | Change | Kind | Why |
|---|---|---|---|---|
| 1 | `2dfb4844` | The PTE A/D-bit update is an atomic read-check-write (exclusive re-read, re-check, conditional write). | Spec conformance | The privileged spec requires the A/D update to be atomic; upstream writes back the walk's copy with a plain write, which can resurrect a PTE another hart changed.  Sequential execution is unchanged except on the TLB-hit path when the PTE changed without an SFENCE.VMA.  Kept from before the bump (decision D3). |
| 2 | `3fdb4bca` | `external_interrupts_pending` reads the pin registers `sig_meip`/`sig_seip` whether or not the Simple Interrupt Generator is configured. | Platform integration | Since upstream #1899 the pins are ignored without the SIG, and the SIG's MMIO window collides with xv6's PLIC base, so it is off (configuration deviation 1).  Restores the pre-#1899 behaviour for a platform that drives the pins itself (decision D6). |
| 3 | `69ed097e` | `MemoryTriggerPayload` carries its value zero-extended to 16 bytes plus its width, instead of an existentially width-indexed vector. | Representation | The Lean backend cannot represent an existentially typed union constructor (the generated model did not elaborate).  `compare_value` computes what it computed before; trigger matching is unchanged.  Sdtrig is disabled in this configuration anyway. |
| 4 | `9da94b63` | The Zaamo after-trigger tests the result with a pattern (`Retire_Success()`) instead of `==`. | Representation | `ExecutionResult` has no equality in the theorem-prover backends.  Identical behaviour. |
| 5 | `d2cb43fc` | `postlude` no longer requires `FD_instructions`; `transformed_instruction` drops its `LOAD_FP`/`STORE_FP` arms. | Module selection | 0.16's postlude requires the F/D instructions (for the H extension's transformed FP loads/stores in mtinst/htinst), which compiles the whole F/D family, and with it the softfloat externs, into the model whatever `model/sail-modules.txt` selects.  Before the bump the F/D instructions were not in the model; the module subset (section 4), the hook policy (section 5: the softfloat externs stay unrealised) and the audit (no audited theorem may reach them) all assume so.  With H disabled the dropped arms are unreachable.  Accepted 2026-10-19. |
| 6 | `f0ef9813` | `getPendingSet` ignores `hideleg` when H is not enabled, as it already ignores `mideleg` when S is not. | Bug fix | Without H no write reaches `hideleg` (its legaliser lets only the VS bits be set) and nothing resets it, so only an unspecified power-on value can set its S bits, which would route a delegated supervisor interrupt to VS, where a hart without H never takes it.  Approved 2026-10-19. |

Commits 1-5 are pushed; 6 is pending (`local-plan/model-bump/HOST.md`).  The patch files are also
kept in `local-plan/model-bump/patches/`.

## 2. The compiler fork: `dongjaelee1/sail`, branch `xv6`

Named in `tools/regen_sail_model.sh`'s header (merge `b49c997e`).

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
  instructions with the selected `H` group).
- **The configuration**, `model/sail-config-rv64d.json`: upstream's `config.json.in` resolved for
  rv64d, with the deviations listed in its header (items 1-6) and marked "xv6iris" inline.

## 5. Where MachCSL's semantics meets the model

- **Power-on** (`MachCSL/ArchReset.lean`): every register starts with an arbitrary value, then
  the board's short list of obligations, then the model's own `init_model` (configuration assert
  and `reset`), then the firmware step.  The model's own register initialisers (`sail_model_init`)
  are deliberately NOT run; that file's header gives the reason (they would pin ISA-unspecified
  registers to simulator values).  A register joins the board list only if some consumed fact does
  not follow from `init_model` over an arbitrary file.  The 0.16 bump added one:
  `written_trigger_index = none` (the model's own Sdtrig bookkeeping, no hardware counterpart, Sail
  initial value `None()`; with Sdtrig disabled nothing writes it, and every cycle's end asserts
  it is none; decided 2026-10-19).
- **Platform hooks** (`model/Lean_RV64D/LeanRV64D/Xv6Extras.lean`): realised exactly where the
  hook has no effect on modelled state; the reservation predicates are opaque parameters; the
  hooks whose results are consumed (`plat_term_read`, `get_16_random_bits`, the softfloat family)
  are deliberately left unrealised, and the audit (`tools/audit`) fails if an audited theorem
  reaches one.
- **The language** (`MachCSL/Lang.lean`'s header): how the semantics consumes the model's events.

## 6. Open decisions

None (2026-10-19).
