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
| 1 | `2dfb4844` | The PTE A/D-bit update is an atomic read-check-write (exclusive re-read, re-check, conditional write). | **T5** spec-motivated strengthening (the owner's named exception, bump decision D3) | The privileged spec requires the A/D update to be atomic; upstream writes back the walk's copy with a plain write, which can resurrect a PTE another hart changed.  Sequential execution is unchanged except on the TLB-hit path when the PTE changed without an SFENCE.VMA.  Kept from before the bump (bump decision D3).  Known gap: the fresh PTE is re-checked but not compared with the value the walk used (the spec's step 7 compares and, on a mismatch, walks again), so if another hart installs a different valid leaf the access uses the walked translation while A/D are set on the new PTE; an open owner decision (section 6).  Depended on by `MachCSL.TsoMem`'s exclusive PTE kinds (`akPteRe`) and the page-walk leaves (`WpPtWalk`, `WpPtWalkOwn`).  The A/D accesses are exclusive only through their read/write kinds (`Read_RISCV_reserved`/`Write_RISCV_conditional`, which `MachCSL.TsoMem.akExcl` keys on), not under 0.16's `ak_is_exclusive` (`LoadReserved`/`StoreConditional`).  The commit also drops `pmaCheck`'s `assert(not(res_or_con))` for PTE accesses and adds two constant `termination_measure`s (inert in Lean; compiler commit `b72d7e842` emits none).  Audit note (2026-10-20): MachCSL's memory never fails a conditional write (`MachCSL/Lang.lean`'s header, delta 2), so the commit's `Ok(false)` arm -- an `internal_error` ("PTE conditional write failed"), i.e. a STUCK hart, not a retry -- is dead here, and the update's atomicity rests on `TsoMem`'s reservation blocking; the step-7 compare of the later lane closes the walk-to-re-read window only -- hardware's "the conditional write fails, walk again" behaviour is absent by construction (the language's delta 2, and upstream's own `write_ram`, which answers `true` for every `Ok` of `sail_mem_write` and `false` only for an abort: section 5), a pre-bump restriction, not the fork's.  If that lane lets a PTE conditional write fail, the fork's arm must become a re-walk, not the `internal_error`. |
| 2 | `3fdb4bca` | `external_interrupts_pending` reads the pin registers `sig_meip`/`sig_seip` (and, under H, `sig_hgeip`) whether or not the Simple Interrupt Generator is configured. | **T2** platform integration | Platform fidelity: the validated platforms' external interrupts come from a PLIC that drives the pins, and upstream has no knob for that (the SIG is its only external-interrupt source and the pin registers are private; relocating the SIG's window would avoid the collision but model a device no platform has).  Since upstream #1899 the pins are ignored without the SIG, and the SIG's MMIO window collides with xv6's PLIC base, so it is off (configuration deviation 1).  Restores the pre-#1899 behaviour for a platform that drives the pins itself (bump decision D6). |
| 3 | `69ed097e` | `MemoryTriggerPayload` carries its value zero-extended to 16 bytes plus its width, instead of an existentially width-indexed vector. | **T3** representation | The Lean backend cannot represent an existentially typed union constructor (the generated model did not elaborate).  `compare_value` computes what it computed before; trigger matching is unchanged.  Sdtrig is disabled in this configuration anyway. |
| 4 | `9da94b63` | The Zaamo after-trigger tests the result with a pattern (`Retire_Success()`) instead of `==`. | **T3** representation | `ExecutionResult` has no equality in the theorem-prover backends.  Identical behaviour. |
| 5 | `d2cb43fc` | `postlude` no longer requires `FD_instructions`; `transformed_instruction` drops its `LOAD_FP`/`STORE_FP` arms. | **T1** module selection (a `requires` edit), plus a code edit (the two dropped arms) that T1 does not cover: unreachable here twice over (`transformed_instruction` runs only under `currentlyEnabled Ext_H`; without `FD_instructions` the `LOAD_FP`/`STORE_FP` constructors do not exist, which is why the edit was needed); behaviour-changing in a configuration with H and the F/D instructions (mtinst/htinst get 0), hence local, not an upstream candidate | 0.16's postlude requires the F/D instructions (for the H extension's transformed FP loads/stores in mtinst/htinst), which compiles the whole F/D family, and with it the softfloat externs, into the model whatever `model/sail-modules.txt` selects.  Before the bump the F/D instructions were not in the model; the module subset (section 4), the hook policy (section 5: the softfloat externs stay unrealised) and the audit (no audited theorem may reach them) all assume so.  With H disabled the dropped arms are unreachable.  Accepted 2026-10-19. |
| 6 | `f0ef9813` | `getPendingSet` ignores `hideleg` when H is not enabled, as it already ignores `mideleg` when S is not. | **T4** bug fix (precedents: `mideleg` ignored without S, `hedeleg` without H; upstream's own Lean emulator notes that H's registers are read without H: `lean_emulator/LeanRiscv.lean:249-264`, "registers read during reset and interrupt polling even when executing in Machine mode", with `hideleg` initialised to `undefined_Minterrupts ()`) | Without H no write reaches `hideleg` (its legaliser lets only the VS bits be set) and nothing resets it, so only an unspecified power-on value can set its S bits, which would route a delegated supervisor interrupt to VS, where a hart without H never takes it.  Approved 2026-10-19. |

Commits 1-5 are pushed; commit 6 awaits the owner's push (a fresh clone cannot check it out until
then).

## 2. The compiler fork: `dongjaelee1/sail`, branch `xv6`

Named in `tools/regen_sail_model.sh`'s header (merge `b49c997e`; the merge with commit `b72d7e842`
awaits the owner's push).

| Commit | Change | Kind |
|---|---|---|
| `518f0df34` (cherry-pick of zeldovich `3c03fced`, upstream PR #1750) | Boolean `&`/`|` short-circuit when an operand has effects. | Backend bug fix: without it the generated Lean always runs an effectful right operand, which changes the model's semantics.  The rewrite lives in the shared `src/lib/rewrites.ml` but is enabled only in the Lean plugin's `lean_rewrites`: backend-only in effect. |
| `2331f11e6` (cherry-pick of zeldovich `4b46310d`, upstream PR #1774) | Non-atomic operands of type-level arithmetic are parenthesised. | Backend bug fix: without it `flen` prints as 8 bits. |
| `ad1ada173` (ours) | Lean command keywords (`prefix`, `infix`, ...) are escaped in identifiers. | Names only: the generated `DeviceTree` did not elaborate. |
| `b72d7e842` (ours) | `termination_by` is emitted only on a standalone definition that calls itself. | No semantic change: the dropped measures were unused (Lean warned). |

## 3. Post-generation patches (`tools/regen_sail_model.sh`)

Each is conditional and reports itself in the regeneration log.
- **A.** `(pure (print_ ...))` becomes `discard <| pure (print_ ...)`: the same meaning, avoiding
  a Lean elaboration-time blow-up.
- **B.** The single-line widths `if (64 = 32 : Bool) then a else b` are folded to `b` (xlen is 64).
  The line-wrapped forms in type signatures (`BitVec (if ( 64` / `= 32 : Bool) then 7 else 14)`) are
  left as they are: fourteen at this regeneration -- eight in `Vmem.lean`, five in `VmemTlb.lean`,
  one in `Callbacks0.lean` -- counted by a two-line pattern (a line ending in `( 64` followed by one
  starting with `= 32`), which the script's single-line count does not see; type-level, reduced by
  Lean, harmless.  (Two earlier counts, "two" and "three", were wrong.)
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
  decode as illegal; the kernel uses none of them (it never enables FS).  Tier T1: the platforms
  advertise F and D, so does `misa`; an FP instruction with `FS` on decodes as illegal here where
  the hardware would execute it -- invisible to xv6, and a recorded residual of the module subset.
  Zkr is the exception to "decodes as illegal": `is_CSR_accessible` consults `currentlyEnabled Ext_Zkr`
  for `mseccfg`/`mseccfgh` (0x747/0x757) once the privileged ISA is 1.12 or later, that clause lives
  in the uncompiled Zkr module, and the scattered function's default arm is `sail_assert false`, so
  an M-mode `csrr mseccfg` is a STUCK hart, not an illegal instruction (S- and U-mode reads fail the
  privilege check first: `MachCSL/UExecCsrTab.lean`).  Pre-existing (the Rocq tree's finding 32; its
  finding 22 is the opposite row, the CSRs the model implements that QEMU refuses),
  witnessed by `core_csrwide` on QEMU and CVA6 -- the one "stuck" run in each green set -- and off
  every kernel path (xv6's M-mode code never reads it).  `Zkr.supported := false` would not remove
  it (`hartSupports` is not consulted first); compiling Zkr would put the unrealised
  `get_16_random_bits` into every CSR-read cone.  Recorded as a residual (owner, 2026-10-20).  The
  rest of the crypto family and Zfh stay at upstream's defaults: not `misa`-visible, and no capture
  witnesses which of them the platforms have.
- **The configuration**, `model/sail-config-rv64d.json`: upstream's `config.json.in` resolved for
  rv64d, with the deviations listed in its header (items 1-7) and marked "xv6iris" inline
  (restored on review: item 7, the misaligned-AMO fault, had been dropped by the first refresh).
  Tiers (the policy's T0): items 1 and 4 are platform choices (reason (a)); item 2 is (a) in two
  parts: V off is what all three platforms report (`core_csrvals` slot 1, the `misa` low word:
  QEMU 0x001411AD, JH7110 0x0094112F, CVA6 0x0014112F; `core_regs_mcsr` does not publish `misa`,
  and MXL is the board line's, not a capture's), while B is a platform DISAGREEMENT -- the JH7110
  and CVA6 report B (and the JH7110 its vendor X), QEMU virt does not (Rocq finding 29 for the
  JH7110; the CVA6 `core_csrvals` capture for CVA6) -- resolved
  toward QEMU by the owner's ruling of 2026-10-20 under T0(a)'s disagreement rule: the kernel never
  uses B, and B on means regrowing the complete U-mode decode image (`MachCSL/UDecode.lean` pins
  `misa`; the Rocq-era measurement is in `claude-notes/completed/crash.md`), the boards'
  `core_csrvals` runs being its recorded finding (a record fix earlier the same day had claimed
  every platform reports `misa` without B: false, corrected);
  item 3 is (a) by the same rule: H off follows the boards (QEMU virt alone reports H: findings
  19/29; the kernel never enters a virtual privilege or touches an H CSR, and H on would add the
  HLV/HSV/HFENCE families to the U-mode decode image, two-stage translation to every walk leaf and
  the H CSRs to the power-on obligations), and Sdtrig off follows CVA6 -- `core_csrprobe`'s
  scoreboard slot 35 (`csrr tselect`) records a trap on CVA6 and none on QEMU or the JH7110 -- with
  QEMU/CoreCsrprobe the recorded finding; the kernel never touches a trigger CSR, and the cost of
  Sdtrig on is estimated, not measured (trigger checks on every fetch, load, store and AMO leaf, the
  trigger file in the power-on obligations); items 5 and 6 are forced by
  `config_is_valid` once H and Sdtrig are off; item 7 is continuity (b): `MachCSL/UMemAmo.lean`'s
  rules state the pre-0.13 cause (a store/AMO access fault), which the spec permits; no capture
  exercises a misaligned AMO, so the platforms' cause is unwitnessed (an `amo_misaligned` capture
  would let (a) decide it).  Corrected 2026-10-20 on the audit: this entry had said Sdtrig is a
  feature every validated platform has.  A deviation 8 (F and D off, 2026-10-19) was withdrawn on
  2026-10-20: it turned three green device-conformance runs red, because every validated platform
  has F and D and `misa` had come to read a value no platform reports; F and D are advertised
  again, their instructions still uncompiled (section 4's first bullet).  Device conformance: item 3's
  Sdtrig part turns one vtest run red (QEMU `core_csrprobe`'s `tselect`), recorded as a finding in
  `notes/device-conformance.md` ("The 0.16 bump"); under upstream's default it would agree.

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
  And upstream's own `write_ram` answers `true` for every `Ok` of `sail_mem_write` (lean-sail's
  `Option Bool` result is discarded, and is always `none`: v7's `sail_mem_write` answers `.Ok none`
  or `.Err abort`, so the interface has no conditional-write result at all) and `false` only for an
  abort, so in this model a conditional
  write "fails" only as an abort -- the language's delta 2 and the model agree, and fork commit 1's
  `Ok(false)` arm is unreachable from both sides.
- **The language** (`MachCSL/Lang.lean`'s header): how the semantics consumes the model's events.
- **The language's restrictions** (audit, 2026-10-20; `MachCSL/Lang.lean`'s header): delta 2 -- a
  conditional write never fails -- removes spurious SC failures (compensated for LR/SC by the opaque
  reservation predicates) and the failure arm of fork commit 1's A/D update (not compensated:
  section 1, row 1); delta 4's `undefined_*` failures and the `getCycleCount` answer 0 are dead
  here -- the 0.16 model calls neither (`get_cycle_count` has no caller in the generated code).

## 6. Open decisions

Decided by the owner 2026-10-19 (`notes/model-policy.md`, section 8); each item is planned work,
not an open question:

- Fork commit 1 does not compare the fresh PTE with the walked one (section 1, row 1): the
  recorded gap stays for now; a lane after the bump's leaves completes the update with the spec's
  step-7 comparison (a fork commit under T5).
- The driver's `exit_wait` is nondeterministic since 2026-10-19 (section 5); the WFI leaves cover
  the forced-exit arm as they are ported.
- Nothing is filed upstream; the project keeps its own fork.

Decided by the owner 2026-10-20, on the independent audit (`notes/model-policy.md`, section 8,
decisions (6)-(10)): Sdtrig stays off on the witnessed platform disagreement; item 7 stays; no
configuration change for the crypto/Zfh advertisements, the `csrr mseccfg` stuck path recorded
(section 4); the contract changes ratified; the green-set and check-ci rules adopted.  The step-7
lane (above) starts from section 1 row 1's audit note: the compare closes the walk-to-re-read window
only, and whether the language should admit a failed conditional write for PTE kinds is part of
that lane's question.

Decided by the owner 2026-10-20 (later), on a second independent audit (`notes/model-policy.md`,
section 8, (11)-(13)): B stays off as a platform disagreement resolved toward QEMU; T0(a) gains the
disagreement rule; the record fixes above.  For the step-7 lane: the fork's `Ok(false)` arm is an
`internal_error`, so letting a PTE conditional write fail needs a re-walk arm in the fork first.
- F and D were off in the configuration for one day (item 8, 2026-10-19) and are on again since
  2026-10-20 (section 4); Sdtrig stays off, its one device-conformance run a recorded finding.
