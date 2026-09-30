# MachCSL in Lean 4

A port of the MachCSL framework (Kaashoek & Zeldovich, *Extending concurrent
separation logic to the hardware level to verify the xv6 OS kernel on RISC-V
with AI agents*, `machcsl.pdf`) from Rocq to Lean 4, on top of
[iris-lean](https://github.com/leanprover-community/iris-lean) and the
[Sail RISC-V model](https://github.com/riscv/sail-riscv) compiled to Lean by
Sail's own Lean backend.  The Rocq prototype is
[mit-pdos/xv6iris](https://github.com/mit-pdos/xv6iris).

## Status

The Sail model runs as a free monad inside an Iris language, separation-logic
resources exist for registers and memory, and the machine-mode instruction
cycle is specified stage by stage (interrupt dispatch, fetch, decode, execute,
retire, clock tick).  On top of that, per-instruction rules about `wpLoop cpu`
(the paper's `wp CpuLoop`) exist for the instructions xv6's `_entry`,
`timerinit` and `start` use, and `Xv6/Proof*.lean` prove those functions
(linked: `_entry` reaches `main` in supervisor mode) by chaining those rules
-- no symbolic execution of the model occurs outside the framework's leaf
lemmas.  The supervisor-mode side has begun: the kernel execution context
`kctx` (`MachCSL/KCtx.lean`) and the first S-mode instruction rules over it
(`MachCSL/WpSmode.lean`, register-only instructions, interrupts off, Bare
translation).

## Layout

```
lakefile.toml, lean-toolchain     Lean 4 (v4.32.2) project; requires iris-lean,
                                  the vendored lean-sail and the generated model
vendor/lean-sail/                 lean-sail with a FREE-MONAD concurrency interface
                                  (see its README; upstream is an EStateM)
model/Lean_RV64D/                 the Sail RISC-V model compiled to Lean (GENERATED)
model/sail-config-rv64d.json      the model configuration (xv6 platform; same file
model/sail-modules.txt            as the Rocq prototype's model-xv6iris/)
tools/regen_sail_model.sh         regenerate model/Lean_RV64D from sail-riscv
tools/dump_kernel.py              xv6 kernel text -> Xv6/KernelImage.lean
tools/gen_model_facts.py          hartSupports facts -> MachCSL/ModelFacts.lean
tools/gen_platform.py             PMA/PMP reset values -> MachCSL/Platform.lean
tools/check_layering.sh           checks the Spec/Proof/Link import discipline
MachCSL/                          the framework (nothing xv6-specific)
  Lang.lean        the Iris language: state (per-hart register files + shared
                   byte memory, plus the era bookkeeping: generation, power
                   bit, boot image), expressions `hart gen cpu m` carrying the
                   in-flight Sail computation and the power thread `power`,
                   the per-EVENT step relation with the live/corpse gating and
                   the two observed power arms (PowerOff / PowerOn)
  Resources.lean   ghost state in two layers: the fixed layer (generation and
                   started counters, era registry) and per-era register ghost
                   maps (`r ↦ᵣ[cpu] v`) and byte-memory gen_heap (`a ↦ₘ b`);
                   `genCert`, the state interpretation (`powerInterp`)
  Wp.lean          `wpHart`/`wpLoop` (the paper's wp CpuLoop, under the
                   generation's certificate), the corpse rule `wp_dead`, the
                   era dispatch in `wpHart_lift`, `swp` (the paper's
                   wp Sail(m){Φ}) with the bind law, and one rule per event
                   kind (register read/write, memory read/write, silent, choice)
  Power.lean       the power thread: `wp_power` mints a fresh era at every
                   PowerOn and hands the boot client `powerBootRes`
  Tactics.lean     `sail_norm` / `swp_step` / `swp_run`: symbolic execution of
                   the model by head-normalising and applying the event rules
  ModelFacts.lean  (generated) configuration facts as a simp set
  Platform.lean    (generated) the platform's PMA regions and reset PMP state
  PlatformFacts.lean facts about addresses in RAM, alignment, CSR numbers, ...
  Boot.lean        `mBoot` (the machine-mode boot configuration), `pcIs`,
                   `clockCells`, `decodes32/16`
  WpPmp.lean       stage lemma: the PMP check with all entries off
  WpStages.lean    stage lemmas: interrupt dispatch, clock tick, RAM reads,
                   fetch (both alignments)
  WpGpr.lean       `gpr cpu i dq v` and the rules for `rX_bits`/`wX_bits`
  GprLit.lean      `gpr` at literal indices = the register cells
  Instr.lean       `instr pc is_rvc i`: the instruction at a program counter
                   (its read-only fetch footprint + decode fact, persistent)
  DecodeBridge.lean the concrete/symbolic decode bridge (the Rocq `goodb`):
                   `runRead` walks a read-only computation on a reference
                   register map, `swp_runRead` transports its result (proved
                   once by induction), `decodes32/16_bridge` close a decode
                   fact by kernel evaluation (`rfl`), ~30 ms per word
  WpCycle.lean     the cycle lemmas (one `riscvStep` = dispatch, fetch,
                   decode, execute, retire, optional tick), `fetchSpec`/
                   `execSpec`; `wpLoop_m_instr` over `instr`
  WpMmode.lean     per-instruction M-mode rules `wp_m_<instr>` (auipc, lui,
                   addi, add, mul, csrr mhartid, jal, ld), each covering the
                   compressed encoding too
  KCtx.lean        the kernel execution context (the Rocq `sie_cap_gpr`):
                   `KCtx` (register map, SIE index, stack reserve, push_off
                   depth, locks, translation tier, proc) and the resource
                   `kctx cpu k` = `kConf` (S-mode configuration cells at the
                   SIE index) ∗ the whole register file `gprFile` (with `tp`
                   pinned to the hart) ∗ `stackOwn` (trap reserve + avail)
                   ∗ translation slot ∗ interrupt arm ∗ per-cpu bookkeeping
                   ∗ context token; `wpNext` (the continuation may resume on
                   another hart once interrupts are on); file-level
                   register rules `swp_rX_file`/`swp_wX_file`
  WpAluFile.lean   execute stages of the register-only instructions over the
                   whole register file (`execSpecF_<instr>`): one proof per
                   instruction covers every operand pattern (`rd = rs1`,
                   `rs = x0`, ...)
  WpSmode.lean     the supervisor-mode cycle at the Bare tier (fetch through
                   the xv6 PMP, decode with `menvcfg` as `start` leaves it,
                   `wpLoop_s_instr`), `wpLoop_k_setReg` (the cycle over
                   `kctx`) and the S-mode rules `wp_s_<instr>` (addi, andi,
                   ori, xori, srli, slli, addiw, add, sub, and, or, xor, mul,
                   lui, auipc) whose continuation is a `wpNext`
  WpSmodeMem.lean  S-mode physical read/write stage lemmas (1 and 8 bytes)
                   and `execSpecF_lbu/ld/sb/sd` over the register file
  WpSmodeCtl.lean  `execSpecF_jal/j/ret`, the six conditional branches
                   (`bcond`), `subw`/`addw`
  WpSmodeRules.lean the `kctx` rules `wp_s_lbu/ld/sb/sd/branch/j/jal/ret/
                   subw/addw/push/pop` (one schema, `wpLoop_k_gen`)
  WordPointsTo.lean `wordPointsTo`: the points-to of an aligned word in RAM;
                   the cell a load/store rule takes, no side conditions
  CallConv.lean    `byteBuf` (a byte buffer as a list), `cstr` (the
                   points-to of a C string: terminated, no NUL inside, in
                   RAM), `calleeSaved`, the canonical body context `(k.pushed m).withRegs R` and the
                   reading of register chains on literal indices
  WpSmodeFrame.lean the standard two-slot frame as two derived rules
                   (`wp_prologue2`, `wp_epilogue2`) and the tactics
                   `k_step`/`k_norm` the function proofs use
Xv6/                              the xv6 verification (client of MachCSL)
  KernelImage.lean (generated) the kernel text as data, symbol addresses
  KernelTree.lean  (generated) the same text as an address-keyed search tree
  KernelText.lean  `kernelText`: the text section as persistent byte windows,
                   `kernelText_find`: any instruction the tree finds
  Image.lean       the read-only image (`kernelText ∗ kernelData`) as the
                   `KernelImage` instance `kctx` owns; `kctx_kernelText`/
                   `kctx_kernelData` take a copy out of the context
  CodeTactics.lean `text_instr`: an `instr` fact from `kernelText` by a tree
                   lookup and a decode walk, both evaluated by `rfl`
  SpecEntry.lean   the WP specification of `_entry` (`ENTRY`)
  ProofEntry.lean  its proof (instruction rules only)
  LinkEntry.lean   the proved interface clients import
  Geom.lean        where this kernel keeps `cpus[]` (the `KernelGeom`
                   instance `kctx` needs)
  Spec/Proof/Link{Strlen,Memcmp,Memmove,Memcpy}.lean
                   the four string functions, verified over `kctx`
```

### Spec / Proof / Link files

Every verified function `F` of the kernel follows the Rocq prototype's module
discipline: `Spec<F>.lean` states the contract once (a `wp_F_body` definition
and a `structure F_SPEC : Prop` interface), `Proof<F>.lean` proves it (taking
callees' interfaces as arguments, importing no other `Proof*` file),
`Link<F>.lean` instantiates it.  Code facts are not stated anywhere: a step
proves its `instr` premise from `kernelText` on the spot (`text_instr`).
`tools/check_layering.sh` checks the import rules.

### Verified S-mode functions

`strlen`, `memcmp`, `memmove` and `memcpy` (kernel/string.c) are proved
against whole-function contracts stated in the kernel execution context,
in the shape of the Rocq prototype's `wp_<f>_sconf_body`: the caller hands
over `kctx cpu k` (registers as the map `k.regs`, the arguments in
`a0..a2`), the kernel text, the clock, `pcIs` at the function, the byte
buffers (`byteBuf`, the source at the caller's fraction, a written
destination owned whole) and a `wpNext` continuation that receives the
context back at any register map `R'` with `calleeSaved k.regs R'`, the
result in `R' 10`, control at `jumpPc (k.regs 1)`, and the buffers.  The
proofs chain the `wp_s_*` rules through `k_step`; loops are lemmas by
induction on the remaining count (the loop body is one lemma, e.g.
`strlen_iter`); `memcpy`'s proof takes the `memmove` interface as a
parameter and is closed in `LinkMemcpy`.  Present hypotheses of every
contract: `k.sie = false` and `k.tier = .bare`.

The per-cpu and process layer (mirroring the Rocq `cpu_own`/`cur_proc`/
`proc_priv` vocabulary) is in `Xv6/ProcDefs.lean` (the `struct proc`
geometry, `procFields`/`procPriv`/`procPub`/`procDormant`/`procSlot`,
`curProc`) and `MachCSL/KCtx.lean` (`cpuCells`: `c->proc`, `c->noff`,
`c->intena` inside `kctx`).  On top of it `cpuid`, `mycpu`, `push_off`,
`pop_off` and `myproc` are verified (`Spec/Proof/Link{Cpuid,Mycpu,Pushoff,
Popoff,Myproc}.lean`): `myproc` returns the context's current proc
(`R' 10 = k.proc`), through `push_off`/`pop_off` (whose contracts move the
depth `noff` of the context, `KCtx.pushOff`/`KCtx.popOff`) and the inlined
`mycpu()`.  The S-mode CSR rules these need (`csrr sstatus`,
`csrrci sstatus, SIE`) are in `MachCSL/WpSmodeCsr.lean`, the per-cpu cell
rules (`wp_s_lw_noff`, `wp_s_sw_noff`, `wp_s_lw_intena`, `wp_s_sw_intena`,
`wp_s_ld_proc`) and the 4-byte `lw`/`sw` in `MachCSL/WpSmodeRules.lean`.

`printk` is not verified: it needs spinlocks (`acquire`/`release` with
`push_off`/`pop_off`, S-mode `sstatus` CSR rules and the AMO rules), the
console (`consputc` → `uartputc_sync`, a UART device model) and
`printint` (`divu`/`remu`, `.rodata` reads) -- the interrupt-toggling and
device layers of the context that do not exist yet.

### Instruction rules and stage lemmas

Symbolic execution of the model (`swp_run`) is confined to *leaf* lemmas in
`MachCSL/`: stage lemmas about one stage of the cycle (`swp_fetch_m4`,
`swp_tick_clock_m`, ...) and the execute stage of one instruction
(`execSpec_auipc`, ...).  `wpLoop_m_instr` assembles a whole cycle
from the stage lemmas, given the execute behaviour of the instruction and the
persistent `instr pc is_rvc i` (the Rocq prototype's `instr`: the fetch
footprint of the instruction at `pc` together with its decode fact; a
compressed encoding is described by the base instruction it expands to).  The
per-instruction rules `wp_m_<instr>` instantiate the execute part; code files
prove the `instr` facts for their literal words through the decode bridge
(`DecodeBridge.lean`: the kernel evaluates the decoder on a concrete
reference register map, and a once-proved read-frame congruence transports
the result to the symbolic configuration -- the model's well-founded
functions `hartSupports`/`currentlyEnabled` are `unseal`ed per fact so the
elaborator can evaluate them too).  A function's text is the contiguous
sublist of the dumped kernel instructions (`<f>Instrs`), so each fact picks
its word by list lookup.  Proofs about kernel code (`Xv6/Proof*.lean`) only
chain `wp_m_*` rules.

S-mode kernel code runs under the kernel execution context `kctx cpu k`
(`KCtx.lean`), the ever-present resource of the Rocq prototype's
`sie_cap_gpr`: the S-mode configuration cells, the whole register file, the
stack below `sp`, the translation slot, the interrupt arm and the per-cpu
bookkeeping all share the one index `k.sie`, so enabling interrupts (which
lets a trap claim the trap reserve of the stack at any instant) is one
transition of the whole bundle.  The rules `wp_s_<instr>` (`WpSmode.lean`)
take `kctx cpu k` and deliver `wpNext k.sie k.proc cpu K`: with interrupts on
and a current proc the continuation `K` may run on any hart (preemption,
scheduling, resumption elsewhere); with interrupts off it runs here.  The
execute stages behind them are stated over the register file
(`WpAluFile.lean`), so one leaf proof covers `add rd, rd, rs`, `mv`, `li` and
every other operand pattern.  Present limits: the rules assume `k.sie =
false` (no interrupt engine yet) and the Bare tier (no page-table fetch yet);
both are hypotheses that later work removes without changing the statements.

## Design (how it follows the paper and the Rocq prototype)

* **Model as a free monad.**  Sail's Lean backend targets `lean-sail`, whose
  concurrency-interface-V1 monad is a deterministic `EStateM`.  MachCSL needs
  the model's *events* (register/memory reads and writes, ...) to be explicit
  so that a machine step interprets one event at a time, interleaving harts
  and devices between events.  `vendor/lean-sail` therefore redefines
  `PreSailM` as a free monad over an `Outcome` event type (the analogue of the
  Rocq backend's `Interface.outcome`/`iMon`); the generated model compiles
  against it unchanged.
* **The language** (`Lang.lean`) is the Rocq prototype's: a hart expression
  `hart gen cpu m` carries the remaining Sail computation `m`; `primStep`
  consumes its head event (`evStep`), or at the cycle boundary (`m = pure ()`)
  restarts the fetch/decode/execute cycle `riscvStep tick` with a
  nondeterministic clock-tick choice.  Values are empty: the machine never
  terminates.
* **Eras** (the Rocq prototype's generations, `claude-notes/design/crash.md`
  there): the global state carries the current generation and the power bit.
  A hart of generation `gen` is *live* iff the power is on and `gen` is
  current; otherwise it can only self-loop (the corpse arm).  The power
  thread's `PowerOff` arm bumps the generation (so "`gen` has passed" is a
  stable death certificate) and `PowerOn` resets the machine to the boot image
  (`bootShape`) and forks the new generation's harts.  Both are observations.
  The ghost state mirrors this (`Resources.lean`): a fixed layer (`genAuth`,
  the started counter, the era registry) survives power cycles; the register
  maps and the memory heap are per era and simply abandoned at power loss.
  `wpHart` is stated under the persistent `genCert` (born + started +
  registered); `wpHart_lift` dispatches once and for all (live: the ambient
  era's `machInterp`; dead: `wp_dead`), so no instruction rule ever mentions
  a generation.  `wp_power` (`Power.lean`) is proved against a boot client
  obligation `Hboot`: from `powerBootRes` (certificate, every register cell,
  every byte) at any booted machine, the WPs of all harts; `wpLoop_ofEra`
  turns a client's ambient `wpLoop` into what the power thread forks.
* **Resources** (`Resources.lean`): one `ghost_map` per hart for registers
  (keyed by the register's constructor index, valued in `⟨r, v⟩` because
  registers have dependent types) and iris-lean's `gen_heap` for bytes.
* **WPs** (`Wp.lean`): `wpLoop cpu` is the continuation-style, postcondition-
  free WP of the paper; `swp cpu m Φ` is the paper's `wp Sail(m){Φ}`, defined
  in continuation-passing style over `wpHart` (as `HartSwp.swp` in the Rocq
  prototype) so that `swp_bind` is the sequencing combinator of §4.2 and every
  event rule is stated once against the head of `m`.
* Not yet ported: TSO/relaxed memory (memory is sequentially consistent),
  reservations for exclusive accesses, devices/MMIO, the observation-trace
  ghost, adequacy.  The state and step relation are shaped so these are
  additional fields and arms.

## Building

Toolchains: Lean via `elan` (`lean-toolchain` pins v4.32.2); the Sail compiler
with its Lean backend lives in the opam switch `lean-xv6` (built from
rems-project/sail git main, 2026-08; it is only needed to regenerate the
model).

```sh
lake build                                        # everything (model included; ~25 min first time)
opam exec --switch=lean-xv6 -- tools/regen_sail_model.sh   # regenerate model/Lean_RV64D
python3 tools/dump_kernel.py --kernel xv6-riscv/kernel/kernel   # regenerate Xv6/KernelImage.lean
tools/check_layering.sh                                        # Spec/Proof/Link import rules
python3 tools/gen_model_facts.py && python3 tools/gen_platform.py
```

## Checks and reports

`make help` lists the entry points (targets are in `tools/ci/*.mk`; each
script's header says what it guarantees and when it fails).

```sh
make lint          # layering, no sorry/axiom/native_decide, module drift, pins   (no toolchain)
make check-gen     # every generated file equals its generator's output           (no toolchain)
make test-tools    # unit tests of the Python tools (tools/tests/)
# after `lake build Xv6 MachCSL`, on the build machine:
tools/ci/timed_build.sh LOG --clean    # the build, with a timed log for the profile
tools/ci/reports.sh LOG                # profile, proof coverage (blocking), dead code
tools/ci/dead_imports.sh               # dead `import` lines (informational)
tools/ci/vtest.sh check-ci             # device conformance: the model against the checked-in captures
```

Proof coverage (`tools/proof_coverage.py`) joins the pinned images to the
elaborated environment (`tools/ci/EnvFacts.lean`).

* Kernel, per function: *proven* when a `Link*` theorem concludes a
  whole-function contract whose entry pc is the function's address and the
  top theorems (`tools/ci/roots.txt`) reach it.  Every kernel function must
  be, except the rows of `tools/ci/coverage_allow.txt` (each with its reason
  and what Rocq's coverage reports for it).
* User programs, per instruction: *stepped* when the instruction has a fact
  `uinstrIs γt pc rvc i` in the cone of the top theorems.  Every byte that is
  not stepped is explained from the program's call graph and control flow
  (`tools/text_coverage.py`): library code unreachable from the ELF entry,
  functions reachable only through call sites no proof steps, and dead arms
  behind a branch the proofs step one way.  A byte that stepped code runs
  into and nothing steps is a *finding*, and fails the check.  The floor is
  `tools/ci/coverage_user_baseline.txt`.

Device conformance (`vtest-lean/`, `tools/vtest/`) re-checks the machine
model -- the Sail hart as the language runs it, the two UARTs, the PLIC, the
virtio disk -- against 150 behaviours captured from QEMU, the VisionFive 2
board and the CVA6 RTL: each capture is a theorem that the language has an
execution showing what the platform showed (`RunAgrees`), proved by compiled
evaluation behind a proved link to the step relation.  It is not part of the
proof build; `tools/vtest/README.md` says what is claimed and what is trusted.

The model is generated from the MachCSL fork of sail-riscv
(`zeldovich/sail-riscv`, branch `xv6`, commit `070832a1`), the same source and
configuration as the Rocq prototype; the kernel image is `mit-pdos/xv6-riscv`
branch `verified` at `ded23f2a`.

## Continuous integration

`.github/workflows/ci.yml` runs on every push to `lean` and on pull requests
targeting it, on the self-hosted runner `coqdev`.  It is the Lean counterpart
of the Rocq tree's CI job, step for step, and **every step is one call of
`tools/ci/run_all.sh <step>`**, so CI and a developer run the same commands.

| step | what it checks | fails when |
|---|---|---|
| `toolchain` | installs elan and the Lean of `lean-toolchain` into `$HOME/.elan` if absent (no sudo); fetches the packages of `lake-manifest.json` without building or updating them | the download fails, or lake wants to rewrite the manifest |
| `toolchain-check` | the three `lean-toolchain` files agree, `lakefile.toml` and the manifest agree, the `lake` on `PATH` is the pinned Lean, every fetched package is at its pinned revision | any of them differs |
| `lint` | layering (Spec/Proof/Link); no `sorry`/`axiom` in `Xv6/`, `MachCSL/` and `vtest-lean/`, no `native_decide` in `Xv6/` and `MachCSL/`; every module is imported from the roots; the audited theorems are the coverage roots | any lint fails |
| `check-gen` | every generated file equals its generator's output (text trees, `ModelFacts`, `Platform`, the user images and what is derived from them) | a generated file is stale or hand-edited. Without `riscv64-linux-gnu-objdump` the user-ELF re-dump is *skipped*, not failed |
| `build-deps` | builds the Sail model, lean-sail and iris-lean (cached in CI) | they do not build |
| `build` | `lake build Xv6 MachCSL` from nothing, with a timed log | the proofs do not build |
| `audit` | the axioms of each top theorem and the `opaque`s / Sail platform hooks in its cone, against `tools/audit/baseline.json` | anything outside the baseline, a stale baseline row, a `sorryAx` anywhere |
| `tcb` | the definitions each top theorem's *statement* depends on, per file, against `tools/tcb/expected.json` | the set of modules (or axioms/opaques) a statement reaches changed |
| `reports` | proof coverage of the pinned images; build profile and dead code | a kernel function is not proven, linked and reached (and has no allowlist row), a user program is below its baseline or has an unexplained unstepped byte, a top theorem is gone. The profile and the dead-code report never fail |
| `vtest` | device conformance: the machine model against the captures checked in under `vtest-lean/` | a proof of the green set stopped compiling (a run with no proof is a finding, not a failure) |
| `test-tools` | the unit tests of the Python tools | a test fails |

The markdown of `check-gen`, `audit`, `tcb`, `reports` and `vtest` goes to the
job summary (about 150 KB in all; GitHub's limit is 1 MiB per step, and
`run_all.sh` cuts a step's summary to fit rather than lose it whole).

**What CI deliberately does not do.**  It does not build the xv6 kernel or
the user programs, does not re-dump the kernel images (`make check-gen-kernel`
does, given the pinned ELF), does not regenerate the Sail model (that needs
the patched `sail`: `tools/regen_sail_model.sh`, then `git diff --exit-code
model/`), and never runs QEMU.  All of those outputs are checked in; CI
compiles them, and re-derives only what needs neither an ELF nor `sail`.  The
proofs' build is not cached: every run recompiles `Xv6/` and `MachCSL/`, as
the Rocq job recompiles every `.vo`.  Only the toolchain and the builds that
no proof edit touches (the fetched packages, the model, lean-sail) are.

**Trust.**  `audit` and `lint` are about `Xv6/` and `MachCSL/`: the top
theorems use no `native_decide` and no axiom outside the baseline.  The
`vtest` suite is different and separate: each capture is checked by
`native_decide`, so it trusts the Lean compiler as well as the kernel
(one compiler-trust axiom per capture, confined to the `Vtest` library, which
is not a default target and which nothing in the proofs imports).

**Reproducing it.**  Never on the development machine
(`notes/coord/gcp_rule.txt`); on the build VM, from your worktree:

```sh
/shared/xv6rocq/gcp-rocq/run-on-gcp tools/ci/run_all.sh          # the whole sequence (= make ci)
/shared/xv6rocq/gcp-rocq/run-on-gcp tools/ci/run_all.sh audit    # one step
tools/ci/run_all.sh --list                                        # the step names
tools/ci/run_all.sh lint check-gen test-tools                     # the steps that need no Lean: anywhere
```

`-k` keeps going after a failure, `--from STEP` resumes.  Reports and logs go
to `.lake/ci/` (`summary.md` is what the job summary would be), and a table of
step times is printed at the end.  `run_all.sh build` builds incrementally
over whatever `.lake/build` holds; CI starts from a clean checkout, and
`make timed-build` is the clean build by hand.

Measured on the build VM (96 cores), running the workflow's step commands in
a fresh clone with an empty `$HOME`:

| step | from nothing | caches restored |
|---|---|---|
| `toolchain` (elan + Lean download, package clones) | 19 s | 0 s |
| `toolchain-check`, `lint`, `check-gen` | 7 s | 7 s |
| `build-deps` (model, lean-sail, iris-lean) | 2 min 10 s | 0 s |
| `build` (2657 jobs; 2.1-2.5 h of CPU; critical path 220-280 s) | 3 min 45 s | 3 min 49 s |
| `audit` | 32 s | 33 s |
| `tcb` | 14 s | 15 s |
| `reports` | 61 s | 61 s |
| `vtest` | 23 s | 23 s |
| `test-tools` | 1 s | 1 s |
| **total** | **8.5 min** | **6.2 min** |

On 96 cores the build is bound by its critical path (average parallelism
about 27); with fewer cores expect about 2.5 h / cores.  The two caches are 736 MB
(elan and the toolchain; used only on a runner that does not already have
the toolchain in `~/.elan`) and 150 MB (packages and the model build).

**What the runner needs.**  `bash` 5 or later (`timed_build.sh` uses
`EPOCHREALTIME`), `git`, `curl`, `python3` (standard library only), `make`,
`tar`, and GNU coreutils/grep/sed/awk; a writable `$HOME` (elan goes to
`~/.elan`, 2.8 GB); about 4 GB of workspace; network access to GitHub and, the
first time, to `elan.lean-lang.org` and `releases.lean-lang.org`.  Optional:
`riscv64-linux-gnu-objdump` (binutils), which turns the skipped `check-gen`
checks into real ones.  Memory: the build runs one `lean` per core; on the
96-core VM (shared, so these are upper bounds) available memory dropped by
20-35 GB during the two build steps and 13 GB during `vtest`, and by well
under 1 GB in every other step.

**The nightly dead-import sweep** is `.github/workflows/lean-dead-imports.yml`:
the same build, then `tools/ci/run_all.sh dead-imports`
(`tools/ci/dead_imports.sh`), report only.  GitHub fires scheduled workflows
only from the default branch, so that file takes effect once it is copied to
`main`; it checks out `lean` itself.
