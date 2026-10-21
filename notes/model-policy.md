# The machine model: what it is, what may change in it, and how

**Status:** approved by the owner 2026-10-19 (proposed the same day, during the sail-riscv 0.16
bump).  It
consolidates the owner's rulings on the bump (`notes/design-rulings.md`, "The sail-riscv 0.16
bump"), the rules the Rocq-era project laid down, and the policies of the projects this tree
depends on (section 7, with an assessment of each).  It is the standard every change to the model
and to how MachCSL runs it is judged by.  `notes/model-diffs.md` is the register this policy
requires; a conflict between the two is a bug in the register.

## 1. What "the model" is

The machine model is the Lean code in `model/Lean_RV64D/`, a reproducible function of eight pinned
inputs.  Every one of them is part of what the theorems are about:

| | Input | Where it is pinned | Who owns it |
|---|---|---|---|
| I1 | the upstream release of [riscv/sail-riscv](https://github.com/riscv/sail-riscv) | the base of `SAIL_RISCV_REV`, `tools/regen_sail_model.sh` | upstream |
| I2 | the model fork's commits on top of I1 (`dongjaelee1/sail-riscv`, branch `xv6`) | `SAIL_RISCV_REV` | this project |
| I3 | the module subset | `model/sail-modules.txt` | this project |
| I4 | the configuration | `model/sail-config-rv64d.json` | this project (values of upstream's knobs) |
| I5 | the Sail compiler (`dongjaelee1/sail`, branch `xv6` = an upstream `sail2` commit + Lean-backend fixes) | `SAIL_REV`, `SAIL_XV6_REV` in the regen script, checked against `sail --version` | upstream + this project's fixes |
| I6 | lean-sail, the Lean runtime the generated code targets | `lakefile.toml` (by git revision) and the regen script | upstream, used unmodified |
| I7 | the post-generation patches | the regen script | this project |
| I8 | the platform-hook realisations | `model/Xv6Extras.lean` | this project |

Around the model, MachCSL decides four more things the theorems depend on just as much:

| | MachCSL's side | Where |
|---|---|---|
| M1 | power-on: which register values a hart starts from | `MachCSL/ArchReset.lean` |
| M2 | the driver: how a cycle is driven (`try_step`'s arguments, the clock tick) | `MachCSL/Lang.lean` (`riscvStep`) |
| M3 | the event interpretation: what each `InstructionEffect` means | `MachCSL/Lang.lean`, `MachCSL/TsoMem.lean` |
| M4 | the platform: devices, memory map, interrupt wiring | `MachCSL/Dev/*`, `MachCSL/Platform.lean` |

**The claim this tree makes** (README) is therefore: *the proofs are about upstream sail-riscv
release I1, as specialised by I3 and I4, with the deviations I2, I5 and I7 recorded in
`notes/model-diffs.md`, run by MachCSL's semantics M1-M4.*  No document of this tree may call the
model "unmodified" or "the official semantics" without that qualification.

## 2. The order of authority

When sources disagree, this is the order:

- **A1. The ratified RISC-V specifications** (unprivileged and privileged ISA) are the authority
  on what hardware does.  Upstream's own contribution standard is to justify a change by quoting
  them; so is ours.
- **A2. The upstream release** is the authority on the formalisation of A1.  *Follow the model as
  released.*  Where the model and the spec disagree, the spec wins only through the deviation
  process of section 4, never by a silent edit.
- **A3. Upstream's configuration** is the way the model is specialised to a platform (WARL
  choices, extension sets, the memory map).  The ISA code is never edited for a platform reason a
  knob can express.
- **A4. The Sail language manual** is the authority on what the generated Lean must mean.  The
  Lean backend and lean-sail are tools: a backend bug is fixed in the compiler fork (I5), never
  worked around in the model, in a post-generation patch, or in a proof.
- **A5. MachCSL's own semantics** (M1-M4) is this project's and is documented in the files above.
  It may *add* behaviours the model leaves to the environment (an arbitrary power-on value, a
  nondeterministic tick) and may *remove* them only where the removal is recorded together with
  the spec's permission for it (section 5).

## 3. The ISA/platform boundary

Upstream draws the line itself, and this tree follows it:

- **The ISA part** -- instruction and CSR semantics, traps, interrupts behind
  `interrupt_interface.sail`, memory behind `phys_mem_interface.sail`, virtual memory, and the
  step function `try_step` -- is upstream's.  It is followed as released; changes to it are
  deviations (section 4).
- **The platform part** -- `platform.sail` (the CLINT and HTIF windows), the Simple Interrupt
  Generator (upstream: "for testing purposes"), the reservation and terminal hooks, randomness,
  and the harness's schedule (when `exit_wait` is passed, when the clock ticks) -- is explicitly
  not the specification, and upstream states its intent to move interrupt controllers out of the
  model.  MachCSL owns this part: its devices (two UARTs, the PLIC, the virtio disk), its driver,
  its hook realisations.  Replacing it is not a deviation of the model, but it is recorded
  (`notes/model-diffs.md` §5) because the theorems depend on it.
- **The seam** -- model code that mixes the two (the pin registers gated on the SIG; the CLINT,
  which stays inside the model and is hart-indexed since 0.16) -- is crossed in this order of
  preference: a configuration value; a hook; the smallest fork commit, written the way upstream
  says it is heading (external controllers), so that it can be offered upstream.

## 4. Deviations: the tiers and what each requires

A *deviation* is any way the generated model differs from upstream release I1 built with
upstream's defaults.  Every deviation has a tier, and every tier has an admission rule and a
record.  "Recorded" always means: a row in `notes/model-diffs.md` in the same commit, with the
tier, the reason, the behavioural difference, the theorems that depend on it, and its upstream
status.

| Tier | What | Admitted when | Decided by |
|---|---|---|---|
| **T0 Configuration** | a value of upstream's config differs from the release default | for one of two reasons, named in the entry: (a) *the platform* -- the configuration follows the validated platforms (QEMU virt, JH7110, CVA6; `notes/device-conformance.md`) wherever they agree: the memory map is the board's, and a feature they have may be turned off only when the kernel never uses it *and* the cost of modelling it is documented as prohibitive, in which case its device-conformance runs are recorded as configuration findings, never removed; "the kernel never uses it" alone is not a reason (amended 2026-10-20: item 8 of 2026-10-19 turned F and D off on that reason alone, made `misa` read a value no validated platform reports, and was withdrawn); *when the validated platforms disagree*, the integrator proposes which platform the value follows, with the kernel-use and cost arguments and the device-conformance result, the owner rules, and the other platforms' runs are recorded findings (added 2026-10-20 on the second audit; the three disagreements in the tree: H follows the boards, Sdtrig follows CVA6, B follows QEMU -- section 8); or (b) *continuity* -- a release changed a default, the old behaviour is spec-permitted, and a stated theorem depends on it (cite it; what the value fixes is the theorem's statement, not its soundness, and a capture that witnesses the platforms' behaviour turns the question into (a); reworded 2026-10-20 on the audit).  "As before" alone is not a reason.  Marked inline and in the file's header; `config_is_valid` re-checked.  Experimental extensions stay at upstream's defaults behind a gate defined `false`. | integrator; the owner where the validated platforms disagree |
| **T1 Module selection** | what is compiled (`sail-modules.txt`; an edit to a `requires` list) | it changes only *what* is compiled, never the behaviour of what is; code the selection makes unreachable is argued unreachable in this configuration; extensions advertised by `misa` but not compiled are listed | integrator |
| **T2 Platform integration** | a fork edit that connects the model to our platform | no configuration value or hook achieves it; the behaviour it adds or restores is spec-permitted; it is written for upstream's stated direction | integrator, reported |
| **T3 Representation** | a fork edit the Lean target needs, with identical behaviour | behavioural identity is argued in the commit (checked where possible); it is what upstream does for its own prover targets, so it is an upstream candidate | integrator, reported |
| **T4 Bug fix** | the released model contradicts a quotable sentence of the spec, or consults architectural state that does not exist in this configuration, and the effect is reachable here | the spec is quoted; the fix is minimal and in upstream's own style (with its precedent where one exists); an upstream candidate | integrator, reported |
| **T5 Spec-motivated strengthening** | behaviour the spec requires but upstream's scope (single-hart, sequential) does not model | **owner ruling only**, as a named exception: the spec clause; the exact difference from the release, sequential and concurrent; the theorems that need it; the residual gap; dropped at the next bump if no theorem needs it | owner |
| **T6 Anything else** | convenience, taste, "cleaner", a speculative fix | never | -- |

The other inputs have their own rules:

- **The compiler fork (I5)** may carry only Lean-backend fixes: a departure from the manual's
  semantics (the short-circuit of `&`/`|`, which the manual guarantees), a wrong value in the
  output (type-level arithmetic), or output that does not elaborate (keywords, `termination_by`).
  Each is a PR upstream or in upstreamable form.  Nothing in it may be specific to this model.
- **Post-generation patches (I7)** may only rewrite syntax to the same meaning; each is scripted,
  conditional, and reports itself; the target is zero patches.  A patch that would change meaning
  is a fork commit in disguise and is forbidden.
- **lean-sail (I6)** is used unmodified at a pinned revision.  A needed change is a lemma on
  MachCSL's side or a change upstream, never a vendored edit (the vendored copy the bump retired is
  the cautionary case).  Its own `lean-toolchain` is ignored by lake on purpose; the CI toolchain
  check says so.
- **Hook realisations (I8)** follow `model/Xv6Extras.lean`'s header: a hook is realised only where
  it has no effect on modelled state; the reservation predicates stay opaque; a hook whose result
  is consumed is left unrealised, so that a hart reaching it is stuck and the audit fails.  The
  generated code is never patched to the same end.

**What "clearly a bug" means (the owner's rule of 2026-10-19), operationally:** T4's test.  A
behaviour that is merely surprising, inefficient, or different from a previous release is not a
bug: a release that changes a default is followed, and the old behaviour is recovered, if at all,
through T0(b).

*Provenance (recorded 2026-10-20 on the audit):* T4's second clause -- a read of architectural state
that does not exist in this configuration -- was formulated on 2026-10-19 for fork 6 `f0ef9813`,
after that fix was made; its commit quotes no spec sentence (none says a disabled extension's CSRs
are not consulted) and rests on the model's own precedents (`mideleg` without S, `hedeleg` without
H).  The clause stands, as the test future cases are held to.

## 5. MachCSL's side: power-on, the driver, nondeterminism

- **Power-on** (`MachCSL/ArchReset.lean`): arbitrary garbage in every register, then the board's
  short explicit list of writes, then the model's own `init_model`, then the firmware step.  The
  model's register initialisers (`sail_model_init`) are not run: they would narrow power-on to the
  simulator's boots (the owner's decision, made twice in the Rocq era).  *A new board line needs
  all of:* (1) a consumed fact that `init_model` does not derive over an open register file
  (`MachCSL.BootReset` is the check); (2) a claim a reader can check against the board -- or, for
  a register with no hardware counterpart, evidence that upstream's own code relies on its
  declared initial value (upstream's reset is "the minimum the spec requires", so such a
  declaration is a power-on assumption in upstream's terms too), in which case the line is flagged
  as model bookkeeping (a third case beside the two above, formulated 2026-10-19 after the
  `written_trigger_index` line needed it); (3) never a reset added to the fork for MachCSL's convenience: that edits
  the ISA part to serve M1.
- **Registers the model consults that are architecturally absent in this configuration** (H's
  CSRs with H off): if the read can change behaviour, it is a T4 fix in upstream's style
  (`hideleg`, after the `mideleg` and `hedeleg` precedents); if it cannot, the cell is held at an
  arbitrary value (`hgeie` in `hwConfig`): no board line, no reset.
- **The driver** (`riscvStep`): the model's `try_step` is the semantics; the schedule is the
  environment's, and upstream itself runs two different ones.  Every schedule choice that removes
  behaviours is recorded with the spec's permission for it.  The policy prefers exposing the
  environment's inputs nondeterministically (the tick already is; `exit_wait` should be), so that
  the theorems cover every schedule upstream runs.
- **Nondeterminism and failure**: an unspecified value is modelled as *anything*, never as
  nothing; a model failure (`assert`, `exit`, an unrealised hook, lean-sail's failing
  `undefined_*`) is a stuck hart, never excused; a claim that the model cannot do something comes
  from its definitions, never from a runner's silence.  The one such path known in this
  configuration, an M-mode `csrr mseccfg` (`notes/model-diffs.md` section 4: an uncompiled Zkr clause
  behind `is_CSR_accessible`), is recorded as a residual -- pre-bump and off every kernel path -- not
  excused.

## 6. Process

- **Pins.** All of I1-I6 are pinned by commit hash.  `tools/regen_sail_model.sh` *fails* on a
  checkout at another fork revision or a compiler other than the pinned merge
  (`REGEN_ALLOW_UNPINNED=1` downgrades both to warnings, for an experiment whose output is never
  committed).  The CI toolchain check keeps the two lean-sail pins and the lake manifest in
  agreement.
- **Reproducibility.** A regeneration is accepted only when: `git diff --exit-code model/` is
  empty *before* the intended change; every generated module builds (not only the root's import
  closure); `tools/check_gen.py` passes (it also regenerates the tables derived from the model:
  `ModelFacts`, `Platform`, the literal-CSR block of `UExecCsrDflt`); the configuration's
  deviation markers agree with its header (`tools/config_deviation_lint.py`, run by the lints);
  the `Register` count matches (`MachCSL.regCount`);
  `#print axioms` of the top theorem shows the three standard axioms; the cold-boot proof
  evaluates `config_is_valid`; and the device-conformance runs (`tools/ci/vtest.sh`) stay green.
- **Bumps.** The model moves release to release, never to a `master` commit.  The compiler moves
  to a release once one contains the fixes; until then a pinned upstream commit plus the fixes.  A
  bump: reads the ChangeLog since the previous pin and lists every item touching a recorded
  deviation or a board line; regenerates the configuration from upstream's template and re-applies
  the deviations by script, then diffs field by field (the first 0.16 refresh silently lost one:
  that is the case this rule exists for); re-derives the board list by running `BootReset` over
  garbage and listing which consumed facts stopped deriving, before adding or removing a line;
  re-audits lean-sail's source when its pin moves (it has no changelog).
- **The register** (`notes/model-diffs.md`): one row per deviation with the fields of section 4,
  updated in the same commit; "upstream status" is one of *PR #n open / merged in release X /
  candidate, not filed / owner decided not to file*.
- **Upstreaming.** Nothing is filed upstream (owner, 2026-10-19): the project keeps its own fork,
  and filing is low priority.  Every fork commit still keeps the shape that would allow it -- one
  topic, a spec quotation where the tier asks for one, upstream's style -- as hygiene, and the
  register's "upstream status" records *owner decided not to file*.
- **Public claims and notes.** README and every note describe the model as section 1's claim.
  Deviation headers ("Deviations from Rocq", "Deviations from upstream") and the rule that a
  tracked file points at nothing outside the repository are this tree's conventions, not
  inherited ones; they stand.
- **The green set** (`vtest-lean/Vtest.lean`'s imports; 2026-10-20).  A run leaves the green set
  only by an owner ruling recorded in `notes/design-rulings.md`; until then a run that went red is a
  failing check, not a finding.  (Item 8's three runs were moved out about an hour after the item
  landed and a day and a half before the owner saw the consequence; the rule exists for that.)
- **Configuration changes** (2026-10-20) are proposed to the owner together with
  `tools/ci/vtest.sh check-ci`'s result on the changed configuration, never before it: the
  device-conformance runs are the arbiter of which machine the configuration describes.
- **Who decides.** T0 where the validated platforms agree, T1-T3 and compiler fixes: the integrator,
  recorded; a T0 value on which the validated platforms disagree: the owner, on the integrator's
  proposal (2026-10-20).  T4: the integrator, with
  the spec quotation, reported to the owner.  T5, every change to M1's board list, every change to
  M2's schedule, every change to the kernel's and the user tier's contracts (`SpecUser.USER`'s
  statement, `smFacts`, the user frames), and moving a run out of the green set: the owner.

## 7. The policies this one rests on, and how far each is adopted

Investigated 2026-10-19 (the Rocq-era tree at `rocq`; sail-riscv 0.16's README, CONTRIBUTING,
docs and ChangeLog; the Sail manual and the Lean backend's sources; lean-sail v7's sources).

| Source | Policy | Assessment | Here |
|---|---|---|---|
| xv6iris (Rocq) | "against the official Sail RISC-V semantics (from the fork)" | honest only while the fork is enumerated beside it; "official" cannot carry a fork that changes translation behaviour | §1's qualified claim |
| xv6iris (Rocq) | four inputs decide the model; one pin; regenerate unchanged first; a wrong pin is a warning | right shape; the warning was too weak (silent compiler fallbacks happened) | §6, fail by default |
| xv6iris (Rocq) | the config is the lever: turn off what the kernel never uses; pin an old default when the proofs depend on it | both sound, never stated as one rule | T0(a) and T0(b) |
| xv6iris (Rocq) | fix at the source, in the fork; never patch generated code; hand copies only if kernel-checked | consistent, well executed | §4 (I7 rule); T2-T5 |
| xv6iris (Rocq) | hooks: realise only what has no effect on state; consumed hooks stay unrealised | principled | I8 |
| xv6iris (Rocq) | power-on = garbage + minimal board list + the spec's reset; `sail_model_init` not run | the strongest rule in the tree, and the one a bump exposes most; it had no re-derivation procedure | §5, §6 (bumps) |
| xv6iris (Rocq) | prefer fixing the config to fixing a constant; the TCB audit; undefined is "anything"; the tick is a sound weakening; vtest validates against machines | all adopted unchanged | §5, §6 |
| xv6iris (Rocq) | defects: kernel bugs are never modelled; model defects fixed ad hoc, nothing reported upstream | the kernel side is exemplary; the model side needed the tiers | §4, §6 (upstreaming) |
| sail-riscv | the model is the ISA spec adopted by RISC-V International; justify a change by quoting the spec | reasonable; applies to the ISA part only | A1, A2, T4 |
| sail-riscv | specialise through the configuration, validated by `config_is_valid` | reasonable; several of our needs have no knob, so some code deviations are unavoidable | A3, T0 |
| sail-riscv | "platform" is not ISA; interrupt controllers are to become external; the harness owns the schedule | supports MachCSL owning the platform and the driver | §3, §5 |
| sail-riscv | unratified extensions gated off by `sys_enable_experimental_extensions` | adoptable as is | T0 |
| sail-riscv | reset is the spec's minimum; the rest is power-on state (some declared initialisers are relied upon) | consistent with board obligations; names the bookkeeping case | §5 |
| sail-riscv | prover-motivated edits are behaviour-preserving rewrites, routinely merged | our T3 commits are of that kind | T3 |
| sail-riscv | scope is single-hart; system-level concurrency deferred (PR #1860) | a multi-hart verification needs more; hence a tier that only the owner opens | T5 |
| sail-riscv | pin a Sail release; document changed defaults with a recovery recipe; contribution hygiene (one topic, DCO, AI disclosure) | adoptable | §6 |
| Sail manual | boolean `&`/`|` short-circuit; `undefined` has no fixed meaning; externs are backend-defined | the short-circuit patch is a correctness fix; everything about `undefined` must be read off the backend and runtime | I5 rule; §5 |
| Sail (Lean backend) | "highly experimental"; no semantic guarantee; tested by golden files and the exec suite | treat the output as the thing audited | §6 (reproducibility) |
| lean-sail v7 | no README, releases or changelog; failing `undefined_int/nat/string`, choosing `undefined_range` (upper bound excluded), uncatchable `exit`/`assert`, no-op printing; its toolchain pin is nominal | its semantics is its 1,700 lines: pin by commit, re-audit on a bump, record the interface facts | I6 rule; `notes/model-diffs.md` §5 |

## 8. The 0.16 bump judged by this policy

| Deviation | Tier | Verdict |
|---|---|---|
| fork 1 `2dfb4844`, atomic PTE A/D update (carried since the Rocq era's fork) | **T5** (owner exception, bump decision D3) | keep: `MachCSL.TsoMem`'s exclusive PTE kinds (`akPteRe`) and `WpPtWalk`/`WpPtWalkOwn` depend on it; the step-7 value compare the spec asks for (and upstream's reviewers asked for on PR #1860) is the recorded residual gap, to be completed in a later lane (decision (2) below) |
| fork 2 `3fdb4bca`, pins read without the SIG | **T2** | keep: platform fidelity -- the validated platforms' external interrupts come from a PLIC that drives the pins, which upstream (the SIG its only source, the pins private) offers no knob for; relocating the SIG's window would avoid the collision but model a device no platform has; framed for upstream's external-controller direction |
| fork 3 `69ed097e`, fork 4 `9da94b63` | **T3** | keep; upstream candidates |
| fork 5 `d2cb43fc`, F/D out of `postlude` | **T1** by a `requires` edit, plus a code edit (two `transformed_instruction` arms dropped) that T1 does not cover: unreachable here twice over -- `transformed_instruction` runs only under `currentlyEnabled Ext_H`, and without `FD_instructions` the `LOAD_FP`/`STORE_FP` constructors do not exist (which is why the edit was needed) | keep; local: in a configuration with H and the F/D instructions the edit changes behaviour (mtinst/htinst get 0), so it is not an upstream candidate |
| fork 6 `f0ef9813`, `hideleg` ignored without H | **T4** (precedents `mideleg`, `hedeleg`; upstream's own Lean emulator admits the read: `lean_emulator/LeanRiscv.lean:249-264` lists the hypervisor registers "read during reset and interrupt polling even when executing in Machine mode" and initialises `hideleg` with `undefined_Minterrupts ()`) | keep; upstream candidate |
| compiler: short-circuit, type-level parens (PRs #1750, #1774 open); keyword escape, `termination_by` (ours) | I5 rule | keep until a release contains them; the two of ours are candidates |
| patches A, B | I7 rule | keep; both meaning-preserving; retire when the backend allows |
| config items 1-7 | **T0**: 1, 4 (a); 2 -- V off by the platforms' `misa` (all three without V: `core_csrvals` slot 1, QEMU 0x001411AD, JH7110 0x0094112F, CVA6 0x0014112F), B off a platform DISAGREEMENT resolved toward QEMU (the JH7110 and CVA6 report B -- finding 29 for the JH7110, the CVA6 `core_csrvals` capture for CVA6; the kernel never uses it; the cost is the complete U-mode decode image, `MachCSL/UDecode.lean` pins `misa`; owner ruling 2026-10-20); 3 -- H off follows the boards (QEMU virt alone reports H: findings 19/29; the kernel never enters a virtual privilege or touches an H CSR; H on adds the HLV/HSV/HFENCE families to the U-mode decode image, two-stage translation to every walk leaf and the H CSRs to the power-on obligations) and Sdtrig off follows CVA6 (`core_csrprobe` slot 35: `csrr tselect` traps on CVA6, not on QEMU or the JH7110; the kernel never touches a trigger CSR; cost estimated, not measured: trigger checks on every fetch, load, store and AMO leaf, and the trigger file in the power-on obligations), both disagreements ruled 2026-10-20, QEMU/CoreCsrprobe the recorded finding; 5, 6 forced by `config_is_valid` once H and Sdtrig are off; 7 (b): `MachCSL/UMemAmo.lean`'s rules state the pre-0.13 cause, which the spec permits, unvalidated by any capture | keep; item 8 (F and D off, 2026-10-19) withdrawn 2026-10-20; the Sdtrig justification corrected 2026-10-20 (it had said every platform has Sdtrig); the B justification corrected 2026-10-20 (the record fix of the same morning had said every platform reports `misa` without B -- false) |
| module subset + Sdtrig; `misa` advertises F/D it does not compile | **T1** | keep; `misa` advertises F and D as the validated platforms do, their instructions uncompiled (T1, listed; withdrawal of item 8, 2026-10-20); the scalar-crypto and Zfh advertisements stay at upstream's defaults, with the M-mode `csrr mseccfg` stuck path recorded (register section 4; owner, 2026-10-20) |
| board line `written_trigger_index := none` | §5 (model bookkeeping, flagged; upstream relies on the declared `None()`) | keep |
| `hgeie` existential, `mhartid` pinned in `hwConfig` | §5 | keep |
| the driver's `exit_wait = false` | §5: a recorded restriction (upstream runs two schedules; the spec allows WFI to wait or to retire) | nondeterministic since 2026-10-19 (decision (3)): `riscvStep tick ew` |
| lean-sail's rendering of `undefined_*`, `exit`/`assert`, printing, uninitialised registers | interface facts, recorded in `notes/model-diffs.md` §5 | none on a kernel path |
| the dropped fork reset `a5460414` (`hideleg`/`hgeie`) | would have been a reset in the fork for M1's sake | dropped, correctly |
| README's "official semantics", "unmodified"; `master` for `sail2`; "nothing reported upstream" | §1, §6 | corrected 2026-10-19 |

**Decided by the owner (2026-10-19):** (1) this policy is approved; (2) the T5 exception stays
with its recorded gap for now and is completed with the spec's step-7 compare in a lane of its own
after the bump's leaves (a fork commit under T5, re-ruled then); (3) `exit_wait` becomes
nondeterministic, with the WFI leaves of P3; (4) nothing is filed upstream (section 6); (5) F and D
were turned off in the configuration (then T0(a)) on 2026-10-19 and **turned back on 2026-10-20**:
the device-conformance runs showed every validated platform has F and D and `misa` had come to read a
value no platform reports; T0(a) was amended accordingly (above), and Sdtrig stays off with its one
run recorded as a finding.

**Decided by the owner (2026-10-20), on the independent audit** (a clean-context review of the
bump's decisions; `local-plan/model-bump/policy-review/audit-2026-10-20.md`, outside the
repository): (6) Sdtrig stays off, justified by the witnessed platform disagreement, not by the
withdrawn claim that every platform has it; (7) configuration item 7 stays, T0(b) reworded as above;
(8) no configuration change for the scalar-crypto and Zfh advertisements, the `csrr mseccfg` stuck
path a recorded residual; (9) the 2026-10-19 changes to the user tier's and the kernel's contracts are
ratified (`notes/design-rulings.md`); (10) the green-set and configuration-change rules of section 6
are adopted.  The audit's remaining items were record corrections, made the same day.

**Decided by the owner (2026-10-20, later), on a second independent audit**
(`local-plan/model-bump/policy-review/audit2-2026-10-20.md`): (11) B stays off as a platform
disagreement resolved toward QEMU (above; the morning's record fix had justified it by a false
claim, corrected); (12) T0(a)'s disagreement rule (above), applied to H, Sdtrig and B; (13) the
audit's record fixes -- the stuck run is finding 32, not 22; the A/D `Ok(false)` arm is an
`internal_error`, a stuck hart, not a retry, and upstream's `write_ram` discards the conditional-write
result; `sig_hgeip`; fork 5's and fork 6's arguments; `claude-notes/LEAN.md`; patch B's scope; the
compiler row; the adequacy note's heading -- in one commit.
