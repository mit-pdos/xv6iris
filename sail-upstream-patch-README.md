# Upstream-submittable patch: ifetch / TTW tagging at the Sail concurrency interface

## What this is

`sail-ifetch-ttw-tagging-upstream.patch` is a single-commit `git format-patch`
against **upstream `riscv/sail-riscv`**, ready to `git am` onto a branch and open
a PR from. It is the upstream port of the local fork patch
`sail-ifetch-ttw-tagging.patch` (fork commit `00046a7`).

It makes the Sail RISC-V model distinguish, at the concurrency interface, three
kinds of read that are currently indistinguishable there:

- an instruction fetch → `Read_ifetch` → `AK_ifetch()`
- a page-table walk's PTE read → `Read_ttw` (new) → `AK_ttw()`
- everything else → unchanged (`read_kind_of_flags(aq, rl, res)`)

Two files, +24/-1:

- `model/core/phys_mem_interface.sail` — add `Read_ttw` to `enum read_kind`, and
  `Read_ttw => AK_ttw()` to the access-kind match in `read_ram`.
- `model/sys/mem.sail` — in `checked_mem_read`, replace
  `let rk = read_kind_of_flags(aq, rl, res);` with a match on `(access, res)`.

## Upstream state

**Upstream still has the issue as of the SHA below.** `read_kind_of_flags`
(`model/sys/mem.sail:37`) chooses the read kind from the acquire/release/reserved
flags alone; `checked_mem_read` calls it unconditionally, so a fetch, a walk and a
data load all reach `sail_mem_read` as `AK_explicit { AV_plain, AS_normal }`.
`Read_ifetch` exists in `enum read_kind` and maps to `AK_ifetch()`, but nothing in
the model ever passes it; nothing maps to `AK_ttw` at all. (`AK_ifetch` and
`AK_ttw` are both defined in the Sail library's
`lib/concurrency_interface/read_write_v1.sail`.)

- Prepared against upstream `riscv/sail-riscv` **`6f6f2abd533aab765ca2e2f6a14117a12ce9d4f8`**
  ("Add config options for vstvec and the Shvstvecd extension (#1902)", 2026-08-26),
  which was `master` HEAD at the time. The patch carries a `base-commit:` trailer
  recording that SHA.

## What changed in the port, relative to the fork patch

- **Same code shape**; the file layout and the two anchors are unchanged upstream,
  so the diff is structurally identical.
- **The `res` guard is kept, but its justification changed.** The fork has an
  LR/SC-based A/D-bit update (`read_pte_exclusive`, which reads a PTE with
  `res = true`), so on the fork the guard is live. Upstream has no such path — in fact `check_pma` asserts `not(res_or_con)` for `Load(PageTableEntry)`
  and for `InstructionFetch()`, so the guard is currently dead code. It is retained
  as future-proofing (an LR/SC-based A/D update must not silently lose its
  exclusive access kind), and the comment says exactly that.
- **Comments rewritten for upstream**: no shouty capitalisation, no reference to
  the fork's `read_pte_exclusive`, and the rationale is phrased in terms of RVWMO
  and the Zifencei / sfence.vma / Svvptc coherence axes.
- **Commit message rewritten from upstream's perspective**: motivated by the
  faithfulness of the emitted event stream for concurrency/memory-model consumers,
  with an explicit statement that sequential/functional behaviour is unaffected.

## What was verified

- The patch applies cleanly (`git apply --check`) to a pristine checkout of the
  base SHA above.
- Both anchors are unique in upstream's tree
  (`let rk = read_kind_of_flags(aq, rl, res);` occurs once; `Read_ifetch => AK_ifetch(),`
  occurs once).
- Upstream's required Sail version is **0.20.2**
  (`cmake/sail_required_version.txt`), which matches the Sail available locally
  (`sail 0.20.2`) — no version mismatch.
- **Full model typecheck passes**: with the patch applied,
  `sail model/riscv.sail_project --all-modules --strict-var --strict-bitvector
  --strict-exponentials --require-version 0.20.2` exits 0 with no diagnostics
  (these are exactly upstream's `sail_common` flags from `model/CMakeLists.txt`).
  A deliberately-broken variant was checked to confirm the typecheck is real (it
  reports the expected unbound-identifier error).
- **C++ backend generation passes**: the same invocation plus upstream's
  `--cpp` code-generation flags produces `sail_riscv_model.cpp` successfully, and
  the generated code contains the new `Read_ttw` → `AK_ttw` arm.

## What was NOT verified

- No full CMake build of the C emulator, and no linking/running of the emulator.
- No test suite run (no RISC-V test binaries or toolchain exercised), and no
  architectural-test run.
- No Lean/Rocq/Isla backend generation. `handwritten_support/riscv_extras_sequential.lem`
  mentions `Read_plain` / `Read_RISCV_reserved` but does not match exhaustively on
  `read_kind`, so adding a constructor should be harmless there; this was inspected,
  not built.
- No behavioural check that the new event stream is what a concurrency consumer
  wants — the change is by inspection of the access-kind definitions.
- `pre-commit` was not run; the diff was checked by hand against `CODE_STYLE.md`
  (two-space indent, no tabs, no trailing whitespace, `//` line comments).

## Note before submitting

Upstream's `CONTRIBUTING.md` says: *"We require any and all use of generative AI
tools, e.g. for writing code, comments, documentation, or PR text, to be
disclosed."* The commit therefore keeps a `Co-Authored-By: Claude ...` trailer as
that disclosure, and the suggested PR text below repeats it. The commit also
carries a `Claude-Session:` trailer with a link that is not publicly resolvable —
consider dropping that one line before submitting (edit during `git am`, or
`git commit --amend` after).

## Suggested PR description

> The Sail concurrency interface defines `AK_ifetch` and `AK_ttw` for instruction
> fetches and translation-table walks, but the RISC-V model produces neither: the
> read kind attached to a memory read is chosen by `read_kind_of_flags(aq, rl, res)`
> from the ordering flags alone, so a fetch, a page-table walk and an ordinary data
> load all reach `sail_mem_read` as an identical `AK_explicit { AV_plain, AS_normal }`
> event. `Read_ifetch` has no producer anywhere in the model, and nothing maps to
> `AK_ttw` at all. That leaves the emitted event stream unable to express a split
> the architecture makes: RVWMO constrains explicit accesses, while instruction-fetch
> coherence (Zifencei) and walk coherence (`sfence.vma`, Svvptc) are separate axes,
> so a memory-model backend, a litmus-test harness or a concurrent port of the model
> has nothing to key on. This PR chooses the read kind from the access type instead —
> `InstructionFetch()` → `Read_ifetch` → `AK_ifetch()`, `Load(PageTableEntry)` → a new
> `Read_ttw` → `AK_ttw()`, everything else unchanged — in two files, +24/-1. The match
> is guarded on `res` so a reserved read keeps its exclusive kind whatever it reads;
> that guard is dead today (`check_pma` asserts a fetch or PTE access is never
> reserved) and is there so a future LR/SC-based A/D-bit update cannot silently lose
> its exclusivity. No existing read kind changes meaning and there is no change to
> sequential or functional behaviour — the read kind is observable only through the
> concurrency interface's access kind, which the sequential backends ignore.
> Verification: the model typechecks and the C++ backend generates cleanly with
> upstream's own Sail flags (Sail 0.20.2, as required by
> `cmake/sail_required_version.txt`); I have not run the full emulator test suite.
> Disclosure per CONTRIBUTING.md: generative AI (Claude) was used in preparing this
> change and its description.
