# xv6iris (Lean port)

Porting the Rocq/Iris xv6-on-Sail-RISC-V development (`../iris`) to **Lean 4**,
on top of [iris-lean](https://github.com/leanprover-community/iris-lean).

## Status

- **Phase 0 done ✅** — lake workspace on Lean v4.31.0; iris-lean builds as a
  dependency; `Xv6Iris/Hello.lean` proves a MoSeL entailment (`P ∗ Q ⊢ Q ∗ P`).
  `lake build` is green.
- **Memory substrate decided: free/interaction monad** (option 1). The Rocq
  foundational layers (`run`/`exec`/determinism, the `Language` instance,
  points-to) therefore port *directly* rather than evaporating.
- **Byte prelude started** — `Xv6Iris/ModelBytes.lean` (port of
  `RiscvModelBytes.v`): `paAdd`/`nthByte`/`assembleBytes`/`readBytes`/`writeBytes`
  definitions compile; spec lemmas are the next increment.
- **Iris side built out (vertical slice, all compiling) ✅** — `lake build` green:
  - `Xv6Iris/SailMonad.lean` — the free monad as a proper module (the prototype
    promoted): `Outcome`/`Mon`/`bind`(total structural)/`Monad`/`MonadExceptOf` +
    the named primitive surface.
  - `Xv6Iris/Interp.lean` — `MState` + the `exec` interpreter (effects → register
    /memory maps; `choosePrim` resolved by `trivialChoiceSource`) + `run` (its
    graph) + `run_deterministic`. Analog of Rocq `RiscvLang.run`/`RiscvExec.exec`.
    `exec` is total structural (Lean accepts the recursion-under-binder again).
  - `Xv6Iris/Lang.lean` — the iris-lean `Language`/`PrimStep`/`ToVal` instance on
    a concrete demo machine (`Loop`, `Val = Empty`, step = `PC := PC+4`), i.e. the
    operational semantics plugged into iris-lean's program logic.
  - `Xv6Iris/Ptsto.lean` — the ghost-state layer: a register `gen_heap`, `↦ᵣ`
    points-to, the agreement-bridge `stateInterp` (`∃ rm, genHeapInterp rm ∗
    ⌜regAgree rm σ.regs⌝`, Rocq's `reg_interp` pattern), the `StateInterp` +
    `IrisGS_gen` instances, and the read-bridge lemma **`reg_valid`** (proved via
    `genHeap_valid` + agreement).

  Two iris-lean specifics learned: (1) registers are keyed by `Nat` via an
  injective `regAddr` because a custom enum key lacks the `LawfulFiniteMap`
  (`Ord`/`TransOrd`/`LawfulEqOrd`) instances; (2) a *second* `gen_heap` (byte
  memory) must use a **distinct key type** — `genHeapGS`'s `V` is an `outParam`,
  so two heaps over the same key type are ambiguous to instance resolution.

  Next increment: `reg_update` (write bridge; needs map `get?_insert` lemmas +
  `regAddr` injectivity) and **`wp_step`** — the one-step WP rule (analog of Rocq
  `wp_exec_step`) via `wp_lift_step`, then a first real WP about the demo step.

### The one external dependency to resolve — RESOLVED to a path

The free/interaction-monad decision means we need the RISC-V model **in**
interaction-monad form. Investigation of the Sail compiler's Lean backend
(`rems-project/sail`, `src/sail_lean_backend/`):

- The Lean backend has **no monad-selection flag** (only output / lib /
  `-lean_executable` / `-lean_noncomputable` / `-lean_real-numbers` toggles).
  `-lean_noncomputable` merely prepends a `noncomputable section` header — it
  does **not** produce a free monad.
- The printer **hardcodes** `abbrev SailM := PreSailM RegisterType
  trivialChoiceSource exception` (and `SailME`), i.e. always the `lean-sail`
  EStateM. The concurrency interface (`outcome`s, `sail_mem_read/write`) is
  emitted as concrete EStateM ops, not suspendable effects. (The Sail **Coq**
  backend *does* emit the free/prompt interaction monad — the Lean one does not.)

So an off-the-shelf interaction-monad export does **not** exist. But the path is
clean: the 172k-line generated model uses only a **small, named primitive
surface** from `lean-sail` — `readReg`/`writeReg`/`readRegRef`/`writeRegRef`/
`reg_deref`/`sail_mem_read`/`sail_mem_write`/`read_ram`/`write_ram`/`assert`/
`choose`/`internal_pick`/`undefined_*`/`sailThrow`/`sailTryCatch`/`sail_barrier`/
`sail_take_exception` + `Monad` do-notation + `SailME.run` — and never touches
EStateM internals directly. **Plan: fork `lean-sail` to redefine `PreSailM` and
those ~20 primitives as a free/interaction monad** (same names + signatures,
lawful `Monad` instance, `choose`/`internal_pick` → `Choose` outcomes). Then the
**unchanged generated model** becomes an interaction-monad program — no edits to
generated code, no Sail-compiler changes. Cost: re-prove the monad laws +
primitive lemmas (the `simp_sail` set) for the free-monad versions.

(Upstream alternative: add a free-monad target to the Sail Lean backend — more
work, benefits everyone, needs rems-project coordination. The lean-sail fork is
faster and entirely in our control.)

Until the fork lands, the foundation is built model-agnostically against this
abstract interaction-monad interface and validated on a hand-written micro-model.

#### Prototype (done ✅) — `proto/SailFree.lean`

A standalone prototype validates the fork approach. It defines the free monad as a
**polynomial/container free monad** (a concrete `Outcome` effect inductive +
continuation, à la Rocq `Interface.outcome`/`iMon`) and reimplements lean-sail's
named primitive surface with identical signatures. Results:

- The free monad stays in **`Type 0`** (so `SailM α : Type 0`, matching EStateM —
  no universe friction with the generated model). Achieved by the polynomial
  design (no existential over `Type`).
- `Mon.bind` is a **total structural function** — Lean 4.31 accepts the
  recursion-under-binder, so we keep `bind`'s definitional equations (needed for
  the Iris interpreter + proofs; no `partial`).
- `Monad`, `MonadExceptOf (Error ue)`, the `PreSailME` early-return submonad
  (`ExceptT` over the free monad), and `SailME.run`/`throw` all port unchanged.
- Memory effects (`readByte`/`writeByte`) are now `Outcome` *constructors* — the
  interposition seam for MMIO + multi-HART.
- **Verbatim generated model bodies type-check unchanged** against it:
  `encdec_uop_backwards` (do / BitVec-literal match / `assert` / bare `throw
  Error.Exit`), `get_arch_pc` + `tick_pc` (`readReg`/`writeReg`), `not_implemented`
  + `internal_error` (`sailThrow`). Plus representative memory (`readBytes` →
  `readByte` effects) and early-return (`SailME.run`/`throw`) paths. `lake env
  lean proto/SailFree.lean` exits 0.

Still to verify before the full 172k-line model builds: the v4.29→v4.31 toolchain
bump (independent of the monad); a few patterns not in the slice (`sailTryCatchE`,
vector mem ops, the `simp_sail` attribute tags, `main_of_sail_main` — executable
-only). The model does **not** use `get`/`modify`/EStateM internals directly
(confirmed by grep), which is what makes the monad swap clean.

## The three pillars and where they stand

| Pillar | Rocq | Lean target | Notes |
|---|---|---|---|
| Separation-logic framework | coq-iris 4.4 | iris-lean @ `3877dbe`, Lean v4.31.0 | Has `ProgramLogic/{WeakestPre,Lifting,Language,Adequacy}`, `BI/Lib/GenHeap`, ProofMode, full HeapLang template. ✅ feasible |
| Sail RISC-V model | generated Coq (`../model-xv6iris`, free monad) | [`opencompl/sail-riscv-lean`](https://github.com/opencompl/sail-riscv-lean) + [`rems-project/lean-sail`](https://github.com/rems-project/lean-sail) (EStateM) | Lean v4.29.0 → must reconcile toolchain. **Different monad** (see below). |
| Kernel image | `../kernel-rocq` via `../tools/dump_kernel.py` | regenerate as Lean data | Mechanical; re-target the dumper's `--format`. |

## The pivotal design difference: the model monad

- **Rocq model** is a *free / interaction monad*: `M X` with `Ret` / `Next outcome k`,
  where `outcome` has `MemRead n req` / `MemWrite r ... ` etc. as **constructors**.
  The Rocq foundation (`RiscvLang.run`, `RiscvExec.exec`, `exec_run_det`, much of
  `RiscvTryStep`) is an *interpreter* over that tree. The interpreter **interposes**
  on every memory effect — which is exactly how it separates RAM (Iris `gen_heap`
  points-to) from CLINT / HTIF / SIG MMIO ranges.

- **Lean model** (`lean-sail`) is a *concrete deterministic state monad*:
  `SailM = EStateM (Error exception) SequentialState`, with
  `SequentialState = { regs : ExtDHashMap Register RegisterType,
  mem : ExtHashMap Nat (BitVec 8), choiceState, ... }` and `trivialChoiceSource`
  resolving all `choose`/undefined deterministically. `try_step : Nat → Bool → SailM Bool`
  is a state transformer; one machine step is `(try_step 0 false).run σ = .ok _ σ'`.
  Primitives are tagged `@[simp_sail]`.

### Consequence — and the open fork (see "Memory substrate" below)

If we accept a **single flat memory, single HART**, the EStateM form is *simpler*
than Rocq: the relational/functional interpreter + determinism machinery largely
evaporates (EStateM is already a deterministic function; `simp [simp_sail]` steps
it). But that form has **no memory-effect interposition**: `sail_mem_read` /
`sail_mem_write` are fixed `def`s that read/write the one flat `mem` hashmap. For
**MMIO devices** and **shared memory between HARTs**, we need interposition back.

Every load/store/fetch in the model funnels through exactly one seam:
`read_ram`/`write_ram` → `sail_mem_read`/`sail_mem_write` (concurrency interface
V1) → `readBytes`/`writeBytes` on `mem`. So interposition is achievable, two ways:

1. **Enrich the EStateM state + reimplement the seam.** Replace flat `mem` with a
   structured memory (RAM region + MMIO device map + handlers); reimplement
   `sail_mem_read`/`write` to dispatch by address. Multi-HART = one
   `SequentialState` per HART + shared memory as a separate Iris resource + an
   explicit scheduler at the language level. Bespoke, but keeps the fast
   deterministic datapath. Requires **forking lean-sail** (not the generated model).
2. **Use the free/interaction-monad Sail export** (like Rocq): `MemRead`/`MemWrite`/
   `Barrier`/… as effects the Iris interpreter interprets. First-class
   interposition; the natural substrate for relaxed/shared memory. Requires the
   Lean Sail backend to *emit* that form — currently lean-sail provides only the
   EStateM monad (the concurrency-interface *types* exist, but the monad is
   concrete state). To be confirmed/requested with the Sail devs.

This fork gates the foundational layer and is the first decision to settle.

## Plan of attack (phased)

**Phase 0 — toolchain + dependency integration (in progress).**
Stand up the lake workspace on v4.31.0; build iris-lean; compile a MoSeL smoke
proof. Then vendor + bump `lean-sail` and a minimal slice of the model to v4.31.0
and get *something* from the model type-checking in-tree (resolve the 4.29→4.31
gap). Decide vendor-vs-git for the (172k-line) model.

**Phase 1 — settle the memory substrate** (the fork above), then build the
foundational layer:
- `Lang`: the Iris `Language` instance — `Loop` expression, `mstate` (= the sail
  state, possibly enriched), `primStep Loop σ Loop σ' := (try_step 0 false).run σ = .ok _ σ'`.
- `Ptsto`: the GS bundle (`InvGS_gen` + two `genHeapGS`: registers, memory),
  `↦ᵣ` / `↦ₘ` points-to, the `stateInterp` bridging gen_heap auth maps to the
  sail state's `regs`/`mem`, plus the `valid`/`update` lemmas. Mirror HeapLang's
  `PrimitiveLaws.lean`.
- `Step`: the one-step WP rule via `wp_lift_step` (the analog of Rocq
  `wp_exec_step`). With EStateM this is mostly: reduce `try_step.run σ` and relate
  the resulting state to the points-to updates.

**Phase 2 — per-opcode WP lemmas.** Reduce `try_step`/`ext_decode` symbolically
(`simp [simp_sail]` + concrete encodings). Validate the "decode wall" reduces
performantly in Lean (the original motivation for leaving Rocq). Start with
`auipc` and `ld` (the kernel's first two instructions), then grow the opcode set.
Much of the Rocq ~19k-line per-opcode bulk should shrink where Lean reduction does
the work Rocq had to do by hand.

**Phase 3 — kernel image + boot capstone.** Regenerate the kernel dump as Lean
data; port `KernelBoot` (`wp_kernel_first_two`) and the `WpStart*` chain.

## Pinned dependency revisions

- iris-lean: `3877dbeccd1b0545c5be7ef73318e8c86acf79ab` (toolchain v4.31.0)
- lean-sail: `79b4d08505af29d88b3918f32d29840fae1fa191` (branch `v4`, toolchain v4.29.0)
- sail-riscv-lean: opencompl `main` (toolchain v4.29.0)
