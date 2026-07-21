# Design: function specs as module types (build decoupling)

A whole-function WP proof must NOT depend on its callees' *proofs* — only on
their *specs*. Otherwise the build serializes along the kernel call graph and no
amount of `-j` helps (the build is critical-path bound, not core bound; see
[`../optimization.md`](../optimization.md)).

Every whole-function proof under `iris/` is in this shape. Keep new ones in it.

## The three files

For each kernel function `F` (`Spec<F>.v`, `WpSconf<F>.v`, `Link<F>.v`):

**`Spec<F>.v`** — the public interface, stated once, plus the symbol-address
notation and any pure spec vocabulary:

```coq
Notation AQ := KernelSyms.acquire.

Definition wp_acquire_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) … (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  … -∗ WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ACQUIRE.
  Parameter wp_acquire_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) … (av : nat),
      wp_acquire_sconf_body γ root_ppn … av.
End ACQUIRE.
```

It requires only the definitional layer — never a `WpSconf*` proof file. A
callee's proof-file require becomes that callee's `Spec` file. Spec files
compile in ~2 s.

**`WpSconf<F>.v`** — the proof, a *sealed functor* over its callees' interfaces.
The lemma keeps its original header and concludes with the `_body`:

```coq
Module AcquireProof (Mycpu : MYCPU) (Holding : HOLDING) (PushOff : PUSHOFF) : ACQUIRE.
Section WpSconfAcquire.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_acquire_sconf (γ : gname) (root_ppn : mword 44) … (av : nat)
    : wp_acquire_sconf_body γ root_ppn … av.
  Proof.
    cbv beta delta [wp_acquire_sconf_body].
    intros pcE lk0 a_cpu … Hnotmine Hal0 Hav.      (* the original first tactic *)
    …
End WpSconfAcquire.
End AcquireProof.
```

Callee applications go through the functor parameter
(`Holding.wp_holding_lockinv_s_sconf`); nothing else in the proof changes.
`Section` inside `Module` is fine, and one module may span several sections.

**`Link<F>.v`** — one line, the only file where a proof meets its callees'
proofs:

```coq
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecAcquire SpecMycpu SpecHolding SpecPushOff.
Require Import LinkMycpu LinkHolding LinkPushOff WpSconfAcquire.

Module Acquire := AcquireProof Mycpu Holding PushOff.
```

## Why this exact shape

- **Functor application is free.** A body of 800 opaque lemmas applies in
  0.28 s, the same as a body of 100 — Rocq substitutes, it does not re-typecheck.
- **Seal with `:`, not `<:`.** Sealed, the link `.vo` is ~4 KB and the body is
  pruned; unsealed it carries a full substituted copy. Sealing also hides the
  proof file's internal helpers — a helper a *caller* needs is misfiled and
  belongs at a lower altitude (see [`code-organization.md`](code-organization.md)).
- **The statement lives only in the `_body` `Definition`.** Never spell it out
  inside `Module Type` — it would be duplicated between signature and proof and
  the two would drift.
- **The `Parameter` restates the binder *list*** (not the statement). That
  duplication is load-bearing: Rocq reads argument scopes and implicit-argument
  status off the head constant's type. A nullary `Definition f_spec := ∀ …` hides
  the binder types behind a constant, so `(K - 2)` at a call site parses in
  `Z_scope` instead of `nat_scope` and `{dqc : dfrac}` stops being implicit.
  Restating the binders keeps every existing call site working untouched.
- **`cbv beta delta [f_body].` — not `intros`, `hnf` or `unfold`.** The goal is
  `f_body args`; head reduction *zeta*-reduces the statement's `let`-chain away,
  so the proof's original `intros pcE lk …` would bind hypotheses instead of the
  lets and fail with "No product even after head-reduction". `cbv beta delta`
  does delta on that one constant plus beta, leaving the lets intact, so the
  original tactic script runs unchanged.

## Thin initlock wrappers: one proof, one instance per function

Three functions in the image have a body that is exactly `initlock(&L, "name")`:
`printkinit` (0x80000862), `trapinit` (0x80002402) and `fileinit` (0x80003f94).
gcc compiles all three to the SAME thirteen instructions (the standard 16-byte
frame, two auipc/addi pairs materializing the two arguments, `jal initlock`, the
epilogue), differing only in the entry address and the three relocated
immediates. So there is ONE proof and each member instantiates it — do NOT clone
the straight-line script. **All three are proved and the family is closed** —
there is no fourth member to add, so a new function needing this shape would
have to come from an upstream source change.

`consoleinit` is a near-miss worth not chasing: its first nine instructions are
this pattern, but it continues into `uartinit` and the `devsw[]` writes. The
wrapper owns the epilogue and returns, so sharing with `consoleinit` would mean
splitting prologue-through-jal into a separate piece — not what this shape is.
The other nine callers of `initlock` (kinit, procinit, binit, iinit, initlog,
initsleeplock, uartinit, pipealloc, virtio_disk_init) are unrelated.

- **`SpecInitlockWrapper.v`** — `ilw_code F uname ulk iname ilk j` is that
  thirteen-instruction pattern at entry `F`; `wp_initlock_wrapper_sconf_body` is
  the spec: the usual sconf / `sie_cap_gpr` / `callee_saved` frame, the lock's
  three struct fields in raw and back initialized, plus four pure premises —
  `F+0x1c` is 2-byte aligned, and what the two auipc/addi pairs and the jal
  resolve to (`… = name`, `… = lk`, `… = mword_of_int KernelSyms.initlock`).
- **`WpInitlockWrapper.v`** — `InitlockWrapperProof (Initlock : INITLOCK)`.
- A member `F` supplies only: its `Wp<F>Decode.v` (the shared `mdec_*`
  compressed templates plus the five base words carrying its own immediates)
  ending in an `<f>_code : kernel_text -∗ ilw_code …` bundle; a `Spec<F>.v` in
  the usual shape; and a `WpSconf<F>.v` that is one `iApply` — `Module ILW :=
  InitlockWrapperProof Initlock.` inside the function's own functor, four
  `ltac:(apply bv_eq; vm_compute; reflexivity)` relocation discharges, and
  `iApply (<f>_code with "Htext")`. ~60 lines instead of ~250.

### Proving a whole function over a SYMBOLIC entry address

The wrapper is the first whole-function proof whose entry `F` is a variable, so
none of the usual `vm_compute` address steps apply. What replaces them:

- **pc stepping** — `pc_step F a n b : a + n = b → add_vec_int (mword_of_int
  (F+a)) n = mword_of_int (F+b)` (WpInitlockWrapper.v, over `avi_mword` in
  RiscvExtras.v). The premise is `eq_refl` at every call site.
- **returning from a call** — `jalr_ret_id` (AlignBits.v): jalr's mandatory
  bit-0 clear is the identity on an address whose low bit is already clear, so
  one 2-byte-alignment premise replaces the concrete proofs' `vm_compute`.
- **Any leaf premise mentioning a computed ADDRESS must be discharged from a
  relocation hypothesis, never by `vm_compute`** — `wp_jal_s_sconf`'s
  target-alignment premise becomes `ltac:(rewrite Hjrel; vm_compute;
  reflexivity)`. A `vm_compute` on a symbolic address does not fail fast, it
  hangs (the symptom is a `coqc` that sits on one `iApply` for minutes).
- The first instruction must sit at `mword_of_int F`, **not** `mword_of_int
  (F + 0x00)`: `Z.add F 0` is stuck on a variable, so the two never unify.

## memset: one general spec, page/walk as instances

`memset` has an extra layer because its whole-function spec is used at more than
one shape. The external contract is **`SpecMemset`** (`Module Type MEMSET`,
`wp_memset_sconf`): memset of an ARBITRARY `len`-byte array at base `p`, stated
over the per-byte buffer `[∗ list] j ∈ seq 0 len, (pa_add p j) ↦ₘ …` (in→`olds`,
out→`cbyte`) plus `callee_saved`, with preconditions `0 < len`, `len < 2^32` (the
source's `(unsigned int)n` count truncation — a `slli/srli`-by-32 round-trip,
identity below 2^32; see `slli32_srli32`) and `uint p + len < 2^64` (no address
wraparound; see `ms_cmp_bound`, the `len`-general `ms_cmp_page`). It is proven in
`WpMemsetArray.v` as a functor `MemsetArrayProof (Memset : MEMSET_PARTS)` composing
the piecemeal prefix/loop/suffix.

Those piecemeal parts are **`SpecMemsetParts`** (`Module Type MEMSET_PARTS`,
`wp_memset_prefix/loop/suffix_sconf`) — NOT the external spec; only
`WpMemsetArray` consumes them. (Historically `SpecMemset` held the parts; it is
now `SpecMemsetParts`, and the general spec took the `SpecMemset` name.)

Both narrower memset users are **instances of the general spec at `len = 4096`**,
each a functor over `MEMSET` that bridges its own buffer abstraction around
`wp_memset_sconf`: `WpSconfMemsetPage` (`page_own p` in and out, contents
forgotten) and walk's `wp_memset_page_zero_sconf` (`page_own p` in, the written
`cbyte` buffer kept). Neither re-composes prefix/loop/suffix. This also lifted
the ~20 s inline memset composition out of the `WpSconfWalk` critical-path file
into the separately-compilable `WpMemsetArray`.

## Gotchas (all hit in practice)

- **The spec's binder list must mirror the proof file's `Context` exactly.** A
  missing class (e.g. `!lockG Σ` for anything mentioning `is_lock`) reports as
  *every* class failing to resolve — `riscvGS0`, `sieG0`, `CID`, `LookupTotal`,
  … — because Rocq runs typeclass resolution as one search and reports all
  pending evars when it fails. Read past the noise: the culprit is the class you
  did not bind.
- **Do not carry a `let` the statement never uses.** A `_body`'s let-chain is
  part of how the spec reads, so a binding that no proposition mentions is noise
  — delete it and `pose` it in the proof if the script wants the name. (The
  `sp0 := m !!! Regidx csp_rs1` bindings were exactly this: fossils of the
  pre-`sie_cap_gpr` shape, where the spec still carried an explicit
  `stack_own (pa_stk sp0 kv_frame_slots) K` conjunct.) If a `let` *is* used but
  its type cannot be inferred, annotate it (`let sp0 : mword 64 := …`) — a
  `Definition` body, unlike a `Lemma` statement, has no goal to pin the evar.
- **Arguments consumed from *inside* the statement still lose scope.** The
  `Parameter`'s binders only cover the header; a numeric argument that the
  statement itself quantifies needs an explicit mark (`4096%nat`). Two such
  sites exist, both feeding `wp_memset_loop_sconf`.
- **`Link<F>.v` must require `RiscvLang RiscvPtsto SmodeCore` itself.** `Require
  Import Spec<F>` does not transitively put `riscvGS`/`sieG`/`CpuId` in scope,
  and backtick generalization then silently invents *fresh binders with those
  names* rather than erroring — the symptom is a mismatch whose expected type
  reads `forall (riscvGS : ?T -> Type) (Σ : ?T) …`.
- **Symbol notations (`AQ`, `HD`, `MS`, …) live in the Spec file, not the proof
  file**, so a caller that needs one gets it from `Require Import Spec<F>`
  (`Import` is not transitive, so it must require the Spec directly).
- **Pure spec vocabulary moves down into the Spec file.** `PGSIZEv`,
  `negPGSIZEv` and `prun` moved out of `WpSconfFreerange`'s section, and the
  `wp_myproc_sconf_any` axiom out of `WpSconfWakeup`, because callers' *statements*
  mention them.
- Spec files must not `Require Export` (the ssreflect-`by` propagation hazard in
  [`code-organization.md`](code-organization.md) applies here too).

## Adding a new function

Write `Spec<F>.v` first (interface + notation), then `WpSconf<F>.v` as a functor
over the callees you need, then the one-line `Link<F>.v`, and add all three to
`_CoqProject`. Only lemmas another file consumes belong in the `Module Type`;
everything else stays hidden behind the seal.

Before writing a straight-line body, check whether `F` is an instance of a shape
that is already proved — a body that is just `initlock(&L, "name")` is a member
of the thin-wrapper family above and needs no proof of its own.
