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
  `wp_myproc_sconf` axiom out of `WpSconfWakeup`, because callers' *statements*
  mention them.
- Spec files must not `Require Export` (the ssreflect-`by` propagation hazard in
  [`code-organization.md`](code-organization.md) applies here too).

## Adding a new function

Write `Spec<F>.v` first (interface + notation), then `WpSconf<F>.v` as a functor
over the callees you need, then the one-line `Link<F>.v`, and add all three to
`_CoqProject`. Only lemmas another file consumes belong in the `Module Type`;
everything else stays hidden behind the seal.
