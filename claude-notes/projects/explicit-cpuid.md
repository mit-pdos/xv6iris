# Project: the explicit-CPUID refactor

GOAL: remove the ambient `CpuId` from WP statements, so a step's continuation
is about the hart execution RESUMES on rather than (silently) the hart it
started on. Started 2026-07-30; design approved, prototype in progress on
branch `explicit-cpuid`.

## The bug in the current shape

`RiscvLang.v` has `Notation Loop := (LoopE cpu_id)`, so every WP — leaf and
whole-function alike — reads its hart out of the ambient `CpuId` instance.
Pre- and postcondition therefore share one hart *by construction*. That is
false for this kernel: with interrupts enabled a timer trap runs `kerneltrap`
→ `yield()` → `sched()`, and any hart's scheduler may pick the proc back up.
`swtch` does not save `tp`, so the thread resumes with the resuming hart's.

It is invisible today only because `kerneltrap` is an assumed axiom. The
concrete carrier of the falsehood is `IntrDefs.intr_handler_spec`, whose
continuation hands back the SAME `gpr_file m` at the SAME hart — and
`WpSmodeIntr`'s engines absorb an arbitrary interrupt at EVERY step. So the
assumption is baked into every single-instruction leaf, not just the
whole-function specs.

## The shape (validated by compiling, see "Validated mechanisms")

**Keep `Notation Loop`, keep every resource statement byte-for-byte. Bind the
hart per statement, and let the continuation REBIND it.**

```coq
Lemma wp_add_s_sconf `{CID : CpuId} … :        (* NOT a section Context *)
  …
  sie_cap_gpr γ m n b -∗
  pc_is pc -∗ instr pc false (RTYPE …) -∗
  wp_next γ b (λ (CID : CpuId) (γ : gname),    (* rebinds BOTH names *)
    sie_cap_gpr γ (<[Regidx rd := regval_into_reg wval]> m) n b -∗
    pc_is (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
```

Everything inside the λ — `sie_cap_gpr`, `pc_is`, `Loop` — resolves to the
REBOUND `CID`/`γ` with no annotation, because instance resolution is
positional. `iApply` then fixes a leaf's `CID` by unifying its conclusion
`WP (LoopE ?c)` against the goal's `WP (LoopE h)`, so it does not even rely on
instance-search order.

Four consequences, in decreasing order of how much they cost:

1. **`Context \`{CID : CpuId}.` goes away only where a file applies its OWN
   lemmas at a migrated hart** — `Proof*.v` files split into block lemmas, and
   the engine's `iLöb`. MEASURED, not assumed: a `wp_next b (fun (CID : CpuId)
   => …)` lambda parses fine inside a section that already has `Context
   \`{CID : CpuId}`, and — checked by `reflexivity` against the fully
   `(CID:=h)`-annotated form — its body really does mean the LAMBDA's hart.
   (Only a `∀ (CID : CpuId)` in a *definition's binder list* collides, with
   "CID is already used"; that is what forced `wp_next` into its own file.)
   So the ~200 `Wp*`/`Spec*` files keep their section variable and are spared
   the per-lemma binder churn. Where the binder IS needed it must stay
   *implicit* — that is what leaves ~1200 positional call sites' argument lists
   unchanged — and it retires the `sched-hart-generic.md` extraction recipe.
2. **Name the rebound binder `CID`, not `h`.** Then `CID` always means "the
   hart you are on right now" and a postcondition cannot name the entry hart by
   accident. Where one genuinely must (none found so far), name the outer
   binder `CID0` on that statement.
3. **`tp` is pinned to the hart, not carried in the map** (`HartTp.v`).
   `sie_cap_gpr γ m av b` owns `gpr_file (tp_pin m)`, so a migration hands back
   the SAME `m` at the new hart and register towers do NOT grow a layer per
   instruction. Reads go through `rget m k` (correct at every register incl.
   tp, so no `rs <> Rtp` premises and no special tp-read leaf family for the
   inlined `mycpu`); writes need `rd <> Rtp`, which rides inside `rd_ok rd`
   REPLACING `rd <> csp_rs1` in the same premise slot. Discharge with
   `ltac:(rdok)`. `callee_saved` drops tp; `callee_saved_notp` /
   `is_cs_idx_notp` / the `⌜mf !!! x4 = cid_word_of h⌝` premises / `sched_vc_at`
   / `panic_wp_any_at` all collapse.
4. **The SIE state becomes an INDEX, `sie_arm γ b`** (was an internal
   disjunction), so a leaf statement can say the one thing a caller needs.

## `wp_next`: how "interrupts off ⟹ same CPU" is stated

The load-bearing case is `push_off(); c = mycpu(); c->noff++` — code that
disables interrupts, reads `tp`, and expects the answer to stay valid. Handled
by ONE combinator, the only place that names the hart we came from:

```coq
Definition wp_next `{CID0 : CpuId} (γ0 : gname) (b : bool)
    (K : forall (CID : CpuId), gname -> iProp Σ) : iProp Σ :=
  (∀ (CID : CpuId) (γ : gname),
     ⌜ b = false -> (cpu_id : CPU) = (CID0 : CPU) /\ γ = γ0 ⌝ -∗ K CID γ)%I.

Lemma wp_next_intro : (∀ CID γ, K CID γ) -∗ wp_next γ0 b K.   (* any b *)
Lemma wp_next_off   : wp_next γ0 false K ⊣⊢ K CID0 γ0.
```

`wp_next_off` is why **an interrupts-off or M-mode contract is stated exactly
as it is today, with no binder at all** — which is the original ask for the
M-mode boot arm.

Why a pure conditional equality and not something prettier:

- **Branching the quantifier** (`if b then ∀ CID γ, K else K cpu_id γ0`) gives
  cleaner goals at concrete `b`, but breaks every `b`-GENERIC contract
  (`memmove`/`strlen`/`copyin` are called both with interrupts on and off):
  providing *or* consuming it at abstract `b` forces `destruct b` and two proof
  paths — and what the `false` branch then needs is exactly this equality. It is
  this option plus a case split.
- **A ghost recording which hart pinned the SIE-off arm** does not close: the
  caller can only tie the returned ghost back to its own if it already knows no
  interrupt fired, which is what it is trying to learn.
- A `□` wand `ghost_var γ … '0' -∗ ⌜CID = CID0⌝` is NOT provable in the `b=true`
  arm: `□` demands it hold in all future states, and a later `'0'` does not
  contradict an earlier `'1'`.

`γ` is quantified alongside `CID` because the SIE ghost is per-hart
(`sched-hart-generic.md` S1): a migration hands back the resuming hart's.

## Validated mechanisms (all compiled, scratchpad `ShadowTest*.v` / `NextTest.v`)

- A later-introduced `h : CpuId` **shadows** the section instance: `cpu_id`
  resolves to `h`. Rebinding the same name `CID` works too, with no warning.
- `body_means : body Φ x ⊣⊢ <fully (CID:=h)-annotated form>` closes by
  **`reflexivity`** — the unannotated statement is definitionally the annotated
  one, for both the `h` and the shadowed-`CID` spelling.
- Chaining two leaves with `iIntros (CID1)` between them resolves the second at
  `CID1` with **no annotation** — but only once `CID` is a per-lemma binder;
  with a section `Context` the second `iApply` fails ("cannot instantiate"),
  which is the known section-variable restriction.
- `leaf_means` (same, through `wp_next`) closes by `reflexivity`; the
  `wp_next γ0 false` consumer collapses the hart back to `CID0`.

## Prototype status (branch `explicit-cpuid`)

Landed and compiling: **`HartTp.v`** (Rtp / `cid_word_of` / `tp_pin` / `rget` +
`rget_ne`, `rget_tp`, `tp_pin_id`, `tp_pin_upd`), **`WpNext.v`** (`wp_next`,
`wp_next_intro`, `wp_next_off`, `wp_next_trans`, `Ltac wp_next_chain`),
**`IntrDefs.v`** (`sie_arm γ b`, `sie_cap … b`, `sie_cap_gpr … b` over
`gpr_file (tp_pin m)`, `rd_ok`; every `sie_cap*` lemma re-indexed, none
weakened, none found false), and **`ProtoCpuid.v`** — the consumer-side demo.
No admits, no new axioms (`Print Assumptions` on the demo lemmas shows only the
three pre-existing Sail model axioms).

`ProtoCpuid.v` takes the leaf as a section `Hypothesis` stated exactly as
`WpSconfAlu.v:422` will state it, and proves:

- `demo_intr_off` — `add a5, zero, tp ; add a5, a5, a5` at `b = false`. The tp
  read is just the leaf's value premise closed by `rget_tp`; **no special
  tp-reading leaf family is needed**. `rewrite wp_next_off` collapses the hart
  at each step, so the continuation is stated at `CID0` with no binder and the
  `instr` fact derived before step 1 is still usable at step 2. This is the
  `push_off(); c = mycpu()` case.
- `demo_b_generic` — the same stretch with `b` a parameter. **No `destruct b`
  anywhere**: each step yields a conditional equality, `wp_next_chain` composes
  them, and that discharges the function's own `wp_next` obligation.

Two things the prototype corrected:

- **State `wp_next`'s pure fact at the BARE binder** (`(CID : CPU) = (CID0 :
  CPU)`), not via `cpu_id`. Written through the projection the accumulated
  facts read `@cpu_id CID2 = CID1`, mixing projected and bare spellings, and
  `congruence`/`eassumption` then fail to chain them.
- `wp_next` cannot live in a section that fixes `CpuId` — Rocq refuses to
  rebind a section variable's name ("CID is already used"), which is exactly
  the shadowing everything relies on. Hence `WpNext.v`.

Everything above `IntrDefs.v` is currently broken, by design: that is the
Stage-1 sweep (1111 `sie_cap_gpr` sites, 4156 leaf applications, 321 files with
a `Context \`{CID : CpuId}` to retire).

## The SIE ghost is CANONICAL per hart (approved, in progress)

`riscvGS` gained `sie_name : CPU -> gname`, the exact twin of `strans_name` and
for the same reason (mstatus.SIE is a per-hart register). With
`sie_gname := sie_name cpu_id`, the WHOLE sconf tier drops its `γ` argument:
`sconf`, `sie_cap`, `sie_cap_gpr`, `sie_arm`, `intr_count`, `intr_off_tok`,
`intr_inv`, `intr_handler_avail`, `intr_restore`, `intr_config`. `wp_next` then
quantifies only the HART, and every parking contract's `∀ h g` collapses to
`∀ h`.

**The one ghost that stays an explicit parameter** is the per-trap one
`ProofKernelvec.v:1572` mints: during a trap the live SIE bit is 0 while the
interrupted thread's half still reads 1, so the two cannot share a name.
`wp_kernelvec` takes a raw `ghost_var γ (1/2) _` (never `sconf γ`), so it is
unaffected by the tier going γ-free.

Allocation is a three-piece (1/2 tie + 1/4 kernel token + 1/4 invariant)
per-hart mint at adequacy — the `ghost_var_alloc_halves_cpus` induction with
`sie_ghost_alloc`'s split substituted. **Proven standalone** (scratchpad
`SieAlloc.v`); it belongs in `RiscvAdequacy.v`'s `reg_alloc` section next to
`ghost_var_alloc_halves_cpus`, and `RiscvGS`'s one constructor site
(`RiscvAdequacy.v:324`) takes the resulting `f` as the new field.

```coq
Lemma ghost_var_alloc_sie_cpus {A} `{!ghost_varG Σ A} (a : A) (cs : list CPU) :
  NoDup cs ->
  ⊢ |==> ∃ f : CPU -> gname,
    [∗ list] c ∈ cs, (ghost_var (f c) (1/2)%Qp a ∗ ghost_var (f c) (1/4)%Qp a ∗
                      ghost_var (f c) (1/4)%Qp a).
```

Why it matters beyond the argument count: it is what makes the Stage-2
hart-generic handler fact statable *without* a recursive definition —
`□ ∀ c : CPU, ∃ h, intr_inv (CID := c) h` is persistent and hart-independent,
so it survives a trap for free and `intr_handler_spec` never has to return it.

## What the refactor has caught so far

**`cpuid()` / `mycpu()` were silently over-specified.** Their contracts said the
returned id is the ENTRY hart's. The `tp` read happens mid-function, so with
interrupts enabled that is simply false — the value is the id of whichever hart
ran that one instruction. xv6 documents the requirement in a comment
("Interrupts must be disabled", proc.c above `mycpu`); the refactor turns it
into a premise, and both contracts are now stated at `b = false`. Under the old
ambient-`CpuId` shape this was not statable, let alone checkable.

This is the refactor paying for itself: the falsehood was invisible before, and
would have stayed invisible until `kerneltrap` was proved.

## Staging (the key economy)

**The new leaf statements are strictly WEAKER than the current ones** — a
`∀ CID γ` continuation is a stronger obligation on the caller — so they are
derivable from the existing proofs by instantiating at the current hart. That
splits the work:

- **Stage 1 (pervasive, mechanical).** Restate every leaf and every contract in
  the new shape; re-thread consumer proofs (`iIntros "Hcg Hpc"` →
  `iIntros (CID γ Hs) "Hcg Hpc"`, tactic swaps in the `rd_ok` / value-premise
  slots). Leaf proofs are wrappers over the existing ones. Tree stays green;
  no new axioms needed for this stage.
- **Stage 2 (localized, deep).** Make the migration REAL: `intr_handler_spec`'s
  continuation quantifies `(CID, γ)`, and `WpIntrInv.wp_exec_step_intr`'s `iLöb`
  is taken over a hart-generic statement so the post-trap arm can re-enter the
  IH at the resuming hart. Only the engine files change — every leaf statement
  and consumer proof from Stage 1 is already the right shape.

## Stage-2 finding: the engine needs canonical per-hart ghost names

`wp_exec_step_intr` (WpIntrInv.v:224) is an `iLöb` that, on the interrupt arm,
applies `intr_handler_spec` and re-enters the IH. Making that arm resume on a
different hart runs into a definitional cycle:

- the engine's Löb needs `intr_inv γ' handler'` at the NEW hart, but `intr_inv`
  is hart-specific (its invariant body owns that hart's `stvec ↦ᵣ`), so the
  persistent copy it started with is useless there;
- having the handler RETURN it makes `intr_handler_spec` recursive
  (`intr_inv`'s body contains `□ (⌜b='1'⌝ -∗ intr_handler_spec handler)`),
  which needs Iris's `fixpoint` and a contractivity argument.

The cut: give the SIE ghost a **canonical per-hart name** `sie_name : CPU ->
gname`, exactly mirroring the existing `strans_name` (IntrDefs.v:461), and
carry a hart-generic **persistent** `□ ∀ c : CPU, ∃ h, intr_inv (CID:=c) h`.
Persistence is what makes it survive the trap for free, so the handler spec
never has to mention it and the recursion disappears. Canonical names also make
`γ` determined by the hart, which is a simplification the `γ` parameter on ~200
contracts could later be retired against.

Open, deliberately deferred to when `kerneltrap` is actually proven: **what
else has to cross the migration.** `cpu_own γ n eb p C` (CpuOwn.v:49) is
`cpus[c]`'s own fields (`a_cpu_noff/int/proc cid_word`) plus the per-hart SIE
ghost, and a caller holds it across interrupts-enabled instructions. Today
`intr_handler_spec` returns only the register file and config, so nothing hands
`cpu_own` back at the new hart. The natural home is `sie_arm`'s `b = true` arm
— it already holds exactly the resources that exist only while interrupts are
enabled (the trap-scratch CSRs), and it already crosses inside `sie_cap`; the
`b = false` side is where push_off/pop_off hand the bundle to the code. That
choice should be made against `kerneltrap`'s real contract, not guessed.
