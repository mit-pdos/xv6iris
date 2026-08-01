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

## APPROVED: cpu_own rides in the SIE arm when interrupts are enabled

The blocker found at ~100 files in: a leaf's `wp_next` does not carry
`cpu_own`, so a caller holding it across an interrupts-ENABLED instruction is
stuck — the continuation hands back a fresh hart and nothing rebinds
`cpus[c]`'s cells there. Confirmed independently in five proofs
(`kvmmap`, `kvminit`, `kvminithart`, `uvmcreate`, `trapinithart`) and it
affects the 39 `b`-generic contracts that thread `cpu_own` (82 mention it).

Note the gap is NARROWER than it first looked: function CONTRACTS already
cross correctly, because their `cpu_own` input sits outside the `wp_next`
lambda (entry hart) and their output inside it (exit hart) — `SpecAcquire` is
the worked example. Only the LEAF level lacks the vehicle.

**The fix (approved): the `b = true` arm of `sie_arm` holds the per-cpu
bundle.** It already holds exactly the resources that exist only while
interrupts are enabled (the trap-scratch CSRs), and it already crosses inside
`sie_cap` — so a leaf's continuation returning `sie_cap_gpr m' av b` at the new
hart re-delivers that hart's cpu cells for free, with NO growth in any leaf's
footprint. It also matches what the C actually does: a thread only touches
`c->noff` / `c->proc` with interrupts disabled, which is why `push_off` exists.

### The sub-decision this forces, and it must be made deliberately

`cpu_own n eb p C` is parameterized by the current proc `p` and the context
slot `C`, but `sie_arm b` has no such parameters. Three ways out:

1. **Index the arm** — `sie_arm b p C`, hence `sie_cap m av b p C` and
   `sie_cap_gpr m av b p C`. Preserves `p`'s identity across the crossing
   (correct: `c->proc` is thread-dependent, the scheduler sets the new hart's
   to the same proc), at the cost of two more parameters on the tier's central
   bundle — and they are VESTIGIAL in the `b = false` arm, which is exactly the
   shape that made `kalloc_env`'s `tp` parameter noise.
2. **Existentially quantify `p` inside the arm.** No new parameters, but a
   caller loses the identity of its own proc across every enabled instruction,
   which breaks `myproc`'s postcondition and every contract naming `p`.
3. **Keep the arm payload-free and add an agreement ghost** tying `c->proc` to
   a thread-owned fragment, so the arm can hold `∃ p` while the thread retains
   `p`'s identity. No signature growth on `sie_cap_gpr`, one new ghost.

(2) is wrong. (1) is simplest but re-introduces the vestigial-parameter smell
this project just spent a commit removing. (3) is the cleanest shape and the
most work. DECIDE BEFORE IMPLEMENTING — this lands in the tier's central
definition and every contract above it.

## WHERE THE SWEEP STANDS (2026-07-31)

Committed and each verified by my own `coqc`, never by an agent's report:

| layer | done | notes |
|---|---|---|
| foundation | complete | `HartTp`, `WpNext`, `IntrDefs`, `RiscvPtsto`, `CalleeSaved`, `InstrBytes`/`KernelText` hart-free, engines, `RiscvAdequacy` |
| `Spec*` | 71 / 122 | |
| `Wp*` | 17 / 169 | most of the 169 are M-mode leaves needing NO change (interrupts off ⇒ same hart already correct) |
| `Proof*` | 14 / 109 | the consumer wave |
| `Link*` | 0 / 116 | functor instantiations; expected to need little |

IN FLIGHT: the `p`/`C` prototype on `IntrDefs`/`CpuOwn`/`push_off`/`pop_off` +
`ProofKvmmap`. **No consumer agent may run until it lands** — see the guide's
orchestration rule.

### Resumption order, once `p` has propagated

1. Propagate `p` into the `Spec*.v` files that the arity change breaks —
   `SpecPrintint`, `SpecConsputc`, `SpecPlicinit`, `SpecCpuid` were the
   confirmed casualties, expect more. This is the gate on everything else.
2. Resume the two waves that were killed mid-flight. Both are mechanical:
   printk/printint never inspect `p`, so it threads implicitly exactly as `CID`
   does, and only a helper lemma whose own statement mentions `sie_cap_gpr`
   needs it written out. `ProofPrintint.wp_printint_epi` already carries a
   validated partial port; several blocked `Proof*` files carry an in-file
   diagnostic comment at their exact failure point.
3. Then the remaining `Proof*`, largest last: `ProofPrintk` alone is 337 leaf
   applications, a third of the wave.

### THE TP-PREMISE SWEEP (53 files) — owed, and blocking

**53 `Spec*.v` files still carry a raw `⌜m !!! Regidx (mword_of_int 4) = cid_word⌝`
premise.** Under `tp_pin` that slot is unobservable, so the premise constrains
nothing — and `callee_saved` no longer carries tp to discharge it after an
opaque call, so it is not merely noise: it BLOCKS consumers. Confirmed blocking
`ProofUvmdealloc` (via `SpecUvmunmap`/`SpecUvmdealloc`) and forcing a `tp_pin`
re-tagging workaround in `SpecRelease`'s callers, which four agent groups
invented independently.

Why it was missed: the deletion rule was applied only by wave 2's first batch.
Every later brief said "mechanical arity propagation, do not restructure" — so
the batches correctly left them alone. Prompt design, not agent error.

The sweep: delete the premise, then delete the now-dead `tp_pin` re-tagging in
whatever consumers grew it. Deleting a PREMISE strengthens the contract, so it
is safe in the direction that matters; the risk is only that a consumer was
reading the slot, which should surface as a proof failure, not silently.

**Do it with NO consumer agents running** — it changes the wand-chain arity of
53 contracts.

### DEFERRED: the central fix for the conversion blowup

**Measured, diagnosed, and deliberately not done yet** — a local patch is in
place instead (`Local Strategy opaque [rget].` in `ProofVirtioDiskInit.v` plus
the `rgne` sweep it forces).

THE BUG. One `wp_cand_s_sconf` application took **400 s of a 421 s prefix**
(0.06 s before the refactor). Conversion unfolds the transparent register tower
through `rget → tp_pin → rf_upd` over a 24-link `pose`-chain. Making ANY ONE of
the three opaque collapses it to **0.08 s**. Depth is necessary: the same lemma
two links deep is 0.035 s.

RULED OUT by direct measurement — the inline `ltac:`, the statement's `let`,
the value being map-derived, a closed-literal `wval`, operands passed as
separate premises, `and_vec`, the symbolic `cid_word_of`, and `gpr_file`'s
32-way `rf_to_gmap` fold. **A `Strategy` LEVEL does nothing (level 1000 = 390 s);
only true opacity works.**

WHY IT IS LATENT EVERYWHERE: the trigger is `tp_pin`'s extra transparent layer
over a deep tower. There are 7 `let wval := … rget …` statements in
`WpSconfAlu.v` alone and ~25 more across `WpSconfLock` / `WpVirtioDev` /
`WpPlic` / `WpSmodeHalf` / `SpecUart`. Any of them can hit this at sufficient
depth.

THE CENTRAL FIX, when someone wants it: either a global
`Strategy opaque [tp_pin]` in `HartTp.v`, or seal `gpr_file (tp_pin m)` behind
a named opaque wrapper in `IntrDefs.v`. Either makes the failure mode
impossible tree-wide. THE COST is a mechanical sweep: every site that today
closes `rget M k` against `M !!! Regidx k` silently BY CONVERSION needs an
explicit `rgne`. Note also that opacifying all three of `rget`/`tp_pin`/`rf_upd`
additionally broke a `reg_neq` ("No primitive equality found") — prefer the
minimal opacity that works.

NOT worth chasing: `ProofPrintk` is +12 s / +13 %, a FLAT per-step tax from
`wp_next`'s binder (349 `iIntros` = +3.0 s, 91 `iSpecialize` = +1.4 s, +3.3 s
of `Qed`); `tp_pin`/`rget` contribute 0.95 s there. `Strategy`/opacity buys
nothing on that file (measured 102 s vs 100 s). Recovering it would mean
changing the `wp_next` shape — a spec decision, not a tuning knob.

### Known spec fixes still owed

- `SpecMemsetParts`'s loop premises need `Regidx ra5 <> Regidx Rtp` (its other
  operands are excluded from sp/ra1/ra4 but not tp, so `rd_ok` cannot be
  derived). Real bug, blocks `ProofMemset.wp_memset_loop_sconf`.
- ~~`VcGenS`'s symbolic executor still lacks the tp guards that `WpSconfVc` got
  locally.~~ **DONE.** `VcGenS.is_tp` / `is_tp_false` now live in `VcGenS.v`,
  and `vc_step_s` rejects EVERY opcode whose variable register operand
  (source or destination) is tp — `VScaddi`/`VScaddi4spn`/`VScldsp`/`VScaddiw`
  on `rd`, `VScsdsp` on `rs2`, `VSclw`/`VSld` on `rd`+`rs1`,
  `VScsw`/`VSsd` on `rs1`+`rs2`; `VScaddi16sp` is sp-only and needs none.
  `WpSconfVc` was simplified onto it: its local `rd_tp_bad`/`is_tp` are gone,
  replaced by `rd_sp_bad` (the sp half, which is genuinely this tier's — the
  sie capability is keyed on sp) plus `rd_ok_of_guards`, which composes the
  two halves back into `IntrDefs.rd_ok`. The two store shapes `VScsdsp`/`VSsd`
  keep an explicit `is_tp` because `vc_step_sp_s` implements them itself (the
  frame ledger) instead of delegating. Tightening only REJECTS more programs:
  every consumer (`ProofKernelvec`, `WpPopOff`, `WpUartPutcSyncFull`, and the
  13 `Proof*` users of `wp_vc_block_s_sconf`) still runs its block.
- Same class, still owed — a leaf contract that reads a register at a VARIABLE
  index through the raw map instead of `rget`, at the PINNED (`sie_cap_gpr`)
  altitude. `SpecUart` was one (fixed: its three `_body` definitions now spell
  the base as `rget m rs1` and the store byte as `rget m rs2`, which is what
  unblocked `ProofUart.v`). A tree-wide sweep finds 11 more declarations / 18
  sites, all in files that are not yet ported (no `.vo`), so all latent:
  `ProofBrelse.wp_csdsp_au_s_sconf` (rs2), `ProofVirtioDiskInit`
  (`wp_vdi_sw`/`_sw_reset`/`_flip`/`_lw`, 7 sites), `ProofVirtioDiskIntr`
  (`wp_vt_lw_dev`/`wp_vt_sw_dev`/`wp_vt_lhu_used_idx`/`wp_vt_lw_used_elem`,
  5 sites), `SpecMemsetParts.wp_memset_loop_sconf_body` (the bullet above),
  and `WpUartgetc.wp_uartgetc_inline` (rs_lsr/rs_rhr). Everything else that
  greps is either the raw-`gpr_file` M-mode / pre-sconf `WpSmodePt*` tier
  (where the raw read is correct by construction), a map-to-map agreement
  fact, `HartTp.rget` itself, or `IntrDefs.sie_cap_gpr_x0` (guarded by
  `uint i = 0`).
- `kvminithart` / `trapinithart` / `plicinithart` / `plic_claim` are boot- or
  trap-context only and should be stated at `b = false` rather than
  `b`-generic; that is what blocks four of their proofs.

## SURPRISES — the checkpoint

Everything here cost real time to learn. Grouped by whether it is about the
LOGIC, about Rocq/Iris MECHANICS, or about ORCHESTRATION.

### About the logic

1. **`∃ C, R ∗ C ⊣⊢ R`.** "Existentially quantify the context payload inside the
   arm" is a NO-OP — take `C := emp`. An existential `C` *is* "the arm owns no
   `C`", not a way to carry one. So the honest answer was to leave `C` where it
   was, as a caller frame. I asked for something vacuous and an agent caught it.
2. **A thread INVARIANT can just be a parameter.** `p` never changes from a
   kernel thread's point of view — not across migration, interrupt state, or
   push_off depth — so it needed no ghost and no transport, just a binder. I had
   been designing an agreement ghost for it.
3. **`n` and `eb` came for free.** Ghost agreement pins `n = 0 ∧ eb = true` in
   the enabled arm, and `intr_count 0 true` IS the eighth the arm already held —
   so absorbing `cpu_own` changed the arm's *ghost* content not at all.
4. **`cpu_own`-in-the-arm CREATED a new gap.** The arm now holds both eighths,
   so a flip leaf asking for a separate `intr_count` alongside the bundle cannot
   be satisfied by anyone. Proven, not guessed:
   `sie_arm true p ⊢ sie_arm true p ∗ intr_count 0 true` is unprovable. A design
   fix can manufacture its own downstream gap.
5. **Not every gap wants a transport lemma.** `locked_transport` (by analogy
   with `cpu_own_transport`) does not exist soundly: the hart sits inside an
   exclusive `excl_auth` fragment, and at both stop points the missing thing is
   a Coq-level `⊢` PREMISE, not a resource — a resource-consuming transport
   cannot discharge one. Pattern-matching on the shape of a previous fix is not
   the same as diagnosing what is missing.
6. **The refactor caught a real over-specification.** `cpuid`/`mycpu` claimed the
   returned id is the ENTRY hart's; the `tp` read happens mid-body, so that is
   false with interrupts on. xv6 already knew — `proc.c` says "Interrupts must
   be disabled." above `mycpu`. The refactor turned a comment into a premise.
7. **…but the obvious generalization of that was WRONG.** `myproc` reads a
   per-hart source mid-body (`c->proc`) and is still `b`-GENERIC, because it
   brackets its own push_off/pop_off. The test is what a function RETURNS —
   hart-dependent vs thread-dependent — not what it reads.
8. **`push_off` is not `b = false`.** It is the thing that MAKES `b = false`.
   Entry is generic.
9. **A flipping function has TWO indices** and they differ: the resource index
   (what SIE *is*) and `wp_next`'s (whether interrupts were enabled at ANY point
   DURING the call). `pop_off` is `false` in / `eb` out with `wp_next` index
   `eb`, because it re-enables at its LAST instruction. **Compiling cannot catch
   a wrong choice — at `eb = false` both spellings typecheck.**
10. **A meaningless premise cost 511 lines.** Deleting one vacuous tp premise
    removed 15 `tp_pin` re-tagging workarounds. Four agent groups had
    independently invented that same bridge. **When every consumer reinvents the
    same bridge, the contract is wrong, not the proofs.**

### About Rocq / Iris mechanics

11. **Instance shadowing is positional and total.** A rebound `CID` captures
    every resource in scope with ZERO annotation — verified by `reflexivity`
    against the fully-annotated form. This is what made the whole refactor cheap
    instead of a 1200-site annotation sweep.
12. **…but Rocq refuses to rebind a SECTION variable's name** ("CID is already
    used"), which forced `wp_next` into its own file.
13. **Yet a `fun (CID : CpuId) =>` LAMBDA inside such a section is fine.** The
    restriction is on definition binders, not lambdas — which is why ~200
    `Wp*`/`Spec*` files kept their `Context` and were spared the churn.
14. **THE VACUITY TRAP.** In `bi_scope` a `forall` extends MAXIMALLY, so an
    unparenthesised `∀` in a wand chain swallows the trailing `WP` and the
    contract becomes trivially provable. It compiles. The `Module Type` seal
    accepts it. Only symptom is a remote `iIntros` failure in another file.
    `tools/spec_vacuity.py` exists because of this.
15. **An `Ltac` defined inside a Section does not survive it**, and an Ltac body
    resolves literal hypothesis names at DEFINITION time.
16. **The transparent-tower conversion blowup.** One `iApply` took 400 s of a
    421 s file (0.06 s pre-refactor) because conversion unfolded
    `rget → tp_pin → rf_upd` over a 24-link chain. Making any ONE opaque
    collapses it to 0.08 s. **A `Strategy` LEVEL does nothing (390 s at level
    1000) — only true opacity works.** Eight alternative explanations were
    falsified by measurement.
17. **`rget` inside a `wp_next` lambda is a non-terminating `iApply`**, not an
    error — >10 minutes of silence. And it is silently the wrong hart even when
    it does work.
18. **`instr` / `kernel_text` were hart-free in substance already** — only a
    `∀ σ, mstate_interp σ` clause tied them. Quantifying the hart inside made
    them fully hart-free, and NO consumer use changed textually.
19. **Name collisions typecheck.** Fourteen instances of a pre-existing `b`/`p`
    (byte value, page address, PLIC state, buffer base) aliasing the new index —
    all `mword 64` or `bool`, all silent. This is the single most common way
    this refactor goes wrong.

### About orchestration

20. **The frontier tells you what to do NEXT, never how much is LEFT.** Driving
    from a `-k` build's failing set hid 21 files for five waves — a file deep in
    the graph never ENTERS the frontier until its dependencies are green. The
    `Link*` layer exposed them because it sits at the top and fails against
    everything. **Count against the full file list, or ask the top of the graph.**
21. **A shared `.vo` tree plus concurrent agents is fragile.** One `rm -f *.vo`
    during "cleanup" wiped 641 files under five running agents. Banning `make`
    was not enough; the deletion had to be banned by name.
22. **`make` without `-k` on a deliberately-broken tree stops at the first
    casualty** and silently leaves two-thirds of the buildable tree unbuilt.
23. **Agents hang in wait loops.** Three of seven lost their entire report that
    way despite completing the work. "Edit, compile once, report, never wait"
    had to become an explicit protocol line.
24. **Coordination dominates cost**, not porting: 150k–800k tokens per agent for
    files whose edits were minutes of work.
25. **A stale baseline manufactures a phantom regression.** `durable-notes`'
    "~65 s" for ProofPrintk was measured at 4800 lines; the file had since grown
    to 7903. That produced a confident "+56% regression" that did not exist, and
    the reasoning ("+2.5% of source cannot explain +56% of time") was *sound
    applied to a wrong premise* — the most dangerous kind of error, because it
    reads as rigour.

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
