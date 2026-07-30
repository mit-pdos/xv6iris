# Porting guide: the explicit-CPUID sweep

The mechanical recipe for porting one file to the new interface. Read
[`explicit-cpuid.md`](explicit-cpuid.md) for WHY; this file is the HOW. The
worked examples are `iris/ProtoCpuid.v` (shapes, with commentary) and
`iris/WpSmodeIntr.v` (a real leaf/engine port).

**Read `../durable-notes.md` first** — its build and proofmode gotchas all still
apply, and two of them bite in this sweep specifically (Ltac literal names,
stale `.vo`).

## Build discipline (non-negotiable — other agents are working concurrently)

- `eval $(opam env --switch=/shared/xv6rocq)` first, always.
- `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden <file>.v`
- Compile **one file at a time**, only files you were assigned.
- **NEVER run `make` in any form.** Not `make`, not `make -f CoqMakefile`, not
  `make clean-proofs`, not "just to check". This has already happened once and
  it wiped the shared `.vo` tree (641 files down to 10) out from under five
  concurrently-running agents. `make` here can clean and rebuild from scratch,
  which costs everyone ~20 minutes and makes every other agent's compiles fail
  with errors that look like porting bugs but are not. The orchestrator runs
  the shared builds; you run `coqc` on your own files and nothing else.
- **NEVER delete build artifacts.** No `rm *.vo`, no `rm *.glob`, no "cleaning
  up" of any kind. The `.vo` tree is SHARED — deleting it from `iris/` is the
  same catastrophe as `make clean-proofs`, just reached by a different route,
  and that is exactly how it happened. You do not need to clean anything: a
  stale `.vo` is fixed by RECOMPILING the named file unchanged, never by
  deleting it. If you think you need to remove a file, you are wrong; report it
  instead.
- **If you see `Cannot find a physical path bound to logical path X`, or the
  `.vo` files have vanished: STOP AND WAIT.** Someone is rebuilding the shared
  tree. Do NOT edit your source in response — nothing is wrong with it. Sleep
  60s and retry the same `coqc`. Report it if it persists past a few minutes.
- Everything above `IntrDefs.v` is broken on this branch by design. Ignore
  breakage outside your assignment.
- **"Compiled library X makes inconsistent assumptions over library Y" is
  usually NOT your bug.** It means a sibling `.vo` predates an interface change.
  Recompile the named file *unchanged* and continue. Check `.v -nt .vo` before
  believing any impossible-looking arity/alignment error.

## What changed in the interface

| before | after |
|---|---|
| `sie_cap_gpr γ m av` | `sie_cap_gpr m av b` |
| `sie_cap γ m av` | `sie_cap m av b` |
| `sie_arm γ` (a disjunction) | `sie_arm b` (an `if b then … else …` INDEX) |
| `sconf γ`, `intr_count γ n eb`, `intr_inv γ h`, `intr_config γ`, `intr_handler_avail γ`, `intr_off_tok γ`, `intr_restore γ` | same, minus `γ` |
| `gpr_file m` inside the bundle | `gpr_file (tp_pin m)` |
| `rd <> csp_rs1` premise | `rd_ok rd` **in the same slot** |
| `m !!! Regidx rs` in a GENERIC leaf's value premise | `rget m rs` |
| `callee_saved` (with tp), `callee_saved_notp` | `callee_saved` (tp-free); the `_notp` twins are gone |

The SIE ghost is now canonical per hart (`IntrDefs.sie_gname := sie_name
cpu_id`), which is why `γ` disappeared. The one place an explicit ghost
survives is the per-trap tie `ProofKernelvec.v` mints — leave it alone.

**`instr` and `kernel_text` are now fully HART-FREE** — no `CID` implicit at
all. So a decode fact derived before a step is usable after it, at any hart,
with no re-derivation and no annotation. If you catch yourself wanting to
re-derive one at a new hart, stop: something else is wrong.

**The `callee_saved_notp` family is DELETED** — `callee_saved` *is* the tp-free
relation now. Nine names are gone: `callee_saved_notp`,
`callee_saved_weaken_notp`, `callee_saved_of_notp`, `callee_saved_notp_refl`,
`callee_saved_notp_trans{,_l,_r}`, `is_cs_idx_notp`, `callee_saved_notp_lookup`.
Porting rule: **every `callee_saved_notp` becomes a plain `callee_saved`, and
the bridge applications are deleted rather than replaced** — `_weaken_notp` /
`_of_notp` / `_trans_l` / `_trans_r` all collapse into `callee_saved_trans`.
Likewise every `⌜mf !!! Regidx (mword_of_int 4) = cid_word_of h⌝` premise in a
parking contract is deleted outright: `tp_pin` makes it true by construction.
~78 mentions across 23 files, concentrated in `ProofAcquiresleep.v` (18),
`ProofBread.v` (14), `ProofBwrite.v` / `ProofSleep.v` (8 each), `ProofYield.v`
(6), plus the `Spec*` / `Link*` parking contracts.

**ANY statement about the map's tp slot is now meaningless — delete it.**
`tp_pin` overwrites index 4, so nothing ever observes `m !!! Regidx
(mword_of_int 4)`. That covers three shapes, all of which go:
- `⌜mf !!! Regidx (mword_of_int 4) = cid_word_of h⌝` (parking contracts);
- a raw map-to-map equality `⌜Mf !!! Regidx (mword_of_int 4) = M !!! Regidx
  (mword_of_int 4)⌝` sitting among the callee-saved-style conjuncts (e.g.
  `SpecWakeupParts.v`) — true but vacuous, since the slot it preserves is junk;
- a tp conjunct inside a hand-rolled register-preservation predicate.
Deleting one is not weakening the contract: the real tp is `cid_word_of cpu_id`
by construction, which is strictly more than the old premise said. If deleting
one makes something else unprovable, STOP and report — that means a consumer
was reading the slot, which is the one case this rule would be wrong about.

Know this one: **`is_cs_idx (mword_of_int 4)` is now `false`**, so
`callee_saved_insert_r` accepts a write to tp without complaint. That is sound
(`callee_saved` says nothing about tp) — the guard against writing tp lives in
`rd_ok` instead — but a tp write no longer trips a side condition, so do not
rely on one to catch it.

`cid_word_of` / `cid_word` moved from `ProcGeom.v` to `HartTp.v` — every
register-file resource mentions the hart id now, so the definition had to sit
below the leaf layer. `ProcGeom` **re-exports** them, so the ~90 existing
references through it are unchanged. There must be exactly ONE such constant:
two convertible-but-distinct copies in scope together make every unification
against them fail confusingly.

**Add `HartTp WpNext` to your file's own `Require Import` line.** `Import` is
not transitive, so `tp_pin` / `rget` / `wp_next` are not in scope just because
`IntrDefs` imports them. This is the single most common first error.

## Statement edit

```coq
(* BEFORE *)                                  (* AFTER *)
Lemma L (γ : gname) … (m : regfile) (n : nat) :   Lemma L … (m : regfile) (n : nat) (b : bool) :
  rd <> csp_rs1 ->                                rd_ok rd ->
  … = m !!! Regidx rsa ->                         … = rget m rsa ->
  sie_cap_gpr γ m n -∗                            sie_cap_gpr m n b -∗
  ( sie_cap_gpr γ (<[Regidx rd := v]> m) n -∗     wp_next b (fun (CID : CpuId) =>
    pc_is (add_vec_int pc 4) -∗                     sie_cap_gpr (<[Regidx rd := v]> m) n b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗         pc_is (add_vec_int pc 4) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.              WP (Loop : expr riscv_lang) {{ Φ }}) -∗
                                                  WP (Loop : expr riscv_lang) {{ Φ }}.
```

Rules:

- `(b : bool)` goes **last** in the binder list (call sites are positional up to
  it).
- **Annotate NOTHING inside the `wp_next` lambda.** The rebound `CID` captures
  every resource automatically. Verified by `reflexivity` against the fully
  `(CID:=h)`-annotated form.
- **KEEP the section's `Context \`{CID : CpuId}`.** The lambda binder shadows it
  correctly (also verified). Only remove it from a file that must apply its OWN
  lemmas at a migrated hart — `Proof*.v` files split into block lemmas — and
  then make `CID` an *implicit* per-lemma binder `` `{CID : CpuId} ``, never
  explicit, so positional argument lists do not churn.
- **ANY VALUE THAT READS THE ENTRY MAP MUST BE `let`-BOUND OUTSIDE THE LAMBDA.
  This is a hard rule, and violating it presents as an infinite loop.**
  `rget` carries an implicit `{CID : CpuId}`, so a `rget m rd` written inside
  the lambda elaborates at the LAMBDA's hart — semantically the wrong hart
  (you would be reading the value on the hart you came from), and mechanically
  fatal: the engine's `wval` binder lives OUTSIDE the lambda, so `iApply` has
  to solve `?wval =?= add_vec (rget (CID:=bound) m rd) …` under a binder, and
  instead unfolds `rget`/`tp_pin`/`rf_upd`/`bool_decide` without terminating.
  Measured: >10 minutes of silence on one lemma. `coqc -time` pins it to the
  `unshelve iApply` immediately — see durable-notes, "a failing tactic looks
  like a hang".
  So: `let wval := <value> in` ahead of the premises, `intros wval.` at the top
  of the proof. **The lambda may contain only RESOURCES and binder-bound
  values — never a term that reads the entry map.** (`ret_tgt`, frame bases and
  store values are all in this class.)
- Concrete-register statements (`mm !!! Regidx (mword_of_int 10)`) do **not**
  need `rget` — a0/ra/sp are never tp. Only leaves whose register index is a
  VARIABLE do.
- M-mode / interrupts-off contracts take **no** `wp_next` wrapper: same hart in
  and out, stated exactly as today.

## Proof edit, in the order you hit it

1. Project the new premise once at the top:
   ```coq
   pose proof (rd_ok_sp rd Hrdok) as Hrdsp.   (* every old sp [congruence] still works *)
   pose proof (rd_ok_tp rd Hrdok) as Hrdtp.   (* feeds tp_refold *)
   ```
2. Every `gpr_file`-touching tactic takes `tp_pin m` where it took `m` —
   the map name is the only change (`gpr_file_lookup_acc (tp_pin m) …`,
   `gpr_file_insert_acc (tp_pin m) …`). The resulting value fact feeds the
   `rget m rsa` premise with **no bridge**: `rget` unfolds definitionally, so
   `exact (Hbexec …)` still closes it.
3. Re-fold your own write under the pin, one line, in every gpr-WRITING leaf:
   ```coq
   tp_refold Hrdtp "Hfile".     (* = iEval (rewrite (tp_pin_upd _ _ _ Hrdtp)) in "Hfile" *)
   ```
4. Feeding a step engine: the bundle owns `gpr_file (tp_pin m)` but `sie_cap` /
   `intr_frame` are keyed on `m !!! Regidx csp_rs1`. Use **`tp_pin_sp`**
   (`tp_pin m !!! Regidx csp_rs1 = m !!! Regidx csp_rs1`) plus
   `intr_frame_retarget` in both directions. Do not hand-roll the `Regidx`
   disequality.
5. Discharging a `wp_next` you must PRODUCE (Stage 1 — the engines still resume
   on the same hart):
   ```coq
   iApply ("Hcont" $! cpu_id with "[] …"). iPureIntro. done.
   ```
6. Call sites of a `rd_ok` premise: `ltac:(rdok)` where
   `ltac:(vm_compute; discriminate)` used to sit.

## Caller-supplied propositions must be hart-INDEPENDENT

A leaf that carries an opaque caller payload through the step (`P` in
`wp_gpr_write_s_sconf_cap`, `Ψ` in `wp_store_s_sconf_au`, `Ψ v` in
`wp_load_s_sconf_au`, the `Hrecap` capability transformer) keeps the type
`iProp Σ` — do NOT make it `CpuId -> iProp Σ`.

This is the same rule, for the same reason, as the C-slot in
`sched-hart-generic.md`: nothing in a crossing can turn `P` at the old hart
into `P` at the new one, so a hart-indexed payload would need a transport
bridge as an extra premise — and a `P` that admits one is exactly a
hart-independent `P`.

What follows, and it is a REAL constraint rather than a formality: at Stage 2 a
caller may not carry hart-indexed state (a `cpu_own`, anything mentioning
`sie_gname`, a per-hart lock fragment) across an interrupts-ENABLED step. Such
state either stays at `b = false`, or it has to ride the crossing frame — which
is the open design question in `explicit-cpuid.md`, to be settled against
`kerneltrap`'s real contract. Stage 1 does not exercise this (the hart never
actually changes), so it is easy to build consumers that violate it and only
find out at Stage 2. Don't.

## A function that READS tp mid-body must be stated at `b = false`

`cpuid()` / `mycpu()` are the case. The `c.mv a0,tp` executes in the MIDDLE of
the function, so with interrupts enabled a migration before it has the
instruction read the RESUMING hart's tp: the value returned is the id of
whichever hart executed that one instruction — neither the entry hart's nor the
exit hart's, and no `let` outside the continuation can name it. A contract that
says `a0 = cpuid_ret (rget m0 tp_idx)` is therefore FALSE at Stage 2, and
provable at Stage 1 only because no migration actually happens yet.

xv6 already knew: `mycpu()` carries the comment "Interrupts must be disabled."
This refactor turns that comment into a premise. Such contracts drop the `b`
binder entirely and are stated at `false` — and then need no `wp_next` wrapper
at all, since `wp_next_off` would collapse it, so they read exactly as they did
before the refactor.

**The test is what the function RETURNS, not what it reads.** Ask whether the
returned value is HART-dependent or THREAD-dependent:

- `cpuid()` returns the hart id — hart-dependent. A migration changes it, so
  the contract cannot name it unless interrupts are off. `b = false`.
- `myproc()` returns the current proc pointer — thread-dependent. That travels
  WITH the thread across a migration (it is still the same proc on the new
  hart), so the postcondition is fine at any `b`.

`myproc` is the worked counter-example, and it is worth internalising because
the naive reading gets it backwards: it *does* read a per-hart source mid-body
(`c->proc`), yet it stays `b`-GENERIC. It does its own `push_off()`/`pop_off()`,
so only its INTERIOR is interrupts-off — which is precisely where it gets to
call `mycpu()` at `false`. A function that brackets its own critical section is
b-generic on the outside no matter what it does inside.

## Two different indices: the resource's, and `wp_next`'s

For a function that merely threads the SIE state through, both are `b` and
there is nothing to think about. For a function that FLIPS it — push_off,
pop_off, acquire, release — they differ, and conflating them is a silent
falsehood of exactly the kind this refactor exists to remove.

- **The resource index** is what the SIE state IS at that point.
  `push_off : sie_cap_gpr m n b -∗ … sie_cap_gpr m' n false -∗ …`
- **`wp_next`'s index is whether interrupts were enabled at ANY point DURING
  the call** — not the state at either end.

So:

| function | entry | exit | `wp_next` index | why |
|---|---|---|---|---|
| push_off | `b` | `false` | **`b`** | at `b = true` it can trap on its first instruction, before it disables |
| pop_off / release | `false` | `eb` | **`eb`** | it re-enables at its LAST instruction, so it can trap there |
| threading function | `b` | `b` | `b` | — |

`wp_next false` on pop_off would claim the hart cannot move when it can. Note
this cannot be caught by compiling: at `eb = false` both spellings typecheck.

## Discharge gotchas (all found the hard way)

- **`$!` cannot skip an intervening wand or nested `∀`.** `iApply ("Hcont" $!
  cpu_id v with …)` mis-targets the wand's antecedent or fails to parse. Do the
  pure premise first: `iSpecialize ("Hcont" $! cpu_id with "[]");
  [iPureIntro; done|].` then a plain `iApply` for the rest.
- **A `wp_next` obligation under a `▷`:** put the later OUTSIDE
  (`▷ wp_next b (fun CID => …)`), so the existing `iNext` strips it from goal
  and hypothesis exactly as before. Inside, one `iApply` cannot peel a later
  and a wand at once and you need an `iSpecialize` first.
- **`iIntros (CID)` fails with "CID is already used"** against the section's
  `Context \`{CID : CpuId}` — a term-level `fun (CID : CpuId) =>` binder
  shadows fine, but `iIntros`/`intro` do NOT. In proofs always introduce a
  FRESH name (`CID1`, `CID2`, …); the names do not matter, resolution is
  positional.
- **A local proof variable named `b`** collides with the new `(b : bool)`
  lemma binder. Rename the local, never the binder. Same for a statement-level
  `b : bv 8` byte value (`SpecUart`'s became `bt`).
- **`rdok_split` poses without `as`**, so its projections get generated names.
  `congruence` finds the sp one fine, but `tp_refold` takes its hypothesis BY
  NAME — write `tp_refold (rd_ok_tp _ Hrdok) "Hfile"`, which is name-free and
  a line shorter anyway.
- **Not every leaf case-splits on `b`.** Leaves that never inspect the arm
  (WpPlic's, the WFI leaf) just carry it through opaquely — no `destruct b` at
  all. Only split when the old proof destructed the disjunction.

## The SIE arm

`iDestruct "Harm" as "[Hq0 | (Hq1 & …)]"` becomes a plain **`destruct b`**
(`true` branch first). **No `rewrite /sie_arm` is needed** — `sie_arm true` /
`sie_arm false` reduce by conversion, so the old `iDestruct` / `iFrame` /
`iExact` / `ghost_var_agree` lines work verbatim on the folded form. The old
`iLeft` / `iRight` are simply deleted; nothing replaces them.

Watch for a name collision: `iInv "…" as (b) …` where the invariant's ghost
value was called `b` now clashes with the index. Rename it (`bq`).

## Consumer side (straight-line proof stretches) — PROVISIONAL

Validated on `ProtoCpuid.v` only; will be hardened on a real `Proof*.v` before
the level-23 wave. Expect this section to change.

After each leaf application:

- **interrupts off (`b` literally `false`)** — `rewrite wp_next_off`, then
  `iIntros "…"` exactly as today. The hart collapses back, so decode facts and
  everything else derived earlier stay usable. This is the
  `push_off(); c = mycpu()` case.
- **`b` generic or true** — `iIntros (CID1 Hs1) "…"`. Everything afterwards is
  at `CID1`, resolved automatically with no annotation. Do **not** `destruct b`.
- At the end, discharge your own `wp_next` obligation at the hart you ended on
  with the composed equalities: `iApply ("Hcont" $! CIDn with "[%] …")` then
  **`wp_next_chain`**.

`instr` and `kernel_text` are hart-INDEPENDENT, so a decode fact derived before
a step is still usable after it. If you find yourself wanting to re-derive one
at a new hart, something is wrong — say so rather than working around it.

## Do not

- Do not make `wp_exec_step_intr`'s `iLöb` hart-generic, and do not touch
  `intr_handler_spec`'s continuation. That is Stage 2.
- Do not weaken, admit, axiomatize or delete a lemma to make it compile. If one
  is genuinely unprovable under the new interface, STOP and report which and
  why — that is a design signal, and the orchestrator wants it.
