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
- **NEVER** `make clean-proofs` (nukes the shared `.vo` tree, breaks every
  sibling), and do not run a full `make`.
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

Know this one: **`is_cs_idx (mword_of_int 4)` is now `false`**, so
`callee_saved_insert_r` accepts a write to tp without complaint. That is sound
(`callee_saved` says nothing about tp) — the guard against writing tp lives in
`rd_ok` instead — but a tp write no longer trips a side condition, so do not
rely on one to catch it.

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
- `let`-bound values computed from the entry map (`ret_tgt`, a frame base) stay
  OUTSIDE the lambda; they are words, not hart-indexed resources.
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
