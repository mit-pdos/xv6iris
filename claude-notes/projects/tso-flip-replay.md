# The M1 notation-flip REPLAY RUNBOOK (↦ₘ + ↦₈, stage 1)

This is the PROCESS, written to be re-run on top of a moved `main`.
The flip landed on `tso` as commits `3dfbcfcc` + `fba0ae63` (2026-08-26);
those diffs are the reference, but main moves quickly, so re-applying
the process below is expected to be cheaper than merge/rebase.  The
DESIGN rulings live in tso-port.md §0.8′; this file is only the how.

The one-sentence method: **flip the notations in one file, then let the
build enumerate the seams** — definitions are opaque names to their
consumers, so only fact-PASSING sites break, and no amount of grepping
predicts them better than `make -k` does.  It took ~30 rounds at
~5–15 min/round on the GCP box (`./gcp-rocq/run-on-gcp … make -f
CoqMakefile -j180 -k`, always from the repo root).  Keep
`ps -o pid,etime,rss -C rocqworker --sort=-etime` handy; anything past
~8 min gets a `coqc -time` single-file autopsy (find the sentence, not
the file).

## Preconditions (already on main by then, or re-applied first)

1. The lock surface at context shape (tso-port.md §0.6′) and the kmem
   recipe (§0.7′).
2. `TsoCtx.v` with the corrected Σ (CtxId, own_context, ctx_pointsto,
   CtxMorph, `<{ }>`); `TsoCtxShim.v`.
3. `tools/ctx_convert.py binders` already swept (CpuId-keyed binders).

## Pass 0 — the flip itself (hand edits, small)

- `TsoCtx.v`: the ctx WORD tower (`ctx_word_pointsto` +
  unfold/aligned_p/bytes/intro/frac_split/persist/agree +
  `ctx_morph_word`), then the notation block re-declaring all FOUR
  spellings of `↦ₘ` and of `↦₈` (incl. the `↦₈[ kt ] dq` bracket form
  with `dq custom dfrac at level 1` — copy the modifiers exactly or the
  ε-dq spellings keep parsing raw).  `↦ₓ`/`↦ᵣ` never flip;
  `↦₂`/`↦₄`/`↦ₛ`/`↦ₚ` are stage 2.
- Seal note: `ctx_word_pointsto` is NOT sealed at all (tower over the
  sealed byte; the tree's structural word proofs need it transparent).
- `TsoCtxShim.v`: `ctx_word_shim/of_mem/to_mem`, `ctx_buf_of/to_mem`,
  `ctx_eslot_of/to_mem` (the ∃-slot forms stack frames trade in).
- `<{ P }>` must already be the `const_pay` COMBINATOR, not a λ — ANY
  `CurCtx`-typed binder (even `_`, which Coq auto-names) is a TC
  candidate inside `P` and elaboration picks it site-dependently.  If
  main still has the λ form, change it in the same commit as the flip
  or the proc-lock cluster will not unify with itself.

## Pass 1 — import order

`Require Import TsoCtx` must be LAST (or at least after RiscvPtsto) in
every file that should flip.  Two audits:
- direct order per file;
- MID-FILE imports: some files `Require Import TsoCtx` between
  sections; hoist to the top ONLY for files that need the flip in their
  early sections (ProofFilewrite, VirtioDiskRwDefs were such) — kit
  files that were green with a late import (HartMemRun, RiscvExec,
  UmodeMem) must KEEP it late.

## Pass 2 — binders, three tools, in this order

1. `ctx_convert.py ambient --apply --files <error files>` — section
   binders for TsoCtx-importing files whose sections use the flipped
   vocabulary.  Deliberately NOT tree-wide (a dry run lists ~100 files;
   most are already fine through inline binders): apply to files the
   BUILD names.  The mode skips files that manage inline XI binders
   (stripping those breaks module-signature argument order — the
   ProofProcMapstacks lesson: signature has `{GEN}{CID}{XI}` inline
   order, a section binder reorders).
2. `ctx_convert.py inline --apply --files <error files>` — per-decl
   binders in inline-managed files, gated on the FLIPPED vocabulary AND
   enclosing-section coverage (a combined
   `Context `{GEN}`{CID}`{XI}` line counts as covered).
3. Backward-walk one-offs: for "Cannot infer CurCtx" / "?XI : CurCtx"
   existential errors the modes missed, walk from the error line to the
   enclosing decl and add `` `{XI : CurCtx}`` after the name.  In files
   WITHOUT the TsoCtx import (boot tier), spell it QUALIFIED
   (`` `{XI : TsoCtx.CurCtx}`` after a plain `Require TsoCtxShim.`) so
   the file's own notations stay raw — an unqualified name in a
   no-import file silently GENERALIZES `CurCtx : Type`.

The vocabulary (`FLIPPED` in the tool) is a HARVEST: it cannot see
ctx-ness that arrives through a converted definition name, so every
`parameter XI of <name>` existential error adds `<name>` to the list.

## Pass 3 — the error-driven loop, with the fix table

Build; classify each error; fix; repeat.  The classes, in observed
frequency order:

| symptom | fix |
|---|---|
| `Cannot infer CurCtx` / `?XI` existentials at a decl | binder (pass 2.3) |
| `XI is already used` | decl inside a covered section → strip the inline binder; NEVER strip on module-field lemmas — remove the SECTION binder instead |
| `iFrame: cannot frame (…word_pointsto…)` (raw vs ctx) | if direction known: `TsoCtxShim.ctx_word_of/to_mem`, `ctx_eslot_*`, `ctx_buf_*`; if unknown: replace `iFrame "A B C"` with `iSplitL "A"; [iExact "A"|]…` chains — `iExact` unifies THROUGH the seal in either direction |
| `word_pointsto_<law>` applied to a ctx fact | rename to `ctx_word_pointsto_<law>` (arity gains a leading ξ — one more `_`) |
| `rewrite /word_pointsto` no-op then a split fails | `rewrite /ctx_word_pointsto` |
| a file full of explicit `word_pointsto (KTR := kt)` spellings mixing with flipped facts | sed the whole file to `ctx_word_pointsto (KTR := kt) cur_ctx` (ProofKexecTail/Parts, SpecKexecB2 pattern) |
| ctx bytes feeding a `↦₂`/`↦₄`/`↦ₛ` target (or back) | per-byte/word shim conversion + a "stage 2" comment — each is a stage-2 worklist marker |
| `Timeless`/`Persistent` `apply _` fails on a mixed bundle | decompose (`repeat apply bi.sep_timeless`) with named instance fallbacks (`ctx_pointsto_timeless`, `ctx_word_pointsto_timeless`) |
| `iSpecialize/iApply: cannot instantiate` across a module functor | pin `(GEN := GEN) (CID := CID) (XI := XI)` at the iApply |
| big-op payload defs shared across sections | make their `Typeclasses Opaque` seal `Global` (kmem lesson: iFrame crawls 4088 conjuncts otherwise) |
| a proof needs a fact at a context it doesn't hold | STOP and check whether the crossing is real (below) |

## The three probes (use before guessing)

- **What does a notation mean here?** Scratch file with
  `Set Printing All. Check (fun a v => (a ↦ₘ v)%I).`
- **Is a slow file degenerate?** `coqc -time`, sort by seconds; the
  hanging sentence is the one after the last printed line (BYTE
  offsets).
- **Is a context crossing provable at SC?** In a scratch section with
  `Local Transparent ctx_pointsto own_context hart_view_lb ctx_dom
  ctx_parked.`, try `Lemma _ : P (XI := ξ) ⊣⊢ P (XI := ξ').
  Proof. reflexivity. Qed.`  FAST failure ⇒ genuinely ξ-dependent
  (some identity ghost inside) ⇒ the crossing needs real M2 transport,
  not a tactic; success ⇒ shim/iExact will work.  This is how the park
  protocol's unprovability was established — the 35-minute `iExact`
  was unification exhausting a FALSE goal, not a slow true one.

## Landmines (each cost an hour the first time)

- The seal is unification-permeable: silent crossings compile (fine —
  cutover finds them) and var-vs-var crossings CRAWL.  Watch etimes.
- λ/∀ binders of type `CurCtx` capture TC resolution inside their body
  — statements that ∀-quantify a context (park/resume) must pin every
  non-crossing implicit explicitly, or use `const_pay`.
- A lemma whose PROOF uses `cur_ctx` captures the section's XI into its
  ARGUMENTS even when the statement is raw — instantiate ∀-context
  facts at a concrete `MkCtxId inhabitant inhabitant` in such proofs
  (kernel_data_string lesson).
- Boot files never get ambient binders (the eight-hart adequacy trap);
  they talk through qualified `TsoCtxShim.…` names.
- sed replacement checks: `ctx_word_pointsto` CONTAINS
  `word_pointsto`; parenthesized args break naive regex reversal.

## Order of the design edits (tso-port.md §0.8′ has the WHY)

kernel_data ∀-form → lock_name/sl_name raw + lk_cpu_res ∃ +
lk_cpu_cell_acc → const_pay wrapper → kmem minimal-diff redo →
StackOwn flip (+ stack_own_reindex, BootBridge mint) → cpu_ctx_free ∃
(+ ctx_cells_reindex) → wordw/bb/kxc interior towers ctx.

Commit at every green-ish plateau; narrative messages; the checkpoint
section is updated in the same commit as the code it describes.
