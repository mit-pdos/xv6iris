# Continuation folds — the worklist

**The lever** is optimization.md's "Fold block continuations into named
definitions" / "Seal a whole-function proof's continuation", and its worked
example is the ProofSysUnlink case study in that file. Read those first; this
file is only the tree-wide survey of WHERE ELSE the shape occurs, with the
measurements that size each one.

**The shape**: a block-decomposed whole-function walk hands a continuation
from block to block, and it is spelled INLINE in every statement that carries
it. Inline, it is re-embedded in the proof term of every proofmode step that
carries it, so it costs `|Δ| × steps` — and in these files it measures 35–90 %
of the statement it sits in. Naming it changes no proof script: the constant
stays TRANSPARENT and the `iApply ("H" $! …)` sites unify through it.

## Landed

| what | measured |
|---|---|
| `ProofSysUnlink`: `sys_unlink_closer` + `su_w1/w2/w3_seam` | 153.7 s → 133.1 s (−13.4 %), `.vo` −14.8 % |
| kexec: `KexecOkQ.kexec_closer`, 36 inline copies across 12 files | B3/C/A 166.6 s → 153.6 s (−7.8 %), `.vo` −7 to −10 % |

**The kexec cone is now DONE, and the reason is worth knowing**: its block
SEAMS were already folded (`ProofKexecSeam.kxc_at_12c`, used 7× in
ProofKexecB3), and the return closer was the only inline continuation left in
it. Nothing there is left to fold.

## Remaining, ranked

Per-lemma cost from isolated `coqc -time`; share is the largest inline
continuation as a fraction of that lemma's statement.

| file | build | the fold |
|---|---|---|
| **`ProofPrintk.v`** | 60 s | **14 lemmas, one shape.** `wp_printk_prologue` 66 %, `wp_printk_setup` 48 %, and a dozen `wp_printk_arm_*` at 35–43 %, all 7–19 rows. The arm continuations already come in three near-identical variant groups differing in one pure clause (`+2` vs `+3`), so ONE definition parameterised over that clause serves them all. The richest remaining target. |
| `ProofIput.v` | 79 s | `ip_free_entry` **47.9 %** of a 16 kB statement (7663 B, 50 rows), `ip_free_offlock` 31 %. **MEASURE BEFORE EDITING** — optimization.md records that naming `ip_free_locked`'s closer here cost **+13 s**. These are two DIFFERENT and larger continuations than the one that regressed, so it is not settled either way; it is the one file that has already resisted this lever. |
| `WpSconfCsr.v` | 34 s | `wp_csrr_sstatus_s_sconf` **89.5 %** and `wp_csrci_sstatus_x0_s_sconf` 78.3 % — the highest shares in the tree. A leaf/engine file, so per-proof step counts are lower than a walk's; expect less than the share suggests. |
| `ProofSysExec.v` | 51 s | `sx_setup` 63.2 %. But the file is ~30 proofs and this is one of them — high share, small prize. |
| `ProofInitlog.v` | 44 s | `il_hd` 47 %. |

## Not instances — do not go looking here

The most expensive files in the tree mostly do NOT have this shape, and that
is the useful negative: `ProofCreate` (159 s), `ProofNamex` (147 s),
`ProofNamexTr`, `ProofSysLink`, `ProofWritei`, `ProofUvmcopy`,
`ProofVirtioDiskInit`, `ProofSysOpen`, `ProofEndOp`, `ProofSyscall`,
`ProofDirlink`, `ProofReadi`, `ProofDirlookup` all score **zero** — no inline
continuation anywhere in their statements. Their cost is elsewhere
(`ProofCreate` already carries the `Strategy opaque` lines). This is not a
"sweep the expensive files" job.

## How to survey (and the trap in the survey)

Statement share is a good proxy for Δ share, but the detector must
**require ≥6 top-level `-∗` rows in the continuation's body**. Without that
check it counts a call to an ALREADY-NAMED definition as if it were inline —
which is exactly how `ProofKexecB3.kxc_ph_step` first read as "43.5 %
foldable" when its body is one `kxc_at_12c` application and there was nothing
to do. The payoff is that LEMMA's own cost × the share, never the file's cost
× the share.

Two traps that cost real time, both written up where they belong:
optimization.md's binder-list bomb (understate a factored `Definition`'s
`` `{!…} `` list and elaboration DIVERGES — 300 GB — rather than erroring;
overstate it and every call site fails cleanly), and durable-notes.md's
ambient-class-field version of the same bug. Keep `ulimit -v 25000000` on
`coqc`/`make` while doing this work.
