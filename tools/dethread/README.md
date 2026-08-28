# `tools/dethread` — the rank-1c de-threading sweep, kept because it is re-runnable

This is the machinery that took `dev`, `nib`, `inodestart` and the log's names
off the file-system contract surface and replaced them with the ambient
`icfg_dev` / `icfg_nib` / `icfg_ist` / `icfg_log` (see the R1c "as landed"
paragraph in `claude-notes/projects/durable-disk.md`).  It is tracked not as a
record but because it is DETERMINISTIC and therefore still useful: whenever a
lane that restructures the same proofs lands ahead of a de-threading branch —
the continuation-fold lane does this constantly, lifting a block's tail into a
named `*_exit` definition whose binder list spells all four names out — the
rebase conflict is always "the fold vs. the inlined continuation", and the
resolution is always *take the fold and re-run the sweep on it* rather than
merge by hand.  `dethread.py` is the shared Rocq-source parser (comment
stripping, declaration headers including a `Lemma X : forall …`'s binders,
bracket-aware application argument lists).  `rewrite.py` is phase one: it
computes, per declaration, which EXPLICIT argument positions carry one of the
four names, then drops those binders, renames the uses inside each declaration
to the class field, and deletes the corresponding positional argument at every
application in the tree — `apply` writes, anything else is a dry run reporting
what it could not prove safe.  `cleanup.py` removes the blank lines that leaves
inside a binder list.  `premise.py` + `phase2.py` are phase two: once both sides
of a tie are ambient, `⌜g = icfg_log⌝` has become `⌜icfg_log = icfg_log⌝`, so
they find those premises in each declaration's `->` chain, delete them, delete
the name the proof's `intros` gave each one, and drop the argument every caller
fed it.  `fixuse.py` finishes the job: a hypothesis of type `icfg_X = icfg_X`
is one Rocq REFUSES to rewrite by, so every `rewrite`/`iEval (rewrite …)` that
consumed one has to go with it.  `cut.txt` is the 91-file cut — the contract
surface above the WAL; everything outside it keeps its parameters on purpose
(the WAL and everything below `FsCfg`, the per-call `dev` of the bio layer and
`SpecStati`, the boot side's era numbers, and the pure lemmas with no `icfg` in
scope, which is R1b's memory bomb — `tools/dethread_check.py` is the guard for
that one).

**Re-running the sweep on one file** (the fold-lane rebase recipe):

    BASE=<the commit you are rebasing ONTO> tools/dethread/redo-files.sh ProofIput.v

It builds a scratch copy of `BASE`'s tree, swaps in `origin/main`'s version of
the named files, runs all four passes over it, and copies just those files
back.  Two edits were made BY HAND during R1c and the passes cannot know about
them, so re-check the output for both: `SpecKexec.fs_fabric` lost its last
conjunct (so a destruct pattern must lose its `%Hclogf` slot and
`fs_fabric_mk` its `[%]` one), and `KexecOkQ.kexec_closer` lost its
`inodestart` argument.  Then compile the file standalone before the tree build.
