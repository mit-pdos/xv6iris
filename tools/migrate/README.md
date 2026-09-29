# `tools/migrate` -- bringing Iris-4.4-era Rocq sources to the current toolchain

The toolchain moved on 2026-09-26 (`opam/README.md`): coq-iris 4.4.0 → rocq-iris master
(`8e490959`), coq-stdpp 1.12.0 → rocq-stdpp master (`d510b616`), coq-sail-stdpp 0.20.1 → 0.20.3.
Every proof in the tree was reconciled with a deterministic script plus a short list of hand
fixes; the script is here so that **a branch written against the old toolchain can be brought
across the same way**, instead of by hand.

## If you have an in-flight branch from before the toolchain change

```sh
git fetch origin                          # main now has the new toolchain
git checkout my-branch
git merge --no-commit --no-ff origin/main # conflicts in every proof both sides touched: expected
tools/migrate/merge_upstream.py origin/main   # re-merges each conflicted iris/*.v as
                                              # merge3(ours-migrated, base-migrated, main)
git status                                # what is left is a real conflict; resolve, commit
```

`merge_upstream.py` was written for the opposite direction (merging new upstream work into the
migrated tree); its rule is symmetric: for each `iris/*.v` changed on the side that is NOT migrated
it computes `merge3(migrated(theirs), migrated(base), ours)` so the renames never conflict. Read
its docstring before the first use and check the printed CONFLICT list.

For a file (not a branch) that has never seen the new toolchain:

```sh
tools/migrate/migrate.sh iris/MyNew.v     # in place; once
```

## What the script does (so you can judge what it did)

- `migrate-master.sed` (run with `sed -E`): the upstream Iris/stdpp rename tables (Iris 4.5 +
  master, stdpp 1.13 + master); `ghost_var`/`ghost_map_auth`/`mono_nat_auth_own` at a fraction →
  their `_frac` notations, and the `@`-explicit / named-instance forms of those to the notations'
  unfolding with `DfracOwn` (the notations cannot take an instance); `list_*` lemma requalification;
  skips `Require` lines.
- `unwrap.pl` (`perl -0pi`): coq-sail 0.20.3 removed the identity wrappers `get_word`/`to_word`/
  `with_word`; their applications, `unfold`s and rewrite-list entries are removed.
- `migrate_imports.py`: `weakestpre` no longer re-exports `language` (explicit import after the
  first `program_logic` import); `stdpp.list_*` submodules requalified; the `language` re-import
  after `adequacy` (stdpp's `nsteps` shadowing).

What it does NOT do, and what you will fix by hand (the patterns seen on the whole tree, in
`claude-notes/durable-notes.md` "Build" and the fork's notes): section variables Rocq now counts
as used → `clear V.` at the proof start (never add them to `Proof using`: that changes the closed
statement); proof-mode instance resolution needing an explicit `(KTR := …)`/`(CID := …)` -- Iris master
resolves a lemma's unconstrained instance evar EAGERLY to the newest instance in context, where
Iris 4.4 left it for the `with "H"` unification to fill, so `iDestruct (lem … with "H")` fails with
`iSpecialize: cannot instantiate` on two terms that print identically; name the OUTER instance,
the one `H` is stated at (`Set Printing Implicit. Show.` tells which), not the one an `iIntros (CID1 …)`
just introduced (2026-09-29: `kexec_closer_after_next (CID0 := CID0)`, `kfork_cont_ev (CIDa := CID0)`); `iFrame`
of a persistent hypothesis now frames every occurrence and fails where it made no progress;
dfrac validity (`rewrite dfrac_op_own dfrac_valid_own in H`); stdpp's `set_to_map` takes the value
function. None of these change a statement.

## Checking that a migration changed no statement

Compare, for every declaration present under the same name before and after, the text of its
declaring sentence (keyword to the sentence's final `.`, whitespace collapsed, comments and strings
blanked). On 2026-09-29 the whole tree's diff against the migrated upstream tree came down to three
declarations plus the regenerated model; keep it so.
