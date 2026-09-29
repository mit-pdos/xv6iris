# `tools/integrity` -- the fork's proof-integrity gate

The xv6iris fork is developed by several agents merging into `main` under one human owner. This
directory is the gate on `main`: what may reach it, what needs the owner's explicit approval, and
how the approval is recorded. It replaces the unversioned `.git/hooks/integrity-check` grep of
2026-09-24 (kept as `*.before-integrity` by the installer). Written 2026-09-27; the policy
comparison in §3 is the reasoning behind every rule.

## 1. Use

```
git integrity                      # on a branch: what this branch adds vs main (working tree)
git integrity --quiet              # BLOCKING items and counts only
git integrity-audit --switch S [--opam-root R] [--from-log LOG]
                                   # run the three Print Assumptions audits on the BUILT tree,
                                   # compare with audit-baseline.txt, record the result for the
                                   # exact index tree
INTEGRITY_ALLOW=<fp> git merge --no-ff agent/x   # on main: approve exactly the BLOCKING list
                                                 # whose fingerprint the refusal printed
python3 tools/integrity/integrity.py check --base A --tree B [--upstream U]   # any two trees
python3 tools/integrity/tests/test_integrity.py                               # fixtures
tools/integrity/hooks/install.sh   # once per clone: hooks (all worktrees) + the two aliases
```

The report has two lists and a gate line:

- **BLOCKING** -- on `main` the commit is refused unless `INTEGRITY_ALLOW=<fingerprint>` names
  this exact list (the fingerprint is a hash of the blocking findings; an unrelated edit does not
  move it, a new finding does). The `commit-msg` hook then appends `Integrity-Allow: <fp>` and the
  approved findings to the message, so the history says what was waived and by whose hand.
- **REVIEW** -- attributed and listed for reading; nothing to approve.
- **audit gate** -- whether the exact tree being committed has a recorded audit identical to
  `audit-baseline.txt`. A proof-relevant change (`*.v` in the four proof dirs, any `_CoqProject`,
  `Makefile`, `opam/xv6rocq.export`) without one BLOCKS. The record is keyed by the index tree id,
  so it is valid for the merge commit that has that tree (`main` is an ancestor of every
  `agent/*` branch, so the merge result IS the branch tip's tree) and void the moment a proof file
  is staged afterwards.

Attribution: with an upstream commit known (`--upstream`, or the newest `upstream/main` commit
contained in the tree's commits, e.g. the merge head), a finding whose text is in upstream's
version of the file is **upstream's**; a deletion upstream also made is upstream's. Everything
else is **ours**. Only exact text matches count: a line our migration renamed reads as ours and
gets a second look, which is the right failure direction.

## 2. The rules

Owner decision (2026-09-27): **the same rule for everyone.** The fork's standard is at least
upstream's for every change, whoever made it; the `[upstream]` label on a BLOCKING line means
"upstream did this", and accepting upstream is what the approval token is for.

| Finding | rule |
|---|---|
| `Admitted`, `admit`, `give_up` in code | BLOCK |
| disabled checker (`Unset Guard/Positivity/Universe Checking`, `bypass_check`, `Admit Obligations`) | BLOCK |
| `Axiom`/`Parameter`/`Conjecture` outside a `Module Type`; `Variable`/`Hypothesis`/`Context` outside a `Section` | BLOCK |
| a `Module Type` field (`Parameter` inside `Module Type`) | REVIEW (the spec pattern; the audits see through it) |
| **STATEMENT**: a declaration kept under its name whose declaring sentence changed (statement, or a `Definition`'s body) | BLOCK |
| `Abort`; a top-level declaration GONE (upstream's `lemma_diff` regex, on comment-free text) | REVIEW |
| deleted `.v` file | REVIEW; BLOCK if some file still `Require`s it |
| `_CoqProject` flags or load paths | BLOCK |
| `_CoqProject` rows added/removed | REVIEW; BLOCK if a listed file is missing or an unlisted one is still present |
| `Makefile` lines in the audit/coqc/switch recipes (comments excluded) | BLOCK |
| `Makefile` other lines (pins, messages) | REVIEW |
| `iris/*Assumptions.v` (the audit files), `model-xv6iris/*.v` | BLOCK |
| `opam/xv6rocq.export`, anything under `tools/integrity/` | BLOCK |
| `.github/*` | REVIEW |
| proof-relevant change without a recorded baseline-identical audit of this tree | BLOCK |

The STATEMENT check compares, for every declaration present under the same name before and
after, the normalised text of its declaring sentence (keyword to the sentence's final `.`,
whitespace collapsed, comments and strings blanked). Moving a declaration or reflowing it is not a
change; adding a premise, weakening a conclusion or editing a `Definition` body is. Attribution:
`[upstream]` when upstream's version says exactly what ours now says; `[upstream~]` when upstream
also changed that statement but ours differs textually from upstream's (our migration renames
inside the statement, typically) -- read those; `[ours]` otherwise. It is the check that makes
"every statement kept" (the definition of a MECHANICAL fix) verifiable rather than asserted.

Keyword matches inside comments and strings are not findings; their count is printed
(`ignored: N`) so a sudden drop in that number is visible, per durable-notes' "when a checker's
verdict surprises you in the good direction, check the checker".

## 3. Upstream's policy, and where this differs

What upstream (mit-pdos/xv6iris) actually does, from its notes, CI and tools:

1. **`Print Assumptions` on the closed theorems is THE check** -- "the only one that sees through
   every functor and seal"; "a grep for `Admitted`/`Axiom` cannot stand in for it" (ci.yml, the
   audit step). CI runs `audit-only` and `audit-union-only` on every push and **reports the lists
   without diffing them** against an expected set -- "same contract as when they lived in the
   build log, so read them". The baseline lives as prose in `durable-notes.md` ("must show EXACTLY
   these thirteen. Diff **textually, not by count**"; "a MISSING assumed Link means someone proved
   it -- update this list in the same commit").
2. **`tools/lemma_diff.py`** reports, per changed file, declarations GONE, ADMITTED, and NEWAXIOM
   (`Axiom`/`Parameter`/`Hypothesis`, anywhere, `Module Type` fields included): "Every line is a
   thing to justify"; "read the report rather than treating it as a pass/fail oracle". It exists
   for interface sweeps -- "a file that compiles because something was quietly dropped".
3. **The trusted-base report** (`tools/tcb`) lists the definitions the adequacy STATEMENT unfolds
   to; also a report, "what to watch is the file count".
4. **`Parameter` inside `Module Type` is the spec pattern itself** (`design/spec-modules.md`),
   and an assumed callee -- `Module Type` + an `Axiom` in its `Link` file -- is a documented,
   accepted shape ("an assumed Link is sometimes what is keeping a top-level theorem honest"); the
   coverage report shows such functions as *assumed*, and any cone that uses one shows the axiom
   in its audit. (Today upstream's tree has no such `Axiom`, no disabled checker, and nothing
   assumed outside a `Section`/`Module Type`.)
5. **No hook, no approval token.** A single owner reads reports.

Where the fork's rules follow upstream:

- Nothing here replaces `Print Assumptions`; the gate *requires* it (the audit record), which is
  upstream's "definitive check" made a precondition rather than a habit.
- `Module Type` fields are not treated as leaks (upstream's pattern), and vanished declarations
  are reported (upstream's `lemma_diff`, reused through its `DECL` regex) -- our grep never did
  this, and our sed-driven migrations are exactly the interface sweeps that tool was written for.
- Every finding is still listed to be read; the BLOCK/REVIEW split only decides who must act.

Where the fork's rules are stricter, and why that is right for a fork with agents:

- **The audit is diffed against a checked-in baseline, not just read.** Upstream chose "report,
  not check" because the list legitimately changes when a Link is proved and the CI must not go
  red on progress. In the fork the readers of the report are agents, and "an agent read the list
  and found it fine" is the failure the owner's hook exists to prevent. The baseline file is
  itself a blocking trust file, so the legitimate change (a proved Link) costs exactly one owner
  approval, in the same commit, which is what upstream's prose asks for by hand.
- **An `Admitted`, an axiom outside a `Module Type`, a disabled checker, a changed statement or a
  trust-file change blocks `main` whoever made it** (the owner's rule "must never reach main";
  upstream's main tolerates an assumed Link and, being upstream, restates freely). The owner's
  ruling (2026-09-27): the fork's standard is at least upstream's for every change, and when the
  block comes from upstream, the owner accepts upstream -- through the token, so the acceptance
  is recorded. The cost is that every upstream sync needs the token (upstream restates statements
  in most commits); the report groups those by file, and the `[upstream]` label separates them
  from anything of ours at a glance.
- **Approval is tied to the report** (`INTEGRITY_ALLOW=<fp>`) and recorded in the commit.
  Upstream needs neither: one human, no merges from agents.

Where upstream's policy is still ahead:

- **The trusted-base file count** (tcb report) is not gated here; recording it beside the audit
  and flagging a change would close the other half of upstream's audit for the price of one
  more number. (The statement diff, listed here on 2026-09-27 as missing from both upstream's
  tools and this one, is now built: the STATEMENT rule above.)

## 4. Replay of this fork's two merges into main (2026-09-26/27)

Old grep (`.git/hooks/integrity-check`) vs `integrity.py check --base .. --tree .. --upstream ..`:

| Merge | old: flagged | new: BLOCKING | new: REVIEW |
|---|---|---|---|
| `5c4caf45f` (Iris-master upgrade + upstream 162 commits) | 6 "risky lines" (5 comments, 1 `Module Type` field), 8 trust files, 48 deleted `.v` -- all upstream's, checked by hand | ours: `model-xv6iris/rv64d.v`, `rv64d_types.v` (regenerated), `opam/xv6rocq.export` (new), NOT-AUDITED (historical tree, no record) | upstream's: 48 deletions (none still required), `_CoqProject` rows +65/-48 and the audit rows, 1 `Module Type` field, ~60 GONE declarations grouped by file; ours: 4 CI files; 73 comment matches ignored |
| `f8fd831a5` (upstream 90 commits) | 3 comment lines, `Makefile`, `iris/_CoqProject`, 1 deleted `.v` | none (the tree's audit was recorded from its log: 13/13/14 = baseline) -- **integrity: OK** | upstream's: `XV6_REV` bump, 1 deletion, `_CoqProject` +25/-1 rows, 30 GONE; 22 comment matches ignored. With the STATEMENT rule (added afterwards) this merge BLOCKS on upstream's restated declarations -- the owner's accept-upstream case; see the run recorded below the table |

Run of `f8fd831a5` with the STATEMENT rule (2026-09-27, 1.5 min): BLOCKING = 248 restated
declarations in 60 files, every one `[upstream]` or `[upstream~]` (12 of the latter: our
`ghost_var_frac`/`mono_nat_auth_own_frac`-style renames inside statements upstream also changed),
nothing `[ours]`; the audit gate satisfied. That is the accept-upstream case: one token approves
exactly that list.

Both merges were in fact approved with `INTEGRITY_ALLOW=1` after the same attribution was done by
hand; the new report is that hand work.

## 5. Limits

- Attribution is textual (exact line in upstream's file). A line renamed by our migration reads
  as ours; the human sees it twice rather than never.
- The scanner is line-based over comment-stripped text: a declaration keyword split across lines
  in an unusual way, or `Module Type` opened with a one-line `:=`, is handled; exotic
  vernacular (`Declare Module`, `Include` of an axiom-bearing module type into a `Module`) is not
  reasoned about -- the audit gate is what covers those.
- The audit record trusts `make -n` to say the tree is built (a `.vo` older than its `.v` shows
  up there; a `.vo` built from a different library copy does not -- see
  `docs/after-image-rebuild.md`).
- `check` on a 700-file merge takes ~2.5 min (two `git show` and a scan per changed file); a
  typical commit takes seconds.
