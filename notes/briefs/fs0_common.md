# fs.c port, wave 0 — common brief

You are porting part of the Rocq (Coq/Iris) verification of xv6's fs.c to the Lean 4 port at
/shared/lean-xv6 (branch lean-v2). The standing instruction from the user: **"this has a ton of
subtle details; pay careful attention to the Rocq proofs or you'll end up reinventing the
wheel."** Port Rocq LITERALLY: same definitions, same lemma names (camelCased per the port's
convention: Rocq `hdr_dec` → Lean `hdrDec`, `log_opS` → `logOpS`, `di_addrs` → `diAddrs`),
same lemma statements, same proof structure. Do not redesign. If a Rocq definition looks
odd, it is odd for a reason recorded in its header comment — copy the reason into the Lean
docstring.

## Where things are
- Rocq sources: /shared/xv6rocq/iris/<File>.v (ignore /shared/xv6rocq/.claude/worktrees/*).
- The survey note: /shared/lean-xv6/notes/fs-rocq-summary.md (1.5 MB; grep it by section
  header — `grep -n '^## ' notes/fs-rocq-summary.md`). §2.4 on-disk encodings, §2.5 bitmap,
  §2.6 inode shape, §2.12 directory view, §2.13 path algebra, §2.20 porting order, §5 the
  mapping to the Lean port (what already exists), §6 pitfalls.
- Lean port: Xv6/*.lean (kernel), MachCSL/*.lean (framework). Existing vocabulary you must
  REUSE rather than duplicate: `BSIZE` (Xv6/DiskDefs.lean), `LOGBLOCKS`/`MAXOPBLOCKS`
  (Xv6/LogDefs.lean), block contents are `List (BitVec 8)` of length BSIZE, words are
  `BitVec 32`/`BitVec 64`; the Lean counterparts of Rocq's byte/word helpers live in
  MachCSL (grep `bytesToWord`, `wordToBytes`, `byteBuf`, `ctxBytes`, `histBytes`,
  `leBytes`, `BitVec.ofNat` uses in Xv6/LogDefs.lean and Xv6/DiskTier.lean). Grep before
  defining anything: `grep -rn 'def <name>' Xv6 MachCSL`.
- Style templates: Xv6/LogDefs.lean (a literal port of Rocq LogDefs.v — pure algebra plus
  lemmas), Xv6/LogLedger.lean (map folds via `LawfulFiniteMap` toList permutations),
  Xv6/VirtioQueue.lean (BitVec/wrap arithmetic lemmas).

## Rules
- One Lean file per Rocq file, same name: Rocq `DinodeEnc.v` → `Xv6/DinodeEnc.lean`.
  Header docstring: what the file is, the Rocq file it ports, and every deviation.
- Every Rocq lemma is ported and PROVED. **Never commit or leave `sorry`.** If a lemma is
  genuinely unportable, stop and report it rather than weakening it.
- Keep every tactic block short (the project rule: no proof over a few minutes of
  elaboration; split lemmas). `omega`, `simp`, `decide` and `bv_decide` are fine; watch
  `decide` on large BitVec literals.
- Build ONLY your own modules: `timeout 1800 lake build Xv6.<Module>` for each file you
  create. NEVER run a bare `lake build` (other agents are building in this tree; a bare
  root build races with them). NEVER build modules you did not write.
- Do NOT edit Xv6.lean (the root import list), any existing file, or git state: no `git add`,
  no `git commit`. The coordinator wires imports and commits. If a port truly needs an
  existing file changed, report the exact change instead of making it.
- Do not create files outside Xv6/ (scratch goes in your own subdirectory of
  <your scratch dir>/).
- Layering: `tools/check_layering.sh` must stay green; definitional files import only
  definitional files (no `Code*`/`Proof*`/`Link*`).

## Lean/iris-lean gotchas (from earlier waves)
- `BitVec.ofNat_add` splits sums; state lemmas in the shape the normaliser produces.
- `iframe` is syntactic: `(BitVec.ofNat 32 n).toNat` normalises inconsistently; prefer
  explicit `Nat` parameters with a `subst`.
- Map folds: use `LawfulFiniteMap` toList permutation lemmas (Xv6/LogLedger.lean).
- `decide` on `∀ i < 1024` is slow; use `List.range` + `simp`/`decide` on small ranges or
  `omega`-shaped statements.

## Report
When done: the list of files with line counts, the build command output's last line for each,
every deviation from Rocq (with the reason), and anything you found already present in Lean
that you reused instead of porting.
