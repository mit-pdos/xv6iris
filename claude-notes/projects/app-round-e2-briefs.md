# Round E2 — lane briefs and the build script (checkpointed 2026-09-05 so another agent can resume)

Companion to app-round-e2.md (the proposal and rulings).  Each brief below was written for a subagent lane; paths under /tmp/… in them refer to the ORIGINAL session's scratchpad — substitute this file and a copy of the script below.  The rules every lane follows: build only on the GCP VM through the script (never make by hand, never locally), never change git state inside a lane, no subagents inside a lane, absolute paths, batch edits (FsAbsDefs' cone is ~500 files, ~10 min), no Admitted/Axiom, and the statements of SystemAdequacy.xv6_fs_adequacy_xv6Σ and App.xv6_app_adequacy_triv_xv6Σ byte-identical.  After a lane is green: run `make audit-only` on the VM (13 axioms is the baseline), commit, fetch/rebase, rebuild if iris files came in, push.

## The build script (vmbuild.sh <logname> [new iris files relative to iris/])

```bash
#!/bin/bash
# vmbuild.sh <logname> [extra files relative to iris/ ...]
# Syncs /shared/xv6iris-3 to the VM, deletes the remote artifacts of every
# locally-modified/untracked iris/*.v (and the extras), regenerates
# CoqMakefile, builds iris with -k, writes a sentinel and prints the errors.
set -u
LOG=${1:-build}; shift || true
cd /shared/xv6iris-3
FILES=$( (git diff --name-only; git diff --cached --name-only; git ls-files --others --exclude-standard) \
         | grep '^iris/.*\.v$' | sed 's|^iris/||' | sort -u | tr '\n' ' ')
FILES="$FILES $*"
/shared/xv6iris-3/gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- bash -c "
  cd /mnt/rocq/trees/_shared_xv6iris-3/iris || exit 9
  for f in $FILES; do rm -f \${f%.v}.vo \${f%.v}.vos \${f%.v}.vok \${f%.v}.glob; done
  coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
  (make -f CoqMakefile -j180 -k > /tmp/$LOG.log 2>&1; echo EXIT=\$? >> /tmp/$LOG.log)
  echo COMPILED=\$(grep -c 'ROCQ compile\|COQC' /tmp/$LOG.log)
  grep -n 'Error' /tmp/$LOG.log | head -40
  tail -1 /tmp/$LOG.log"
```

## roundE2V2-brief.md

## Lane E2-V2: the view EXCLUDES nlink = 0 inodes

Ruling (owner, 2026-09-05, reversing Q-b; recorded in claude-notes/projects/app-round-e2.md under
"Q-d, THE OPEN DESIGN QUESTION"): an inode is in the user-visible view iff it is allocated AND
`fn_nlink n ≠ 0`.  Consequences the ruling accepts: iput's free and ialloc's claim are VIEW-
PRESERVING (the row is absent before and after); reads through an open fd of an UNLINKED file
lose their view spec (follow-up on the fd row, not this lane); a removed cwd's relative lookups
are unspecified.  Read that section, then FsAbsDefs.v's header (lane E2-V's note) and
durable-notes.md ("Build", proofmode gotchas).  Tree: HEAD 1f06aa4af green.  Build ONLY via
`bash /tmp/claude-0/-shared-xv6iris-3/f5f45108-e792-447c-8e66-7d345052a2ba/scratchpad/vmbuild.sh rE2V2`
(foreground, timeout 600000; poll /tmp/rE2V2.log via run-on-gcp on overrun; never stop to wait).
No make by hand, no local builds, no git state changes, no subagents, absolute paths, nothing
under claude-notes/.  ~500 files per build: batch edits.

### The change (FsAbsDefs.v)

    Definition abs_of (n : fs_node) : option anode :=
      if decide (fn_type n = 0 \/ fn_nlink n = 0) then None else Some (abs_row n).

`abs_of_free` becomes `abs_of_none : fn_type n = 0 \/ fn_nlink n = 0 <-> abs_of n = None`;
`abs_of_typed` needs both `fn_type n ≠ 0` and `fn_nlink n ≠ 0` (name it `abs_of_live`);
`abs_of_Some` yields both; `abs_of_orphan` is now `abs_of n = Some a -> an_nlink a ≠ 0` (restate);
`abs_of_bare_dir` (a bare dir at nlink 0) is now `abs_of n = None` — restate or delete with its
users.  Update the header note (E2-V's paragraph) to say the filter is type AND nlink.  Keep every
other statement as it is; the row-reading sites gain the `fn_nlink ≠ 0` fact they hold (an
`inode_ok`/entry-reachability fact: a node reached by a directory entry has nlink ≥ 1; the read/
write fires' fd-held inodes do NOT necessarily — see below).

### The sites that read an nlink-0 row (the ruling's cost — handle honestly, do not fake)

- `SpecSysReadAU.v` ~725 `⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝` on the fd's inode, and the
  read/write fires (`arf_read_fire`, `wrf_awrite_fire`, FsAbsWriteFire's chain): the fd's inode may
  be at nlink 0 (unlinked while open).  Make the view clause CONDITIONAL on the count: the fire
  yields `⌜fn_nlink n ≠ 0 -> av !! i = Some (abs_row n)⌝` (or a `match`/disjunction the contract
  already has room for), and the write delta on an nlink-0 inode is view-preserving (`abs_view` is
  unchanged: use `abs_view_insert_None`/`_same`).  Report exactly which contracts changed shape.
- Unlink's target fire (`uf_utgt_fire`, FsAbsUnlinkFire) when the count hits 0: the row is DELETED
  from the view — `delta_unl_tgt` must become "nlink−1, and delete when it reaches 0" (FsAbsDelta.v,
  with `delta_unlink_split` and its lookup lemmas re-proved; the AU unlink proofs that use them follow).
- Create's armed child (`cre_pre`'s `av !! i = Some (MkAnode c 1)`) is at nlink 1: unchanged.
  ProofIlock's claim (#2) and EscrowDeposit's free (#1) stay on `_auto` in this lane (E2-Z converts
  them to `_same` — DO NOT do it here; note only that `abs_of` is `None` on both sides at those sites).
- Pins (FsInitPin/FsShPin/SpecKexecPin/FdRowMint) read image nodes at nlink ≥ 1: add the fact.

### Gate

Green; both audited statements byte-identical; no Admitted/Axiom.  Report: `abs_of` and every
restated lemma verbatim, every contract whose SHAPE changed (the conditional view clause), the
new `delta_unl_tgt`, files touched with one line each, deviations.  Do not commit.

## roundE2D-brief.md

## Lane E2-D: the delta vocabulary for create's legs, link and the free (PURE; FsAbsDelta.v)

Rulings: claude-notes/projects/app-round-e2.md (status block, and "Q-d": the view EXCLUDES nlink-0
rows — lane E2-V2 landed that; read FsAbsDefs.v at HEAD).  Consequences for the vocabulary: there is
NO `delta_claim` (ialloc's claim is view-preserving) and NO `delta_free` (identity); the node APPEARS
at the arm and DISAPPEARS at the unarm.  Read that
file's §2(b), §3, §4, §5, §6 and fs-syscall-specs.md §4 (the δ vocabulary) and §7.  E2-V (view =
allocated rows, `abs_of : fs_node -> option anode`, `abs_view := omap abs_of`) has LANDED: read
FsAbsDefs.v at HEAD for the exact spelling and FsAbsDelta.v for the landed deltas
(`delta_create`, `acre_bump`, `delta_write`, `delta_trunc`, `unl_dec`, `delta_unl_ent`,
`delta_unl_tgt`, `delta_unlink`, `fs_delta`) and SpecSysUnlinkAU.v:73-108 for the two-instant
split's shape (`delta_unlink_split`).

Build ONLY via `bash …/scratchpad/vmbuild.sh rE2D` (same rules as every lane: foreground, timeout
600000, poll on overrun; no make by hand; no git state changes; no subagents; absolute paths).

### Mint (pure functions on `aview`, with the doc's names in comments)

    delta_arm i c           : av ↦ <[i := MkAnode c 1]> av            (nlink 0 → 1: the row APPEARS, content c — for ADev the major/minor; precondition i ∉ dom av)
    delta_unarm i           : av ↦ delete i av                         (the failure arm's undo, Q-h: the row DISAPPEARS)
    delta_dots i d          : av ↦ alter (ADir ∅ ↦ ADir {"." := i, ".." := d}) i av   (mkdir's dot writes, nlink unchanged)
    delta_ent d nm i        : av ↦ alter (ents += nm ↦ i, nlink += acre_bump (child)) d av   (the parent leg; = today's `delta_create`'s parent row)
    delta_link_tgt t        : nlink+1 at t
    delta_link_ent d nm t   : ents += nm ↦ t at d
    delta_link_untgt t      : nlink−1 at t                             (link's failure arm)
    delta_link d nm t       := delta_link_ent d nm t ∘ delta_link_tgt t
    delta_create_split      : cre_pre-style premises -> delta_create d nm i c av = delta_ent d nm i (delta_arm i c av)   (state the exact premises the proof needs; mirror `delta_unlink_split`)
    delta_link_split        : link_pre premises (t is a file/dev in av; ents !! nm = None at d) -> delta_link d nm t av = … (the composite)
    fs_delta                : gains the new kinds (keep it the disjunction of ALL write-kind deltas; every existing user of `fs_delta` must still compile)

Provide the row-reading lemmas each future fire will need (mold: the landed `delta_create_parent`,
`delta_unl_*_lookup` family): `delta_X_lookup_same` (other keys unchanged), `delta_X_lookup_at`
(the moved key), and for `delta_arm` the `∉ dom av` precondition's consequence.  Keep every
existing lemma's statement.  No consumer outside FsAbsDelta.v changes in this lane.

### Gate

Green; both audited statements byte-identical; report the definitions verbatim and the lemma
list.  Do not commit.
